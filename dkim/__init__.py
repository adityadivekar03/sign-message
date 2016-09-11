# This software is provided 'as-is', without any express or implied
# warranty.  In no event will the author be held liable for any damages
# arising from the use of this software.
#
# Permission is granted to anyone to use this software for any purpose,
# including commercial applications, and to alter it and redistribute it
# freely, subject to the following restrictions:
#
# 1. The origin of this software must not be misrepresented; you must not
#    claim that you wrote the original software. If you use this software
#    in a product, an acknowledgment in the product documentation would be
#    appreciated but is not required.
# 2. Altered source versions must be plainly marked as such, and must not be
#    misrepresented as being the original software.
# 3. This notice may not be removed or altered from any source distribution.
#
# Copyright (c) 2008 Greg Hewgill http://hewgill.com
#
# This has been modified from the original software.
# Copyright (c) 2011 William Grant <me@williamgrant.id.au>

import base64
import hashlib
import logging
import re
import time

from dkim.types import Signature

from dkim.canonicalization import (
    CanonicalizationPolicy,
    InvalidCanonicalizationPolicyError,
    )
from dkim.crypto import (
    DigestTooLargeError,
    HASH_ALGORITHMS,
    parse_pem_private_key,
    parse_public_key,
    RSASSA_PKCS1_v1_5_sign,
    RSASSA_PKCS1_v1_5_verify,
    UnparsableKeyError,
    )
try:
  from dkim.dnsplug import get_txt
except:
  def get_txt(s):
    raise RuntimeError("DKIM.verify requires DNS or dnspython module")
from dkim.util import (
    get_default_logger,
    InvalidTagValueList,
    parse_tag_value,
    )

__all__ = [
    "DKIMException",
    "InternalError",
    "KeyFormatError",
    "MessageFormatError",
    "ParameterError",
    "InvalidSignatureTypeError",
    "Relaxed",
    "Simple",
    "DKIM",
    "sign",
    "verify",
]

Relaxed = b'relaxed'    # for clients passing dkim.Relaxed
Simple = b'simple'      # for clients passing dkim.Simple

def bitsize(x):
    """Return size of long in bits."""
    return len(bin(x)) - 2

class DKIMException(Exception):
    """Base class for DKIM errors."""
    pass

class InternalError(DKIMException):
    """Internal error in dkim module. Should never happen."""
    pass

class KeyFormatError(DKIMException):
    """Key format error while parsing an RSA public or private key."""
    pass

class MessageFormatError(DKIMException):
    """RFC822 message format error."""
    pass

class ParameterError(DKIMException):
    """Input parameter error."""
    pass

class InvalidSignatureTypeError(DKIMException):
    """Incorrect signature type error."""
    pass

class ValidationError(DKIMException):
    """Validation error."""
    pass

def select_headers(headers, include_headers):
    """Select message header fields to be signed/verified.

    >>> h = [('from','biz'),('foo','bar'),('from','baz'),('subject','boring')]
    >>> i = ['from','subject','to','from']
    >>> select_headers(h,i)
    [('from', 'baz'), ('subject', 'boring'), ('from', 'biz')]
    >>> h = [('From','biz'),('Foo','bar'),('Subject','Boring')]
    >>> i = ['from','subject','to','from']
    >>> select_headers(h,i)
    [('From', 'biz'), ('Subject', 'Boring')]
    """
    sign_headers = []
    lastindex = {}
    for h in include_headers:
        assert h == h.lower()
        i = lastindex.get(h, len(headers))
        while i > 0:
            i -= 1
            if h == headers[i][0].lower():
                sign_headers.append(headers[i])
                break
        lastindex[h] = i
    return sign_headers

# FWS  =  ([*WSP CRLF] 1*WSP) /  obs-FWS ; Folding white space  [RFC5322]
FWS = br'(?:(?:\s*\r?\n)?\s+)?'
RE_BTAG = re.compile(br'([;\s]b'+FWS+br'=)(?:'+FWS+br'[a-zA-Z0-9+/=])*(?:\r?\n\Z)?')

def hash_headers(hasher, canonicalize_headers, headers, include_headers,
                 sigheader, sig):
    """Update hash for signed message header fields."""
    sign_headers = select_headers(headers,include_headers)
    # The call to _remove() assumes that the signature b= only appears
    # once in the signature header
    cheaders = canonicalize_headers.canonicalize_headers(
        [(sigheader[0], RE_BTAG.sub(b'\\1',sigheader[1]))])
    # the dkim sig is hashed with no trailing crlf, even if the
    # canonicalization algorithm would add one.
    for x,y in sign_headers + [(x, y.rstrip()) for x,y in cheaders]:
        hasher.update(x)
        hasher.update(b":")
        hasher.update(y)
    return sign_headers

def validate_signature_fields(sig, sign_type = Signature.dkim):
    """Validate Signature fields.

    Basic checks for presence and correct formatting of mandatory fields.
    Raises a ValidationError if checks fail, otherwise returns None.

    @param sig: A dict mapping field keys to values.
    """
    if sign_type is Signature.dkim:
        mandatory_fields = (b'v', b'a', b'b', b'bh', b'd', b'h', b's')
    elif sign_type is Signature.ams:
        mandatory_fields = (b'i', b'a', b'b', b'bh', b'd', b'h', b's')
    elif sign_type is Signature.aseal:
        mandatory_fields = (b'i', b'a', b'b', b'd', b's', b'cv')
    else:
        raise InvalidSignatureTypeError

    for field in mandatory_fields:
        if field not in sig:
            raise ValidationError("signature missing %s=" % field)

    if b'v' in sig and sig[b'v'] != b"1":
        raise ValidationError("v= value is not 1 (%s)" % sig[b'v'])
    if re.match(br"[\s0-9A-Za-z+/]+=*$", str.encode(sig[b'b'])) is None:
        raise ValidationError("b= value is not valid base64 (%s)" % sig[b'b'])
    if b'bh' in sig and re.match(br"[\s0-9A-Za-z+/]+=*$", str.encode(sig[b'bh'])) is None:
        raise ValidationError(
            "bh= value is not valid base64 (%s)" % sig[b'bh'])
    # Nasty hack to support both str and bytes... check for both the
    # character and integer values.
    if b'l' in sig and re.match(br"\d{,76}$", str.encode(sig[b'l'])) is None:
        raise ValidationError(
            "l= value is not a decimal integer (%s)" % sig[b'l'])
    if b'q' in sig and sig[b'q'] != b"dns/txt":
        raise ValidationError("q= value is not dns/txt (%s)" % sig[b'q'])
    now = int(time.time())
    slop = 36000		# 10H leeway for mailers with inaccurate clocks
    t_sign = 0
    if b't' in sig:
        if re.match(br"\d+$", str.encode(sig[b't'])) is None:
            raise ValidationError(
        	"t= value is not a decimal integer (%s)" % sig[b't'])
        t_sign = int(sig[b't'])
        if t_sign > now + slop:
            raise ValidationError(
        	"t= value is in the future (%s)" % sig[b't'])

def rfc822_parse(message):
    """Parse a message in RFC822 format.

    @param message: The message in RFC822 format. Either CRLF or LF is an accepted line separator.
    @return: Returns a tuple of (headers, body) where headers is a list of (name, value) pairs.
    The body is a CRLF-separated string.
    """
    headers = []
    lines = re.split(b"\r?\n", str.encode(message))
    i = 0
    while i < len(lines):
        if len(lines[i]) == 0:
            # End of headers, return what we have plus the body, excluding the blank line.
            i += 1
            break
        if lines[i][0] in ("\x09", "\x20", 0x09, 0x20):
            headers[-1][1] += lines[i]+b"\r\n"
        else:
            m = re.match(br"([\x21-\x7e]+?):", lines[i])
            if m is not None:
                headers.append([m.group(1), lines[i][m.end(0):]+b"\r\n"])
            elif lines[i].startswith(b"From "):
                pass
            else:
                raise MessageFormatError("Unexpected characters in RFC822 header: %s" % lines[i])
        i += 1
    return (headers, b"\r\n".join(lines[i:]))

def text(s):
    """Normalize bytes/str to str for python 2/3 compatible doctests.
    >>> text(b'foo')
    'foo'
    >>> text(u'foo')
    'foo'
    >>> text('foo')
    'foo'
    """
    if type(s) is str: return s
    s = s.decode('ascii')
    if type(s) is str: return s
    return s.encode('ascii')

def fold(header):
    """Fold a header line into multiple crlf-separated lines at column 72.

    >>> text(fold(b'foo'))
    'foo'
    >>> text(fold(b'foo  '+b'foo'*24).splitlines()[0])
    'foo  '
    >>> text(fold(b'foo'*25).splitlines()[-1])
    ' foo'
    >>> len(fold(b'foo'*25).splitlines()[0])
    72
    """
    i = header.rfind(b"\r\n ")
    if i == -1:
        pre = b""
    else:
        i += 3
        pre = header[:i]
        header = header[i:]
    while len(header) > 72:
        i = header[:72].rfind(b" ")
        if i == -1:
            j = 72
        else:
            j = i + 1
        pre += header[:j] + b"\r\n "
        header = header[j:]
    return pre + header

#: Hold messages and options during signing and verification.
class DKIM(object):
  # NOTE - the first 2 indentation levels are 2 instead of 4 
  # to minimize changed lines from the function only version.

  #: The U{RFC5322<http://tools.ietf.org/html/rfc5322#section-3.6>}
  #: complete list of singleton headers (which should
  #: appear at most once).  This can be used for a "paranoid" or
  #: "strict" signing mode.
  #: Bcc in this list is in the SHOULD NOT sign list, the rest could
  #: be in the default FROZEN list, but that could also make signatures 
  #: more fragile than necessary.  
  #: @since: 0.5
  RFC5322_SINGLETON = (b'date',b'from',b'sender',b'reply-to',b'to',b'cc',b'bcc',
        b'message-id',b'in-reply-to',b'references')

  #: Header fields to protect from additions by default.
  #: 
  #: The short list below is the result more of instinct than logic.
  #: @since: 0.5
  FROZEN = (b'from',b'date',b'subject')

  #: The rfc4871 recommended header fields to sign
  #: @since: 0.5
  SHOULD = (
    b'sender', b'reply-to', b'subject', b'date', b'from', b'message-id', b'to', b'cc',
    b'mime-version', b'content-type', b'content-transfer-encoding',
    b'content-id', b'content- description', b'resent-date', b'resent-from',
    b'resent-sender', b'resent-to', b'resent-cc', b'resent-message-id',
    b'in-reply-to', 'references', b'list-id', b'list-help', b'list-unsubscribe',
    b'list-subscribe', b'list-post', b'list-owner', b'list-archive'
  )

  #: The rfc4871 recommended header fields not to sign.
  #: @since: 0.5
  SHOULD_NOT = (
    b'return-path',b'received',b'comments',b'keywords',b'bcc',b'resent-bcc',
    b'dkim-signature'
  )

  #: Create a DKIM instance to sign and verify rfc5322 messages.
  #:
  #: @param message: an RFC822 formatted message to be signed or verified
  #: (with either \\n or \\r\\n line endings)
  #: @param logger: a logger to which debug info will be written (default None)
  #: @param signature_algorithm: the signing algorithm to use when signing
  def __init__(self,message=None,logger=None,signature_algorithm=b'rsa-sha256',
        minkey=1024):
    self.set_message(message)
    if logger is None:
        logger = get_default_logger()
    self.logger = logger
    if signature_algorithm not in HASH_ALGORITHMS:
        raise ParameterError(
            "Unsupported signature algorithm: "+signature_algorithm)
    self.signature_algorithm = signature_algorithm
    #: Header fields which should be signed.  Default from RFC4871
    self.should_sign = set(DKIM.SHOULD)
    #: Header fields which should not be signed.  The default is from RFC4871.
    #: Attempting to sign these headers results in an exception.
    #: If it is necessary to sign one of these, it must be removed
    #: from this list first.
    self.should_not_sign = set(DKIM.SHOULD_NOT)
    #: Header fields to sign an extra time to prevent additions.
    self.frozen_sign = set(DKIM.FROZEN)
    #: Minimum public key size.  Shorter keys raise KeyFormatError. The
    #: default is 1024
    self.minkey = minkey

  def add_frozen(self,s):
    """ Add headers not in should_not_sign to frozen_sign.
    @param s: list of headers to add to frozen_sign
    @since: 0.5

    >>> dkim = DKIM()
    >>> dkim.add_frozen(DKIM.RFC5322_SINGLETON)
    >>> [text(x) for x in sorted(dkim.frozen_sign)]
    ['cc', 'date', 'from', 'in-reply-to', 'message-id', 'references', 'reply-to', 'sender', 'subject', 'to']
    """
    self.frozen_sign.update(x.lower() for x in s
        if x.lower() not in self.should_not_sign)

  #: Load a new message to be signed or verified.
  #: @param message: an RFC822 formatted message to be signed or verified
  #: (with either \\n or \\r\\n line endings)
  #: @since: 0.5
  def set_message(self,message):
    if message:
      self.headers, self.body = rfc822_parse(message)
    else:
      self.headers, self.body = [],''
    #: The signing domain last signed or verified.
    self.domain = None
    #: The key selector last signed or verified.
    self.selector = 'default'
    #: Signature parameters of last sign or verify.  To parse
    #: a Signature header field that you have in hand,
    #: use L{dkim.util.parse_tag_value}.
    self.signature_fields = {}
    #: The list of headers last signed or verified.  Each header
    #: is a name,value tuple.  FIXME: The headers are canonicalized.
    #: This could be more useful as original headers.
    self.signed_headers = []
    #: The public key size last verified.
    self.keysize = 0

  def default_sign_headers(self):
    """Return the default list of headers to sign: those in should_sign or
    frozen_sign, with those in frozen_sign signed an extra time to prevent
    additions.
    @since: 0.5"""
    hset = self.should_sign | self.frozen_sign
    include_headers = [ x for x,y in self.headers
        if x.lower() in hset ]
    return include_headers + [ x for x in include_headers
        if x.lower() in self.frozen_sign]

  def all_sign_headers(self):
    """Return header list of all existing headers not in should_not_sign.
    @since: 0.5"""
    return [x for x,y in self.headers if x.lower() not in self.should_not_sign]

  def set_ams_headers(self):
    """Return header list to sign in the ARC Message Signature."""
    headers = list(DKIM.SHOULD)
    sigheaders = [(x,y) for x,y in self.headers if x.lower() == b"arc-authentication-results"]
    instances = len(sigheaders)
    for i in range(1, instances):
        headers.append(b'arc-authentication-results')
    sigheaders = [(x,y) for x,y in self.headers if x.lower() == b"dkim-signature"]
    instances = len(sigheaders)
    for i in range(1, instances):
        headers.append(b'dkim-signature')
    headers = tuple(headers)
    return headers

  def set_aseal_headers(self, idx):
    """Return header list to sign/verify in the ARC Seal."""
    sigheaders = [(x,y) for x,y in self.headers if x.lower() == b"arc-seal"]
    instances = len(sigheaders)
    headers = list()
    for i in range(1, idx):
        headers.append(b'arc-authentication-results')
        headers.append(b'arc-message-signature')
        headers.append(b'arc-seal')
    headers.append(b'arc-authentication-results')
    headers.append(b'arc-message-signature')
    headers = tuple(headers)
    return headers

  #: Sign an RFC822 message and return the Signature header line.
  #: The Signature may be either the DKIM-Signature, ARC-Message-Signature
  #: or the ARC-Seal depending upon the sign_type parameter.
  #:
  #: The include_headers option gives full control over which header fields
  #: are signed.  Note that signing a header field that doesn't exist prevents
  #: that field from being added without breaking the signature.  Repeated
  #: fields (such as Received) can be signed multiple times.  Instances
  #: of the field are signed from bottom to top.  Signing a header field more
  #: times than are currently present prevents additional instances
  #: from being added without breaking the signature. Also, note that in case
  #: of the ARC-Seal, the include_headers parameter must be left empty since
  #: for ARC-Seal the headers are implicit.
  #:
  #: The length option allows the message body to be appended to by MTAs
  #: enroute (e.g. mailing lists that append unsubscribe information)
  #: without breaking the signature.
  #:
  #: The default include_headers for this method differs from the backward
  #: compatible sign function, which signs all headers not 
  #: in should_not_sign.  The default list for this method can be modified 
  #: by tweaking should_sign and frozen_sign (or even should_not_sign).
  #: It is only necessary to pass an include_headers list when precise control
  #: is needed.
  #:
  #: @param selector: the DKIM/ARC selector value for the signature
  #: @param domain: the DKIM/ARC domain value for the signature
  #: @param privkey: a PKCS#1 private key in base64-encoded text form
  #: @param identity: the DKIM/ARC identity value for the signature
  #: (default "@"+domain)
  #: @param canonicalize: the canonicalization algorithms to use
  #: (default (Relaxed, Relaxed))
  #: @param include_headers: a list of strings indicating which headers
  #: are to be signed (default rfc4871 recommended headers)
  #: @param length: true if the l= tag should be included to indicate
  #: body length signed (default False).
  #: @param sign_type: the type of signature - DKIM, AMS or AS, being crafted.
  #: @param cv: the chain validation status for the received ARC chain. To be
  #: specified only when signing the ARC-Seal.
  #: @return: DKIM/AMS/AS-Signature header field terminated by '\r\n'
  #: @raise DKIMException: when the message, include_headers, or key are badly
  #: formed.
  def sign(self, selector, domain, privkey, identity=None,
        canonicalize=(b'relaxed',b'relaxed'), include_headers=None, length=False,
        sign_type=Signature.dkim, cv=None):
    try:
        pk = parse_pem_private_key(privkey)
    except UnparsableKeyError as e:
        raise KeyFormatError(str(e))

    if identity is not None and not identity.endswith(domain):
        raise ParameterError("identity must end with domain")

    canon_policy = CanonicalizationPolicy.from_c_value(
        b'/'.join(canonicalize))
    headers = canon_policy.canonicalize_headers(self.headers)

    if include_headers is None:
        if sign_type is Signature.dkim:
            include_headers = self.default_sign_headers()
        elif sign_type is Signature.ams:
            include_headers = self.set_ams_headers()
        elif sign_type is Signature.aseal:
            sigheaders = [(x,y) for x,y in self.headers if x.lower() == b"arc-seal"]
            i = len(sigheaders)+1
            include_headers = self.set_aseal_headers(i)
        else:
            raise InvalidSignatureTypeError

    # rfc4871 says FROM is required
    if sign_type is not Signature.aseal:
        if b'from' not in ( x.lower() for x in include_headers ):
            raise ParameterError("The From header field MUST be signed")
        for x in include_headers:
            if x.lower() in self.should_not_sign:
                raise ParameterError("The %s header field SHOULD NOT be signed"%x)

    body = canon_policy.canonicalize_body(self.body)

    hasher = HASH_ALGORITHMS[self.signature_algorithm]
    h = hasher()
    h.update(body)
    bodyhash = base64.b64encode(h.digest())

    # Set the sigfields.
    sigfields = list()
    sigfields = [x for x in [
        (b'a', self.signature_algorithm),
        (b'd', domain),
        (b's', selector),
        (b't', str(int(time.time())).encode('ascii')),
    ] if x]

    if sign_type is Signature.dkim:
        sigfields += [x for x in [
            (b'v', b"1"),
            (b'c', canon_policy.to_c_value()),
            (b'i', identity or b"@"+domain),
            (b'q', b"dns/txt"),
            length and (b'l', len(body)),
            (b'h', b" : ".join(include_headers)),
            (b'bh', bodyhash),
            (b'b', b'0'*60),
        ] if x]

    elif sign_type is Signature.ams:
        sigheaders = [(x,y) for x,y in self.headers if x.lower() == b"arc-message-signature"]
        i = len(sigheaders)+1
        sigfields += [x for x in [
            (b'i', str(i)),
            (b'c', b"relaxed/relaxed"),
            (b'h', b" : ".join(include_headers)),
            (b'bh', bodyhash),
            (b'b', b'0'*60),
        ] if x]

    elif sign_type is Signature.aseal:
        sigheaders = [(x,y) for x,y in self.headers if x.lower() == b"arc-seal"]
        i = len(sigheaders)+1
        sigfields += [x for x in [
            (b'i', str(i)),
            (b'cv', cv),
            (b'b', b'0'*60),
        ] if x]

    include_headers = [x.lower() for x in include_headers]
    # record what verify should extract
    self.include_headers = tuple(include_headers)

    sig_value = fold(b"; ".join(b"=".join(x) for x in sigfields))
    sig_value = RE_BTAG.sub(b'\\1',sig_value)
    if sign_type is Signature.dkim:
        sign_header = (b'DKIM-Signature', b' ' + sig_value)
    elif sign_type is Signature.ams:
        sign_header = (b'ARC-Message-Signature', b' ' + sig_value)
    elif sign_type is Signature.aseal:
        sign_header = (b'ARC-Seal', b' ' + sig_value)
    h = hasher()
    sig = dict(sigfields)
    self.signed_headers = hash_headers(
        h, canon_policy, headers, include_headers, sign_header,sig)
    self.logger.debug("sign headers: %r" % self.signed_headers)

    try:
        sig2 = RSASSA_PKCS1_v1_5_sign(h, pk)
    except DigestTooLargeError:
        raise ParameterError("digest too large for modulus")
    # Folding b= is explicity allowed, but yahoo and live.com are broken
    #sig_value += base64.b64encode(bytes(sig2))
    # Instead of leaving unfolded (which lets an MTA fold it later and still
    # breaks yahoo and live.com), we change the default signing mode to
    # relaxed/relaxed (for broken receivers), and fold now.
    sig_value = fold(sig_value + base64.b64encode(bytes(sig2)))

    self.domain = domain
    self.selector = selector
    self.signature_fields = sig
    if sign_type is Signature.dkim:
        return b'DKIM-Signature: ' + sig_value + b"\r\n"
    elif sign_type is Signature.ams:
        return b'ARC-Message-Signature: ' + sig_value + b"\r\n"
    elif sign_type is Signature.aseal:
        return b'ARC-Seal: ' + sig_value + b"\r\n"

  #: Verify a DKIM/ARC signature.
  #: @type idx: int
  #: @param idx: which signature to verify.  The first (topmost) signature is 0.
  #: @param sign_type: the type of signature - DKIM, AMS or AS, being crafted.
  #: @type dnsfunc: callable
  #: @param dnsfunc: an option function to lookup TXT resource records
  #: for a DNS domain.  The default uses dnspython or pydns.
  #: @return: True if signature verifies or False otherwise
  #: @raise DKIMException: when the message, signature, or key are badly formed
  def verify(self,message=None,idx=0,sign_type=Signature.dkim,dnsfunc=get_txt):
    if message:
        self.set_message(message)
    if sign_type is Signature.dkim:
        sigheaders = [(x,y) for x,y in self.headers if x.lower() == b"dkim-signature"]
    elif sign_type is Signature.ams:
        sigheaders = [(x,y) for x,y in self.headers if x.lower() == b"arc-message-signature"]
    elif sign_type is Signature.aseal:
        sigheaders = [(x,y) for x,y in self.headers if x.lower() == b"arc-seal"]
    else:
        raise InvalidSignatureTypeError

    if len(sigheaders) <= idx:
        return False

    # By default, we validate the first Signature line found.
    try:
        sig = parse_tag_value(sigheaders[idx][1])
        self.signature_fields = sig
    except InvalidTagValueList as e:
        raise MessageFormatError(e)

    logger = self.logger
    logger.debug("sig: %r" % sig)

    validate_signature_fields(sig, sign_type)
    self.domain = sig[b'd']
    self.selector = sig[b's']

    if b'c' in sig:
        try:
            canon_policy = CanonicalizationPolicy.from_c_value(sig.get(b'c'))
        except InvalidCanonicalizationPolicyError as e:
            raise MessageFormatError("invalid c= value: %s" % e.args[0])
    else:
        canon_policy = CanonicalizationPolicy.from_c_value('relaxed/relaxed')
    headers = canon_policy.canonicalize_headers(self.headers)
    body = canon_policy.canonicalize_body(self.body)

    try:
        hasher = HASH_ALGORITHMS[sig[b'a']]
    except KeyError as e:
        raise MessageFormatError("unknown signature algorithm: %s" % e.args[0])

    if b'l' in sig:
        body = body[:int(sig[b'l'])]

    # The ARC Seal does not contain the bodyhash.
    if sign_type is not Signature.aseal:
        h = hasher()
        h.update(body)
        bodyhash = h.digest()
        logger.debug("bh: %s" % base64.b64encode(bodyhash))
        try:
            bh = base64.b64decode(re.sub(br"\s+", b"", sig[b'bh']))
        except TypeError as e:
            raise MessageFormatError(str(e))
        if bodyhash != bh:
            raise ValidationError(
                "body hash mismatch (got %s, expected %s)" %
                (base64.b64encode(bodyhash), sig[b'bh']))

    name = sig[b's'] + b"._domainkey." + sig[b'd'] + b"."
    s = dnsfunc(name)
    if not s:
        raise KeyFormatError("missing public key: %s"%name)
    try:
        if type(s) is str:
          s = s.encode('ascii')
        pub = parse_tag_value(s)
    except InvalidTagValueList as e:
        raise KeyFormatError(e)
    try:
        pk = parse_public_key(base64.b64decode(pub[b'p']))
        self.keysize = bitsize(pk['modulus'])
    except KeyError:
        raise KeyFormatError("incomplete public key: %s" % s)
    except (TypeError,UnparsableKeyError) as e:
        raise KeyFormatError("could not parse public key (%s): %s" % (pub[b'p'],e))

    if sign_type is Signature.aseal:
        instance = len(sigheaders) - idx
        include_headers = self.set_aseal_headers(instance)
    else:
        include_headers = [x.lower() for x in re.split(br"\s*:\s*", str.encode(sig[b'h']))]
    self.include_headers = tuple(include_headers)
    # address bug#644046 by including any additional From header
    # fields when verifying.  Since there should be only one From header,
    # this shouldn't break any legitimate messages.  This could be
    # generalized to check for extras of other singleton headers.
    if b'from' in include_headers:
      include_headers.append(b'from')      
    h = hasher()
    self.signed_headers = hash_headers(
        h, canon_policy, headers, include_headers, sigheaders[idx], sig)
    try:
        signature = base64.b64decode(re.sub(br"\s+", b"", str.encode(sig[b'b'])))
        res = RSASSA_PKCS1_v1_5_verify(h, signature, pk)
        if res and self.keysize < self.minkey:
          raise KeyFormatError("public key too small: %d" % self.keysize)
        return res
    except (TypeError,DigestTooLargeError) as e:
        raise KeyFormatError("digest too large for modulus: %s"%e)

def sign(message, selector, domain, privkey, identity=None,
         canonicalize=(b'relaxed', b'relaxed'),
         signature_algorithm=b'rsa-sha256',
         include_headers=None, length=False, logger=None, sign_type=Signature.dkim,
         cv=None):
    """Sign an RFC822 message and return the DKIM/AMS/AS-Signature header line.
    @param message: an RFC822 formatted message (with either \\n or \\r\\n line endings)
    @param selector: the DKIM/ARC selector value for the signature
    @param domain: the DKIM/ARC domain value for the signature
    @param privkey: a PKCS#1 private key in base64-encoded text form
    @param identity: the DKIM/ARC identity value for the signature (default "@"+domain)
    @param canonicalize: the canonicalization algorithms to use (default (Relaxed, Relaxed))
    @param include_headers: a list of strings indicating which headers are to be signed (default all headers not listed as SHOULD NOT sign)
    @param length: true if the l= tag should be included to indicate body length (default False)
    @param logger: a logger to which debug info will be written (default None)
    @param sign_type: the type of signature - DKIM, AMS or AS, being crafted.
    @param cv: the chain validation status for the received ARC chain. To be
    specified only when signing the ARC-Seal.
    @return: DKIM/AMS/AS-Signature header field terminated by \\r\\n
    @raise DKIMException: when the message, include_headers, or key are badly formed.
    """

    d = DKIM(message,logger=logger)
    if not include_headers:
        include_headers = d.default_sign_headers()
    return d.sign(selector, domain, privkey, identity=identity, canonicalize=canonicalize, include_headers=include_headers,
        length=length, sign_type=sign_type, cv=cv)

def verify(message, logger=None, dnsfunc=get_txt, sign_type=Signature.dkim, minkey=1024):
    """Verify the first (topmost) DKIM signature on an RFC822 formatted message.
    @param message: an RFC822 formatted message (with either \\n or \\r\\n line endings)
    @param sign_type: the type of signature - DKIM, AMS or AS, being crafted.
    @param logger: a logger to which debug info will be written (default None)
    @return: True if signature verifies or False otherwise
    """

    d = DKIM(message,logger=logger,minkey=minkey)
    try:
        return d.verify(sign_type=sign_type, dnsfunc=dnsfunc)
    except DKIMException as x:
        if logger is not None:
            logger.error("%s" % x)
        return False
