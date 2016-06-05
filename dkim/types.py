from enum import Enum

class Signature(Enum):
	dkim = 1
	ams = 2
	aseal = 3

class ChainStatus(Enum):
	N = 'none'
	P = 'pass'
	F = 'fail'
