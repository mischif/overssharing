#!/usr/bin/env python

################################################################################
#                                 OverSSHaring                                 #
#                       Generate and break weak SSH keys                       #
#                            (C) 2013, 2016 Mischif                            #
#       Released under version 3.0 of the Non-Profit Open Source License       #
################################################################################

import random
import logging
import argparse
from sys import exit
from fractions import gcd
from struct import pack, unpack
from math import sqrt, floor, ceil
from base64 import b64encode, b64decode
from binascii import hexlify, unhexlify
from itertools import combinations as choose, count, izip_longest

__version__ = "2.1.0"

class CustomLogs(logging.Formatter):
	FORMATS = {
	logging.DEBUG    : "[*] %(message)s",
	logging.INFO     : "[+] %(message)s",
	logging.WARNING    : "[!] %(message)s",
	logging.ERROR : "[-] %(message)s"
	}

	def format(self, record):
		self._fmt = self.FORMATS.get(record.levelno,
			self.FORMATS[logging.DEBUG])
		return logging.Formatter.format(self, record)

class Util(object):

	r = random.SystemRandom()
	log = logging.getLogger(__name__)
	ch = logging.StreamHandler()
	ch.setFormatter(CustomLogs())
	log.addHandler(ch)

	@staticmethod
	def get_key_info(pk):
		"""
		Seperates an RFC4253 SSH public key string into its components
		and returns a dictionary of said components.
		Hat tip to:
		http://blog.oddbit.com/2011/05/08/converting-openssh-public-keys

		Output:
		{
		"n": Modulus of public key
		"e": Exponent of public key
		"c": comment of public key
		}
		"""

		out = {}
		parts = []
		s = pk.split()
		rawdata = b64decode(s[1])

		# Retain the comment if there is one
		out["c"] = None if len(s) < 3 else " ".join(s[2:])

		while rawdata:
			# Get the size of the next part of the key
			dlen = unpack('>I', rawdata[:4])[0]

			# Read the data
			data, rawdata = rawdata[4:dlen+4], rawdata[4+dlen:]

			parts.append(data)

		out["e"] = int(hexlify(parts[1]), 16)
		out["n"] = int(hexlify(parts[2]), 16)

		return out

	@staticmethod
	def mod_inv(e, phi):
		"""
		Generate inverse of e mod phi
		"""

		x, lastx = 0, 1
		a, b = phi, e
		while b:
			a, q, b = b, a // b, a % b
			x, lastx = lastx - q * x, x
		result = (1 - lastx * phi) // e
		if result < 0: result += phi
		assert 0 <= result < phi and e * result % phi == 1
		return result

	@staticmethod
	def int_to_bytes(n):
		"""
		Returns big-endian byte string of given integer with associated length.

		Output:
		(len(bytearray(n)), bytearray(n))
		"""

		l = max(int(ceil(n.bit_length() / 8.0)), 1)
		fmt = "{{:0{}x}}".format(l * 2)
		out = bytearray(unhexlify(fmt.format(n)))
		return (l, out)

	@staticmethod
	def packed_with_int_length(d):
		"""
		Given an integer or string, returns it as a bytestring prepended with
		its length.

		Output:
		result[:4]	big-endian length value
		result[4:]	byte string of input
		"""

		fmt = None
		data = d
		length = 0

		# If a number, convert to bytes and prepare for packing
		if type(d) is int \
		or type(d) is long:
			length, data = Util.int_to_bytes(d)
			data = bytearray(pack(">I", length)) + data

		# If a string, prepare for packing
		elif type(d) is str:
			length = len(d)
			fmt = ">I{}s".format(length)
			data = bytearray(pack(fmt, length, data))

		elif type(d) is bytearray:
			raise TypeError

		# Pack and return
		return data

	@staticmethod
	def packed_with_separate_length(d):
		"""
		Given an integer or string, returns a tuple (lengthData, data).
		
		Output (All big-endian):
		if len(s) < 127:
			lengthData				length value
			data					byte string of s

		if len(s) > 127:
			lengthData[0] - 0x80			length value byte count
			lengthData[1:lengthData[0] - 0x7F]	length value
			data					byte string of s
		"""

		packLen = 0
		sizeLen = 0
		data = bytearray()
		sizeData = ""
		lengthData = bytearray()

		# Numbers with their highest bit set (e.g. num[0] & 0x80)
		# need a null between their prepended length and the start of
		# the number for some reason I don't know but am sure can be
		# found in the bowels of the ASN.1 RFC.
		if type(d) is int \
		or type(d) is long:
			packLen, data = Util.int_to_bytes(d)
			if (data[0] & ord("\x80")):
				packLen += 1
				data.insert(0, "\x00")

		elif type(d) is str:
			packLen = len(d)
			data.extend(pack(">{}s".format(len(d)), d))

		sizeLen, sizeData = Util.int_to_bytes(packLen)

		# If the data we are trying to pack is at least 128 bytes in
		# size, we must add 0x80 to the size of the int that holds the
		# size of the data and prepend that to said int
		if packLen > 127: lengthData.append(ord("\x80") + sizeLen)

		lengthData.extend(sizeData)
		return (lengthData, data)

class PrimeGen(object):

	@staticmethod
	def miller_rabin(n):
		"""
		Performs the Miller-Rabin primality test.

		Returns True if n is a prime with high probability
		Returns False if n is composite
		"""

		s = n - 1
		t = 0

		while s & 0x1 == 0:
			s /= 2
			t += 1

		k = 0

		while k < 128:
			a = Util.r.randrange(2,n-1)
			v = pow(a,s,n)

			if v != 1:
				i = 0
				while v != (n - 1):
					if i == t - 1: return False
					else:
						i += 1
						v = pow(v,2,n)
			k += 2
		return True

	@staticmethod
	def is_prime(n):
		"""
		Determines if n is a prime larger than 10 bits.

		Returns True if n is a prime larger than 10 bits
		Returns False if n is composite or if n is a prime of at most 10 bits

		H/T to https://langui.sh/2009/03/07/generating-very-large-primes/
		for the prime list
		"""

		lowPrimes =	[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71
				,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149
				,151,157,163,167,173,179,181,191,193,197,199,211,223,227
				,229,233,239,241,251,257,263,269,271,277,281,283,293,307
				,311,313,317,331,337,347,349,353,359,367,373,379,383,389
				,397,401,409,419,421,431,433,439,443,449,457,461,463,467
				,479,487,491,499,503,509,521,523,541,547,557,563,569,571
				,577,587,593,599,601,607,613,617,619,631,641,643,647,653
				,659,661,673,677,683,691,701,709,719,727,733,739,743,751
				,757,761,769,773,787,797,809,811,821,823,827,829,839,853
				,857,859,863,877,881,883,887,907,911,919,929,937,941,947
				,953,967,971,977,983,991,997,1009,1013,1019,1021]

		for p in lowPrimes:
			if not n % p: return False
		return PrimeGen.miller_rabin(n)

	@staticmethod
	def make_prime(k):
		"""
		Generates a k-bit prime.

		Returns a number 2 ** (k-1) < n < 2 ** k
		"""

		num = 3
		while not PrimeGen.is_prime(num): num = Util.r.randrange(pow(2,k-1),pow(2,k)) | 1
		return num

class Keypair(object):

	n = 0
	pk = ""
	sk = ""
	comment = ""

	def __eq__(self, other):
		return self.n == other.n
		
	def __init__(self, p, q, e, comment = None):
		Util.log.info("Creating new keypair")

		self.n = p * q
		phi = (p - 1) * (q - 1)

		if comment: self.comment = comment
		else: self.comment = "Public Key {}".format(self.n % 1000000)

		if gcd(e, phi) == 1:
			Util.log.debug("e and phi coprime; moving on...")
		elif gcd(65537, phi) == 1:
			e = 65537
			Util.log.warning("Set e = 65537")
		elif gcd(3, phi) == 1:
			e = 3
			Util.log.warning("Set e = 3")
		else: raise ValueError(
			Util.log.error("Couldn't find coprime e; aborting"))

		d = Util.mod_inv(e, phi)

		assert (e * d) % phi == gcd(e, phi) == gcd(d, phi) == 1

		Util.log.debug("p: {}".format(p))
		Util.log.debug("q: {}".format(q))
		Util.log.debug("n: {}".format(self.n))
		Util.log.debug("phi: {}".format(phi))
		Util.log.debug("e: {}".format(e))
		Util.log.debug("d: {}".format(d))

		self.pk = self.make_pubkey(self.n, e, self.comment)

		if not args.alt_enc: self.sk = self.make_privkey(p, q, e, d)
		else: self.sk = self.make_privkey_with_encoder(p, q, e, d)

	@staticmethod
	def make_pubkey(n, e, comment):
		"""
		Creates RFC4253-compliant SSH public key given modulus and exponent

		Returns a string representing the public key defined by n and e
		"""
		keystring = bytes("ssh-rsa ")
		dataString = Util.packed_with_int_length("ssh-rsa")
		dataString.extend(Util.packed_with_int_length(e))

		length, data = Util.int_to_bytes(n)
		dataString.extend(pack(">I", length + 1))
		# Just to pack in another null
		dataString.extend("\x00" + data)

		return "{}{} {}".format(keystring,
			b64encode(dataString), bytes(comment))

	@staticmethod
	def make_privkey(p, q, d, e):
		"""
		Creates RFC2313-compliant SSH private key given primes and exponents

		Returns a string representing the private key defined by p, q, e and d
		"""

		keystring = bytearray("\x30")
		totalSize = 0
		workString = bytearray()

		# First, get all the parts of a privkey together
		for term in \
		[0, (p*q), e, d, p, q, d%(p-1), d%(q-1), Util.mod_inv(q,p)]:
			lenData, data = Util.packed_with_separate_length(term)
			totalSize += len(data) + len(lenData) + 1
			workString.extend("\x02" + lenData + data)

		packLen, data = Util.packed_with_separate_length(totalSize)

		# If the components of the key are at least 128 bytes in size,
		# we must add 0x80 to the size of the int that holds the size of
		# the data and prepend that to said int
		if totalSize > 127:
			Util.log.debug("Total key length: {}".format(totalSize))

			Util.log.debug("Length data: {}".format(
				"".join(["\\x%02x" % c for c in data])))

			Util.log.debug("Pack length: {}".format(
				"".join(["\\x%02x" % (ord("\x80") + ord(packLen))])))

			# I treat packLen as a small int here, since if packLen
			# was at least 128, that would mean totalSize needs at
			# least 2 ** 128 bits to be represented, I doubt anyone
			# anywhere has written code that can represent such a
			# number
			keystring.extend(chr(ord("\x80") + ord(packLen)))

		keystring.extend(data + workString)
		keystring = b64encode(keystring)

		outString = ["-----BEGIN RSA PRIVATE KEY-----"] \
		 + ["".join(i) for i in izip_longest(
		 	*[iter(keystring)] * 64, fillvalue = "")] \
		 + ["-----END RSA PRIVATE KEY-----"]

		return "\n".join(outString)

	@staticmethod
	def make_privkey_with_encoder(p, q, d, e):
		"""
		Creates RFC2313-compliant SSH private key given primes and exponents
		using a nonstandard encoder.

		Returns a string representing the private key defined by p, q, e and d
		"""

		from pyasn1.codec.der import encoder		# Use these with the other
		from pyasn1.type.univ import Sequence, Integer	# private key encoder

		s = Sequence()
		for index, value in enumerate(map(Integer,
			(0, (p*q), e, d, p, q, d%(p-1), d%(q-1), Util.mod_inv(q,p)))):
			s.setComponentByPosition(index, value)

		keystring = b64encode(encoder.encode(s))
		outString = ["-----BEGIN RSA PRIVATE KEY-----"] \
		 + ["".join(i) for i in izip_longest(
		 	*[iter(keystring)] * 64, fillvalue = "")] \
		 + ["-----END RSA PRIVATE KEY-----"]

		return "\n".join(outString)

def make_keys(args):
	keys = []
	primes = []
	primeCount = next(i for i in count(2) if args.count <= (i * (i - 1) / 2))

	Util.log.info("Making {} {}-bit keys with exponent {}".format(
		args.count, args.bits, args.exp))

	Util.log.debug("Desired keycount requires {} primes".format(primeCount))

	Util.log.info("Generating primes...")
	while len(primes) < primeCount:
		primes.append(PrimeGen.make_prime((args.bits / 2) + 1))

	Util.log.info("Generating keys...")
	while len(keys) < args.count:
		p, q = Util.r.sample(primes, 2)

		# First, make sure we don't get the same prime twice
		if p == q:
			Util.log.warning("Got the same prime twice")
			continue

		kp = Keypair(p, q, args.exp)

		# Then, make sure we haven't gotten this pair of primes already
		if kp in keys:
			Util.log.warning("Got the same pair of primes multiple times")
			continue

		# Seems legit
		keys.append(kp)

	Util.log.info("Writing keys...")
	for key in keys:
		Util.log.debug("pubkey: {}".format(key.pk))
		args.outFile.write(key.pk + "\n")

		if args.secrets:
			Util.log.debug("seckey:\n{}".format(key.sk))
			args.secrets.write(
			"Private Key for {}\n{}\n".format(key.comment, key.sk))

	Util.log.info("Done!")

def break_keys(args):
	pubkeys = []
	keys = []

	for keyfile in args.keyfiles:
		for line in keyfile:
			if line[:7] != "ssh-rsa": continue
			else:
				pubkeys.append(Util.get_key_info(line))
				Util.log.debug("Adding keyfile {}".format(pubkeys[-1]["c"]))

	Util.log.info("SSH pubkeys found: {}".format(len(pubkeys)))

	for pk in pubkeys:
		Util.log.debug("Have key {}".format(pk["c"]))
	if len(pubkeys) < 2:
		exit(Util.log.error("Not enough keys to crack"))

	Util.log.info("Searching for collisions...")
	for pks in choose(pubkeys, 2):
		p = gcd(pks[0]["n"], pks[1]["n"])
		if p > 1:
			Util.log.info("Collision between {} and {}".format(
				pks[0]["c"], pks[1]["c"]))

			q1 = pks[0]["n"] / p
			q2 = pks[1]["n"] / p

			keys.append(Keypair(p, q1, pks[0]["e"], pks[0]["c"]))
			keys.append(Keypair(p, q2, pks[1]["e"], pks[1]["c"]))

	Util.log.info("{} private keys found".format(len(keys)))
	for key in keys:
		args.secrets.write(
			"Private Key for {}\n{}\n".format(key.comment, key.sk))

	Util.log.info("Done!")

if __name__ == "__main__":
	parser = argparse.ArgumentParser(
		prog = "OverSSHaring",
		description = "Generate and break weak SSH keys",
		epilog = "(C) 2013, 2016 Mischif; released under NPOSL-3.0")

	parser.add_argument("--version",
		action = "version",
		version = "%(prog)s {}".format(__version__))

	parser.add_argument("--verbose", "-v",
		action = "store_true",
		help = "Change the program's verbosity")

	parser.add_argument("--secrets", "-s",
		type = argparse.FileType('w'),
		metavar = "out.asc",
		help = "Store secret keys in file")

	parser.add_argument("--alternate-encoder",
		action = "store_true",
		dest = "alt_enc",
		help = "Use an alternate ASN.1 encoder if mine has issues")

	sp = parser.add_subparsers(
	title = "Commands",
	metavar = "")

	make_parser = sp.add_parser("make",
		help = "Generate weak SSH keys")
	make_parser.set_defaults(func = make_keys)

	make_parser.add_argument("--bits", "-b",
		type = int,
		default = 2048,
		metavar = "n",
		help = "Generate n-bit keys")

	make_parser.add_argument("--count", "-c",
		type = int,
		default = 2,
		metavar = "k",
		help = "Generate k weak keys")

	make_parser.add_argument("--exp", "-e",
		type = int,
		default = 65537,
		metavar = "e",
		help = "Set public key exponent")

	make_parser.add_argument("outFile",
		type = argparse.FileType('w'),
		help = "Output file for generated public keys")


	break_parser = sp.add_parser("break",
		help = "Break weak SSH keys")
	break_parser.set_defaults(func = break_keys)
	
	break_parser.add_argument("keyfiles",
		type = argparse.FileType('r'),
		nargs = "+",
		help = "File(s) containing weak SSH public keys")

	args = parser.parse_args()

	if args.verbose: Util.log.setLevel(logging.DEBUG)
	else: Util.log.setLevel(logging.INFO)

	args.func(args)
