#!/bin/env python

import random
import argparse
from fractions import gcd
from struct import pack, unpack
from math import sqrt, floor, ceil
from base64 import b64encode, b64decode
from binascii import hexlify

debug = False

###			     Prime Generation Stuff			     ###

def RabinMiller(n, rand):
### Simple Rabin-Miller primality test ###
     s = n - 1
     t = 0

     while s & 0x1 == 0:
         s /= 2
         t += 1

     k = 0

     while k < 128:
         a = rand.randrange(2,n-1)
         v = pow(a,s,n)
         if v != 1:
             i = 0
             while v != (n - 1):
                 if i == t - 1:
                     return False
                 else:
                     i += 1
                     v = pow(v,2,n)
         k += 2
     return True

def IsGoodPrime(n, rand):
### Returns true if n is a prime larger than 10 bits ###
### H/T to https://langui.sh/2009/03/07/generating-very-large-primes/
### for the prime list ###

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
		if n % p == 0 or n == p : return False

	return RabinMiller(n, rand)

def GenPrime(k, rand):
### Generates k-bit primes ###
	maybePrime = (rand.randrange(pow(2,k-1),pow(2,k)) | 1)
	while not IsGoodPrime(maybePrime, rand):
		maybePrime = (rand.randrange(pow(2,k-1),pow(2,k)) | 1)
	return maybePrime

###			     Random helper functions			     ###

def ModInv(e, phi):
### Generate inverse of e mod phi ###
	x, lastx = 0, 1
	a, b = phi, e
	while b:
		a, q, b = b, a // b, a % b
		x, lastx = lastx - q * x, x
	result = (1 - lastx * phi) // e
	if result < 0: result += phi
	assert 0 <= result < phi and e * result % phi == 1
	return result

def IntToBytes(n):
### Returns big-endian byte string of given integer with associated length ###
	out = '%02X' % n
	if len(out) % 2: out = ('0%s' % out)
	return (len(out.decode("hex")),out.decode("hex"))

def PackedWithIntLength(s):
### Output:
###	result[:4]	big-endian length value
###	result[4:]	big-endian byte string of s

	if type(s) == type(1) or type(s) == type(8675309L):
		(length, bits) = IntToBytes(s)
		bitstring = pack(">I%ds" % length, length, bits)
		return bitstring

	if type(s) == type("str"):
		return pack(">I%ds" % len(s), len(s), s)

def PackedWithBareLength(s):
### Output (All big-endian):
###	if len(s) < 127:
###		lengthData				length value
###		data					byte string of s
###
###	if len(s) > 127:
###		lengthData[0] - 0x80			length value byte count
###		lengthData[1:lengthData[0] - 0x7F]	big-endian length value
###		data					byte string of s

	packLen = 0
	sizeLen = 0
	data = ""
	sizeData = ""
	lengthData = ""

	if type(s) == type(1) or type(s) == type(8675309L):
		(packLen, data) = IntToBytes(s)
		if (ord(data[0]) & ord("\x80")):
			packLen += 1
			data = "\x00" + data

	if type(s) == type("str"):
		packLen = len(s)
		data = pack(">%ds" % len(s), s)

	sizeLen, sizeData = IntToBytes(packLen)
	if packLen > 127: lengthData += chr(ord("\x80") + sizeLen)
	lengthData += sizeData
	return (lengthData, data)

###			 Actual key generation functions		     ###

def MakePubkey(n, e):
### Creates RFC4253-style SSH public key given modulus, exponent ###
	keystring = bytes("ssh-rsa ")
	dataString = PackedWithIntLength("ssh-rsa")
	dataString += PackedWithIntLength(e)

	(length, bits) = IntToBytes(n)
	dataString += pack(">I", length + 1)
	dataString += "\x00" + bits		# Just to pack in another null

	comment = " Public Key %d" % (n % 1000000)
	pk = keystring + b64encode(dataString) + bytes(comment)

	if debug: print "pubkey: \n\n%s\n" % pk
	return pk

def MakePrivkey(p, q, d, e):
### Creates RFC2313-style SSH private key given primes, exponents ###
	keystring = "\x30"
	totalSize = 0
	workString = ""
	for term in [0, (p*q), e, d, p, q, d%(p-1), d%(q-1), ModInv(q,p)]:
		(lengthData, data) = PackedWithBareLength(term)
		totalSize += len(data) + len(lengthData) + 1
		workString += "\x02" + lengthData + data

	(packLen, data) = PackedWithBareLength(totalSize)

	if totalSize > 127:
		if debug: print "total key length: %d" % totalSize
		if debug: print "length data: %s" % "".join(["\\x%s" % hexlify(x) for x in data])
		if debug: print "pack length: %s\n" % "".join(["\\x%s" % hexlify(x) for x in chr(ord("\x80") + ord(packLen))])
		keystring += chr(ord("\x80") + ord(packLen))
	keystring += data + workString
	keystring = b64encode(keystring)

	outString = bytes("-----BEGIN RSA PRIVATE KEY-----\n")
	for string in [keystring[i:i+64] for i in range(0, len(keystring), 64)]:
		outString += string + "\n"
	outString += bytes("-----END RSA PRIVATE KEY-----")

	return outString

def GenKeys(primes, pubExp):
### Creates RFC4253/RFC2313-style SSH keypair given primes, public exponent ###
	p = primes[0]
	q = primes[1]
	n = p * q
	phi = (p - 1) * (q - 1)

	if debug: print "Using primes: %d, %s" % (p, q)
	if gcd(pubExp, phi) != 1:
		if debug: print "e = %d, phi not coprime; trying e = 3" % pubExp
		pubExp = 3
		if gcd(pubExp, phi) != 1: 
			raise ValueError("e = 3, phi not coprime; aborting")

	d = ModInv(pubExp, phi)

	if debug:print "e = %d\nd = %d\nphi = %d\nn = %d\n" %(pubExp, d, phi, n)

	assert (pubExp * d) % phi == gcd(pubExp, phi) == gcd(d, phi) == 1

	testM = 8675309L
	testC = pow(testM, pubExp, n)
	assert pow(testC, d, n) == testM

	pubkey = MakePubkey(n, pubExp)
	privkey = MakePrivkey(p, q, d, pubExp)
	return (pubkey, privkey)

def main():
	keyList = []
	modTable = {}
	primeList = []
	rand = random.SystemRandom()

	if debug: print "Generating %d %d-bit keys with e = %d (requires %d primes)" % (keyCount, args.bitLen, pubExp, primeCount)

	if not debug: print "Generating primes..."
	while len(primeList) < primeCount: primeList.append(GenPrime(primeSize, rand))

	if not debug: print "Generating keys..."
	while len(keyList) < keyCount:
		parts = []
		(pubkey, privkey) = GenKeys(rand.sample(primeList, 2), pubExp)
		pkData = b64decode(pubkey.split()[1])

		while pkData:
			dlen = unpack('>I', pkData[:4])[0]
			data, pkData = pkData[4:dlen+4], pkData[4+dlen:]
			parts.append(data)

		n = eval('0x' + ''.join(['%02X' % unpack('B', x)[0] for x in parts[2]]))
		if n not in modTable:
			keyList.append(pubkey)
			modTable[n] = 1
			if showSecrets: print "Private key %d:\n\n%s\n" % (n % 1000000, privkey)

	if not debug: print "Writing public keys to file..."
	for pubKey in keyList: outFile.write(pubKey + "\n")
	outFile.close()

	print "Done!"
	return

if __name__ == "__main__":
	parser = argparse.ArgumentParser(prog="OverSSHaring", description='Generate weak SSH keys of various sizes', add_help=False, epilog='(C) 2013 Mischif, released under version 2.0 of the Mozilla Public License.\nThis Source Code Form is "Incompatible With Secondary Licenses", as defined\nby the stated license.')

	parser.add_argument("--bits", "-b", metavar="n", dest="bitLen", default=2048, type=int, help="Generate n-bit keys (default 2048)")
	parser.add_argument("--count", "-c", metavar="k", dest="keyCount", default=2, type=int, help="Generate k keys (default 2)")

	parser.add_argument("--exp", "-e", metavar="e", dest="pubExp", default=65537, type=int, help="Set public key exponent (default 65537)")
	parser.add_argument("--secrets", "-s", action='store_true', help="Display secret keys")
	parser.add_argument("--help", "-h", action="help", help="Show this help message")
	parser.add_argument("--version","-v",  action="version", version="%(prog)s 1.0")
	parser.add_argument("outFile", type=argparse.FileType('w'), help="Output file for generated public keys")
	args = parser.parse_args()

	pubExp = args.pubExp
	outFile = args.outFile
	keyCount = args.keyCount
	showSecrets = args.secrets
	primeSize = args.bitLen / 2
	primeCount = ceil(sqrt(2 * args.keyCount)) + 1

	main()

#from pyasn1.codec.der import encoder		# Use these with the other
#from pyasn1.type.univ import Sequence, Integer	# private key encoder
#def UseEncoder(p, q, d, e):
### An alternate encoder that I know works but requires nonstandard packages ###
#	s = Sequence()
#	for index, value in enumerate(map(Integer, (0, (p*q), e, d, p, q, d%(p-1), d%(q-1), ModInv(q,p)))):
#		s.setComponentByPosition(index, value)
#	keyString = b64encode(encoder.encode(s))
#	outString = bytes("-----BEGIN RSA PRIVATE KEY-----\n")
#	for string in [keyString[i:i+64] for i in range(0, len(keyString), 64)]:
#		outString += string + "\n"
#	outString += bytes("-----END RSA PRIVATE KEY-----")
#	return outString
