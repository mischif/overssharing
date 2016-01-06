OverSSHaring
============

Generate and break weak SSH keys that share primes.

Released under version 3.0 of the Non-Profit Open Software License.

# Usage

General Options
---------------

    --secrets out.asc, -s out.asc        Store secret keys in file
    --alternate-encoder                  Use an ASN.1 encoder made by someone else if mine has issues
    --verbose, -v                        Change the program's verbosity

Generating Keys
---------------

Simple usage:

    $ python overssharing.py make authorized_keys

Advanced usage:

    $ python overssharing.py make -h

    --bits n, -b n   Generate n-bit keys
    --count k, -c k  Generate k weak keys
    --exp e, -e e    Set public key exponent

Breaking keys
-------------

Simple usage:

    $ python overssharing.py -s privkeysgohere.txt break /root/.ssh/authorized_keys /home/user/.ssh/authorized_keys ...
