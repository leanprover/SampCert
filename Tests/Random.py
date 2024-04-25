import secrets

class Random:
    def UniformPowerOfTwoSample(n):
        return secrets.randbelow(n)
        #return secrets.randbits(n.bit_length()-1)
