# this sage script produces three candidate fields
# for fast arithmetic and of order roughly 2^128

# single prime of 128 bits
c = 0
for c in range(1, 10000):
    if c % 3 == 0:
        continue
    l = ceil(log(1.0*c, 2.0))
    if is_prime(c*(2^(128-l))+1):
        break

p = c*(2^(128-l))+1
#print("Field 1: ring of integers modulo", p, "=", c, "* 2^", (128-l), "+1 = (2^100 +", (c-2^100), ")*2^", (128-l), "+1")
print("Field 1: ring of integers modulo", p, "=", c, "* 2^", (128-l), "+1")
print("Modulus has ", len(bin(p)[2:]), "bits.")
F = FiniteField(p)
a = 2
for a in range(1, p):
    b = F(a)^c
    if b^(2^(128-l-1)) != 1:
        break
r = F(a)^c
print("Primitive root of unity:", r, "of order 2^", (128-l))
print("Field has roughly 2^", log(1.0*p, 2.0), "many elements")
print("")

# extension field of degree 4 over base prime that fits into 40 bits
c = 0
for c in range(1, 1000):
    if c % 3 == 0:
        continue
    l = ceil(log(1.0*c, 2.0))
    if is_prime(c*2^(40-l)+1):
        break
p = c * 2^(40-l) + 1
F = FiniteField(p)
Fx.<x> = PolynomialRing(F, "x")
for d in range(2, p):
    poly = x^4 + x + Fx(d)
    if poly.is_irreducible():
        break
print("Field 2: ring of polynomials modulo", poly, "with coefficients in ring of integers modulo", p, "=", c, "*2^", (40-l), "+1")
print("Base field modulus has ", len(bin(p)[2:]), "bits.")
a = 2
for a in range(1, p):
    b = F(a)^c
    if b^(2^(40-l-1)) != 1:
        break
r = F(a)^c
print("Primitive root of unity:", r, "of order 2^", (40-l))
print("Field has roughly 2^", 4*log(1.0*p, 2.0), "many elements")
print("")

# extension field of degree 5 over base prime that fits into 32 bits
c = 0
for c in range(1, 1000):
    if c % 3 == 0:
        continue
    l = ceil(log(1.0*c, 2.0))
    if is_prime(c*2^(32-l)+1):
        break
p = c * 2^(32-l) + 1
F = FiniteField(p)
Fx.<x> = PolynomialRing(F, "x")
for d in range(2, p):
    poly = x^5 + x + Fx(d)
    if poly.is_irreducible():
        break
print("Field 3: ring of polynomials modulo", poly, "with coefficients in ring of integers modulo", p, "=", c, "*2^", (32-l), "+1")
print("Base field modulus has ", len(bin(p)[2:]), "bits.")
a = 2
for a in range(1, p):
    b = F(a)^c
    if b^(2^(32-l-1)) != 1:
        break
r = F(a)^c
print("Primitive root of unity:", r, "of order 2^", (32-l))
print("Field has roughly 2^", 5*log(1.0*p, 2.0), "many elements")
print("")


