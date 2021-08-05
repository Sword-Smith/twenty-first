# generate fields with roughly 2^160 elements or more
# must be FFT-friendly -- that is to say, they must have a large smooth subgroup of order 2^k with k > 24

print("generating fields ...")

# 1. find a large prime of 160 bits with an appropriate subgroup
print("Field 1:")
for k in range(0, 10000):
    cofactor = 2^135 - k
    if cofactor % 3 == 0:
        continue
    p = cofactor * 2^25 + 1
    if is_prime(p):
        break

F = FiniteField(p)
print("p:", p, "=", cofactor, "* 2^25 + 1. is prime?", is_prime(p), "bit width:", len(bin(p)[2:]))
print("base-2 log p =", log(1.0*p, 2.0))
print("cofactor:", cofactor, "=", factor(cofactor))
for k in range(2, 100000):
    omega = F(k)^cofactor
    if omega.multiplicative_order() == 2^25:
        break
print("primitive 2^25th root of unity:", omega, "=", k, "^", cofactor, "multiplicative order:", omega.multiplicative_order())
print("")

# 2. extension field of degree 3 over base field with 64 bits
print("Field 2:")
for k in range(0, 10000):
    cofactor = 2^39 - k
    if cofactor % 3 == 0:
        continue
    p = cofactor * 2^25 + 1
    if is_prime(p):
        break

F = FiniteField(p)
print("p:", p,  "=", cofactor, "* 2^25 + 1. is prime?", is_prime(p), "bit width:", len(bin(p)[2:]))
print("base-2 log p =", log(1.0*p, 2.0))
print("cofactor:", cofactor, "=", factor(cofactor))
for k in range(2, 100000):
    omega = F(k)^cofactor
    if omega.multiplicative_order() == 2^25:
        break
print("primitive 2^25th root of unity:", omega, "=", k, "^", cofactor, "multiplicative order:", omega.multiplicative_order())

Fx.<x> = PolynomialRing(F, "x")
poly = x^3 + x
for k in range(0, 10000):
    poly = poly + Fx(F(1))
    if poly.is_irreducible():
        break
print("polynomial:", poly)
print("")

# 3. extension field of degree 4 over base field with 40 bits
print("Field 3:")
for k in range(0, 10000):
    cofactor = 2^15 - k
    if cofactor % 3 == 0:
        continue
    p = cofactor * 2^25 + 1
    if is_prime(p):
        break

F = FiniteField(p)
print("p:", p,  "=", cofactor, "* 2^25 + 1. is prime?", is_prime(p), "bit width:", len(bin(p)[2:]))
print("base-2 log p =", log(1.0*p, 2.0))
print("cofactor:", cofactor, "=", factor(cofactor))
for k in range(2, 100000):
    omega = F(k)^cofactor
    if omega.multiplicative_order() == 2^25:
        break
print("primitive 2^25th root of unity:", omega, "=", k, "^", cofactor, "multiplicative order:", omega.multiplicative_order())

Fx.<x> = PolynomialRing(F, "x")
poly = x^4 + x
for k in range(0, 100000):
    poly = poly + Fx(F(1))
    if poly.is_irreducible():
        break
print("polynomial:", poly)
print("")

