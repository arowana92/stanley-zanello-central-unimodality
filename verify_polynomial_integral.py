"""Certify the compact spatial signs by integrating a Taylor polynomial exactly."""

from fractions import Fraction
from math import factorial, floor, lcm

from verify_gamma_polynomials import monomial_coefficients, read_rows
from verify_polynomial_peak import omitted_lattice_tail


ORDER = 1024
SCALE = 2**120
WINDOWS = ((1, 1359, 3390, 1, Fraction(1, 8)),
           (2, 3330, 4040, -1, Fraction(128)),
           (1, 3980, 6310, -1, Fraction(2)))


def moment_polynomial(power, r, degree):
    """Integer numerator row for the trig Taylor integral and its denominator."""
    # Put w=8t. Its uniform upper bound in the variable z=w^2/256 is 1/4.
    last = len(power)-1
    weighted = [c << (2*(last-i)) for i, c in enumerate(power)]
    top = 3*(degree+r+1) + 2*last
    common = lcm(*range(1, top+1))
    quotients = [0] + [common//i for i in range(1, top+1)]
    den = common*factorial(degree)*SCALE*4**last
    coeffs = []
    for j in range(degree+1):
        if (j+r) % 2:
            coeffs.append(0)
            continue
        k = 3*(j+r+1)
        s = sum(a*quotients[k+2*i] for i, a in enumerate(weighted))
        sign = (-1)**((j+r)//2)
        coeffs.append(sign*3*512**(j+r+1)*(factorial(degree)//factorial(j))*s)
    return coeffs, den


def positive_on(coeffs, den, lo, hi, sign, margin, q=10000):
    """Check sign*P(x)/den > margin throughout the closed interval [lo/q, hi/q]."""
    # Shift by lo, then transform from y to t/(1+t).
    row = [sign*margin.denominator*c for c in coeffs]
    row[0] -= margin.numerator*den
    d = len(row)-1
    shifted = [row[-1]]
    for j in range(d-1, -1, -1):
        following = [lo*c for c in shifted]+[0]
        for i, c in enumerate(shifted):
            following[i+1] += (hi-lo)*c
        following[0] += row[j]*q**(d-j)
        shifted = following
    # Homogenize y=t/(1+t) by multiplying the j-th term by (1+t)^(d-j).
    transform = [0]*(d+1)
    for j, c in enumerate(shifted):
        choose = 1
        for i in range(d-j+1):
            transform[i+j] += c*choose
            choose = choose*(d-j-i)//(i+1)
    if min(transform) <= 0:
        raise ArithmeticError(f"insufficient polynomial margin on {lo}..{hi}")


def check_moments():
    for r in (1, 2):
        coeffs, den = moment_polynomial([2*SCALE, SCALE], r, 7)
        for j, a in enumerate(coeffs):
            d = j+r+1
            factor = 0 if (j+r) % 2 else (-1)**((j+r)//2)
            integral = 512**d*(Fraction(2, d) + Fraction(3, 4*(3*d+2)))
            if Fraction(a, den) != factor*integral/factorial(j):
                raise ArithmeticError("monomial integration check failed")


def main():
    check_moments()
    row = read_rows()["trial"]
    power = [int(c) for c in monomial_coefficients(row, 1)]
    F = Fraction(sum(map(abs, row)), SCALE)
    tail = Fraction(1, 10**14)
    endpoints = [64, 88, 112, 160, 184, 208, 232, 244, 250, 256]
    for lo, hi in zip(endpoints, endpoints[1:]):
        for sign in (1, -1):
            positive_on(power, SCALE, lo, hi, sign, -tail, q=256)
    outside = omitted_lattice_tail()
    for r in (1, 2):
        coeffs, den = moment_polynomial(power, r, ORDER)
        trunc = F*Fraction(512**(r+1), r+1)*Fraction(512*631, 1000)**(ORDER+1)/factorial(ORDER+1)
        omitted = tail*Fraction(4096**(r+1)-512**(r+1), r+1)
        if trunc + omitted >= Fraction(1, 100):
            raise ArithmeticError("insufficient integral tail bound")
        for order, lo, hi, sign, margin in WINDOWS:
            if order == r:
                positive_on(coeffs, den, lo, hi, sign, margin)
                allowance = (trunc + omitted + outside
                             + Fraction(4096**(r+1), (r+1)*10**10))
                if margin <= allowance:
                    raise ArithmeticError("insufficient full-period sign margin")
                lower = Fraction(floor(10**6*(margin-allowance)), 10**6)
                print(f"order {r}, {lo}/10000..{hi}/10000: Taylor margin {margin}, "
                      f"full-period margin > {float(lower):.6f}", flush=True)


if __name__ == "__main__":
    main()
