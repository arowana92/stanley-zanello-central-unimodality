"""Check the exact meander-area moment formulas in finite-reduction.md."""

import argparse
from fractions import Fraction
from math import comb, factorial

from verify import ballot_ranks, direct_ranks


# Laurent polynomials in v = sqrt(1 - 4z), keyed by exponent.
ONE = {0: Fraction(1)}
HALF = Fraction(1, 2)


def collect(terms):
    result = {}
    for power, value in terms:
        result[power] = result.get(power, 0) + value
    return {power: value for power, value in result.items() if value}


def add(polynomials):
    return collect(term for polynomial in polynomials for term in polynomial.items())


def multiply(left, right):
    return collect((a + b, x * y) for a, x in left.items() for b, y in right.items())


def scale(poly, factor, shift=0):
    return {power + shift: factor * coeff for power, coeff in poly.items()}


def euler_derivative(poly, base):
    """Apply z*d/dz including the logarithmic derivative of the factored base."""
    terms = []
    for h, coeff in poly.items():
        terms.append((h, HALF * (h - 1) * coeff))
        if base == "dyck":
            terms.extend(((h - 1, HALF * coeff), (h - 2, -HALF * h * coeff)))
        else:  # Base 1/v for the type B series.
            terms.append((h - 2, HALF * (1 - h) * coeff))
    return collect(terms)


def shifted_rows(rows, order, dilation, base):
    """Coefficients in x after replacing z by exp(dilation*x)*z."""
    terms = [[] for _ in range(order + 1)]
    for i, poly in enumerate(rows):
        terms[i].append(poly)
        for j in range(1, order - i + 1):
            poly = scale(euler_derivative(poly, base), Fraction(dilation, j))
            terms[i + j].append(poly)
    return [add(row) for row in terms]


def moment_polynomials(order):
    dyck, type_b, odd = [ONE], [ONE], [ONE]
    branch = {0: HALF, 1: -HALF}  # z*C(z,1) = (1-v)/2.
    for r in range(1, order + 1):
        shifted = shifted_rows(dyck, r, 1, "dyck")
        known = add(multiply(poly, shifted[r - i]) for i, poly in enumerate(dyck))
        dyck.append(scale(multiply(branch, known), 1, shift=-1))

        shifted = shifted_rows(type_b, r, 2, "type B")
        # Coefficients of exp(x)*(C(z,exp(x))-1)/C(z,1).
        stripped = [branch] + dyck[1:]
        exponential = [add(scale(stripped[i], Fraction(1, factorial(j - i)))
                           for i in range(j + 1)) for j in range(r + 1)]
        known = add(multiply(poly, shifted[r - i]) for i, poly in enumerate(exponential))
        type_b.append(add((dyck[r], scale(known, 1, shift=-1))))

        shifted = shifted_rows(type_b, r, 1, "type B")
        odd.append(add(multiply(poly, shifted[r - i]) for i, poly in enumerate(dyck)))
    # Divide by the exact word count at coefficient extraction. For odd
    # lengths C(z,1)=(1-v)/(2z) and binom(2n+2,n+1)=2*binom(2n+1,n).
    return ([scale(poly, factorial(r), -1) for r, poly in enumerate(type_b)],
            [scale(multiply({0: 1, 1: -1}, poly), factorial(r), -1)
             for r, poly in enumerate(odd)])


def normalized_power_coefficient(h, n):
    """[z^n] (1-4z)^(h/2) divided by binom(2n,n)."""
    value = Fraction(1)
    for i in range(n):
        value *= Fraction(2 * i - h, 2 * i + 1)
    return value


def closed_variance(m):
    """Finite variance of the corank, as simplified in mode-bounds.md."""
    parity = m % 2
    ell = (m + parity) // 2
    central_ratio = Fraction(4 ** ell, comb(2 * ell, ell))
    if parity:
        correction = Fraction(44, 15) * ell ** 2 + Fraction(8, 5) * ell
    else:
        correction = Fraction(228, 5) * ell ** 2 + Fraction(344, 15) * ell + 4
    polynomial = Fraction(472, 15) * ell ** 3 + correction
    return (polynomial - ((3 * ell + 2 - 2 * parity) * central_ratio) ** 2) / 16


def check(order, max_n, direct_n):
    formulas = moment_polynomials(order)
    exponents = [{h for poly in family for h in poly} for family in formulas]
    for m, ranks in ballot_ranks(max_n):
        n, parity = divmod(m, 2)
        if n <= direct_n and direct_ranks(range(m - 1, 0, -2)) != ranks:
            raise ArithmeticError(f"partition enumeration disagrees at length {m}")
        coranks = ranks[::-1]
        count = sum(coranks)
        powers = {h: normalized_power_coefficient(h, n + parity)
                  for h in exponents[parity]}
        moments = []
        for r, poly in enumerate(formulas[parity]):
            moment = sum(value * powers[h] for h, value in poly.items())
            expected = sum(k**r * b for k, b in enumerate(coranks))
            if moment * count != expected:
                raise ArithmeticError(f"moment {r} disagrees at length {m}")
            moments.append(moment)
        if order >= 2 and moments[2] - moments[1] ** 2 != closed_variance(m):
            raise ArithmeticError(f"closed variance disagrees at length {m}")
    print(f"Exact moments of orders 0 through {order} agree for both families "
          f"through n={max_n}. Direct partition counts agree through n={direct_n}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=8)
    parser.add_argument("--max-n", type=int, default=32)
    parser.add_argument("--direct-n", type=int, default=10)
    args = parser.parse_args()
    if args.order < 0 or not 1 <= args.direct_n <= args.max_n:
        parser.error("require a nonnegative order and 1 <= direct-n <= max-n")
    check(args.order, args.max_n, args.direct_n)
