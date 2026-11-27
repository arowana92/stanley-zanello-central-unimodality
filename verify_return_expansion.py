"""Exact checks of the signed last-return identity and its two leading moment terms."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb, factorial

from verify import ballot_ranks, direct_ranks


def signed_areas(length, ranks):
    """Counts by twice the signed area, obtained from the two staircase branches."""
    if length == 0:
        return Counter({0: 1})
    word_length = length - 1
    shift = length + (word_length + 1) // 2
    area_counts = Counter()
    for k, count in enumerate(reversed(ranks)):
        area = 2 * k + shift
        area_counts[area] = area_counts[-area] = count
    return area_counts


def check_last_return(rows, max_length):
    """Enumerate free sign words and compare their entire area distribution."""
    bridges = []
    for length in range(max_length + 1):
        free = Counter()
        bridge = Counter()
        for steps in product((-1, 1), repeat=length):
            height = twice_area = 0
            for step in steps:
                height += step
                twice_area += height
            free[twice_area] += 1
            if height == 0:
                bridge[twice_area] += 1
        if length % 2 == 0:
            bridges.append(bridge)
        by_last_return = Counter()
        for i, prefix in enumerate(bridges):
            suffix_length = length - 2 * i
            strict = signed_areas(suffix_length, rows[suffix_length - 1])
            for a, prefix_count in prefix.items():
                for b, suffix_count in strict.items():
                    by_last_return[a + b] += prefix_count * suffix_count
        if free != by_last_return:
            raise ArithmeticError(f"last-return area counts disagree at length {length}")


def continuum_coefficients(order):
    """Even cosine coefficients from the free, bridge and first-return identities."""
    half_rising = [Fraction(1)]
    for j in range(3 * order):
        half_rising.append(half_rising[-1] * Fraction(2 * j + 1, 2))
    bridge = [Fraction((-1)**i, 96**i * factorial(i)) for i in range(order + 1)]
    bridge_laplace = [value * half_rising[3 * i] for i, value in enumerate(bridge)]
    meander = [Fraction(1)]
    excursion = [Fraction(1)]
    reciprocal = [Fraction(1)]
    for k in range(1, order + 1):
        degree = 3 * k
        free = Fraction((-1)**k, 24**k * factorial(k))
        known = sum(bridge_laplace[i] * meander[k-i] * half_rising[3*(k-i)]
                    for i in range(1, k + 1))
        meander.append((free * factorial(degree) - known) / half_rising[degree])
        reciprocal.append(-sum(bridge_laplace[i] * reciprocal[k-i]
                               for i in range(1, k + 1)))
        excursion.append(-2 * reciprocal[k] / half_rising[degree-1])
    return meander, excursion


def normalized_moment(length, ranks, k):
    """Coefficient of xi^(2k) before division by N^(3k)."""
    counts = signed_areas(length, ranks)
    numerator = sum(a**(2*k) * count for a, count in counts.items())
    return Fraction((-1)**k * numerator, sum(counts.values()) * 32**k * factorial(2*k))


def leading_terms(values, degree):
    """Recover the top two monomial coefficients from exact forward differences."""
    for _ in range(degree - 1):
        values = [b - a for a, b in zip(values, values[1:])]
    differences = [b - a for a, b in zip(values, values[1:])]
    if len(set(differences)) != 1:
        raise ArithmeticError(f"moment exceeds predicted degree {degree}")
    leading = differences[0] / factorial(degree)
    return leading, values[0] / factorial(degree - 1) - comb(degree, 2) * leading


def check(order=10, direct_n=8):
    max_index = 3 * order + 3
    # Use the empty polynomial row for the length-zero strict walk.
    rows = {-1: [1], 0: [1], 1: [1], **dict(ballot_ranks(max_index))}
    for m in range(2, 2 * direct_n + 2):
        if direct_ranks(range(m - 1, 0, -2)) != rows[m]:
            raise ArithmeticError(f"direct strict partitions disagree at length {m}")
    check_last_return(rows, 2 * direct_n + 2)
    print(f"Direct partition counts agree through n={direct_n}. "
          f"Last-return coefficients agree through strict length {2*direct_n+2}.")

    meander, excursion = continuum_coefficients(order)
    for k in range(1, order + 1):
        degree = 3 * k
        for parity in (0, 1):
            values = [normalized_moment(2*j + parity, rows[2*j + parity - 1], k)
                      for j in range(max_index + 1)]
            correction = ((Fraction(1, 12) + Fraction(parity, 2)) * degree * meander[k]
                          - Fraction(degree * (degree-1), 30) * meander[k]
                          + (Fraction(parity, 4) - Fraction(3, 40)) * (excursion[k]-meander[k]))
            if leading_terms(values, degree) != (meander[k], correction):
                raise ArithmeticError(f"moment correction disagrees at {k=}, {parity=}")
    print(f"Both leading coefficients of every even moment through order {2*order} "
          f"agree for both parities. Used N=0..{max_index} with exact rational arithmetic.")


if __name__ == "__main__":
    check()
