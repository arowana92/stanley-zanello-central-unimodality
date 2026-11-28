"""Compare the twenty-node Fourier quadrature with exact partition rank sums."""

import argparse
from fractions import Fraction as Q
from math import comb, factorial, isqrt

from verify import ballot_ranks
from verify_point_window import evaluate, lean_value


EXPORT = """import CentralUnimodality.InterpolatedAmplitude
open CentralUnimodality.Witness
#eval IO.println (Lean.toJson (rationalNodes.map (fun q => (q.num,q.den)),
  (List.range 2).map fun δ => (List.range 20).map fun r =>
    ((pointMomentRow δ r).getD []).map fun q => (q.num,q.den))).compress
"""


def basis_polynomials(nodes):
    polynomials = []
    for a in nodes:
        p = [Q(1)]
        denominator = Q(1)
        for b in nodes:
            if a == b:
                continue
            p = [v - b * w for v, w in zip([0] + p, p + [0])]
            denominator *= a - b
        polynomials.append([c / denominator for c in p])
    return polynomials


def product_interval(a, b):
    ends = [x * y for x in a for y in b]
    return min(ends), max(ends)


def cosine_interval(x, terms):
    term = total = Q(1)
    for j in range(1, terms):
        term *= -x * x / ((2 * j - 1) * (2 * j))
        total += term
    error = abs(term) * x * x / ((2 * terms - 1) * (2 * terms))
    return total - error, total + error


def quadrature_interval(n, tables, basis, cosines):
    values = [evaluate(row, Q(1, n)) for row in tables]
    if any(not row for row in tables):
        raise ArithmeticError("A moment row is missing")
    # Wallis factor equals 4^n/(binom(2n,n) sqrt(2n)).
    unit = 2 ** 160
    root = isqrt(2 * n * unit ** 2)
    inv_survival = Q(4 ** n, comb(2 * n, n))
    wallis = (inv_survival * unit / (root + 1), inv_survival * unit / root)
    lower = upper = Q(0)
    for p, c in zip(basis, cosines):
        even = sum(p[j] * values[j] for j in range(0, 20, 2))
        odd = sum(p[j] * values[j] for j in range(1, 20, 2))
        weights = sorted(even + odd * w for w in wallis)
        lo, hi = product_interval(weights, c)
        lower += lo
        upper += hi
    return lower, upper


def rank_interval(length, ranks, frequency, terms=60):
    n = (length + 1) // 2
    denominator = 4 * (2 * n) ** 3
    powers = [0] * (terms + 1)
    for k, count in enumerate(reversed(ranks)):
        square = (2 * k + length + 1 + (length + 1) // 2) ** 2
        term = count
        for j in range(terms + 1):
            powers[j] += term
            term *= square
    mass = sum(ranks)
    z = Q(-frequency ** 2, denominator)
    total = sum(Q(powers[j], mass * factorial(2*j)) * z ** j for j in range(terms))
    error = abs(Q(powers[terms], mass * factorial(2*terms)) * z ** terms)
    return total - error, total + error


def check(lake, sizes, frequency):
    node_data, tables = lean_value(lake, EXPORT)
    nodes = [Q(*a) for a in node_data]
    if len(set(nodes)) != 20 or len(nodes) != 20:
        raise ArithmeticError("Twenty distinct interpolation sites are required")
    tables = [[[Q(*c) for c in p] for p in t] for t in tables]
    if len(tables) != 2 or any(len(t) != 20 for t in tables):
        raise ArithmeticError("Missing a parity or a moment order")
    basis = basis_polynomials(nodes)
    cosines = [cosine_interval(frequency * a, 72) for a in nodes]
    cases = 0
    worst = Q(0)
    certified = Q(frequency ** 20, factorial(20) * 10 ** 9)
    for length, ranks in ballot_ranks(max(sizes)):
        rows, parity = divmod(length, 2)
        if rows not in sizes or rows + parity < 96:
            continue
        lo, hi = quadrature_interval(rows + parity, tables[parity], basis, cosines)
        ref_lo, ref_hi = rank_interval(length, ranks, frequency)
        error = max(abs(lo - ref_hi), abs(hi - ref_lo))
        if error > certified:
            raise ArithmeticError(f"Quadrature comparison failed at length {length}")
        worst = max(worst, error)
        cases += 1
    if not cases:
        raise ValueError("No selected shapes satisfy the theorem's half-length cutoff")
    print(f"Checked {cases} shapes at scaled frequency {frequency}; "
          f"largest enclosed error {float(worst):.3g} (uniform bound {float(certified):.3g}).")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--rows", type=int, nargs="+", default=[95, 96, 196])
    parser.add_argument("--frequency", type=int, default=12)
    args = parser.parse_args()
    if any(n < 1 for n in args.rows) or not 1 <= args.frequency <= 12:
        parser.error("Use positive row sizes and an integer frequency between 1 and 12")
    check(args.lake, set(args.rows), args.frequency)
