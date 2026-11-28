"""Cross-check the Lean Fourier moment polynomials against exact staircase ranks."""

import argparse
import json
import subprocess
from fractions import Fraction
from pathlib import Path

from verify import ballot_ranks, direct_ranks


EXPORT = """import CentralUnimodality.PointFrequencyWindow
open CentralUnimodality.Witness
#eval IO.println (Lean.toJson ((List.range 2).map fun δ =>
  (List.range 11).map fun j => (pointCoefficients δ j).map fun q => (q.num,q.den))).compress
"""


def lean_value(lake, source):
    run = subprocess.run([lake, "env", "lean", "--stdin"], input=source,
                         text=True, capture_output=True, cwd=Path(__file__).resolve().parent)
    if run.returncode:
        raise RuntimeError(run.stdout + run.stderr)
    return json.loads(run.stdout)


def read_coefficients(lake):
    tables = lean_value(lake, EXPORT)
    if len(tables) != 2 or any(len(family) != 11 or not all(family) for family in tables):
        raise ValueError("Expected both parities and the eleven even orders from 0 through 20")
    return [[[Fraction(a, b) for a, b in row] for row in family] for family in tables]


def evaluate(coefficients, x):
    value = Fraction(0)
    for coefficient in reversed(coefficients):
        value = coefficient + x * value
    return value


def check(lake, max_n, direct_n):
    tables = read_coefficients(lake)
    cases = 0
    for m, ranks in ballot_ranks(max_n):
        n, parity = divmod(m, 2)
        if n <= direct_n:
            if ranks != direct_ranks(range(m - 1, 0, -2)):
                raise ArithmeticError(f"Direct partition enumeration disagrees at length {m}")
        elif n != max_n:
            continue
        half_length = n + parity
        count = sum(ranks)
        totals = [0] * 11
        for corank, multiplicity in enumerate(reversed(ranks)):
            squared_area = (2 * corank + m + 1 + (m + 1) // 2) ** 2
            term = multiplicity
            for j in range(11):
                totals[j] += term
                term *= squared_area
        for j, coefficients in enumerate(tables[parity]):
            measured = Fraction(totals[j], count * (4 * (2 * half_length) ** 3) ** j)
            predicted = evaluate(coefficients, Fraction(1, half_length))
            if measured != predicted:
                raise ArithmeticError(f"Moment {2*j} disagrees for length {m}")
        if half_length >= 196 and measured > Fraction(21, 200):
            raise ArithmeticError(f"Twentieth moment exceeds the certified bound at length {m}")
        cases += 1
    print(f"Exact moments 0, 2, …, 20 agree in {cases} shapes; "
          f"direct enumeration through {min(max_n, direct_n)} rows.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake executable for the pinned Lean toolchain")
    parser.add_argument("--max-n", type=int, default=196)
    parser.add_argument("--direct-n", type=int, default=12)
    args = parser.parse_args()
    if args.max_n < 1 or args.direct_n < 0:
        parser.error("Use a positive maximum size and a nonnegative enumeration cutoff")
    check(args.lake, args.max_n, args.direct_n)
