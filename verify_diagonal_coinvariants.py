"""Compare rational alternating diagonal coinvariant dimensions with enumerated Dyck paths."""

from itertools import product

from verify_trapezoids import trapezoid
from verify_type_b_transfer import alternating_character


def check(n):
    # The invariant elementary symmetric functions give x_i^n = y_i^n = 0
    # in the quotient. The remaining mixed power sums generate its relations.
    cells = list(product(range(n), repeat=2))
    shifts = [(a, b) for a, b in cells if a+b > 0]
    dimensions = alternating_character(n, n, cells, shifts)
    enumerated = trapezoid(n, 0)
    if dimensions != enumerated:
        for degree in sorted(dimensions.keys() | enumerated.keys()):
            if dimensions[degree] != enumerated[degree]:
                raise ArithmeticError(f"n={n}, bidegree {degree}: quotient {dimensions[degree]}, "
                                      f"Dyck count {enumerated[degree]}")
    print(f"n={n}  dimension={sum(dimensions.values())}  "
          f"nonzero_bidegrees={len(dimensions)}  all bidegrees verified")


if __name__ == "__main__":
    for n in range(6):
        check(n)
