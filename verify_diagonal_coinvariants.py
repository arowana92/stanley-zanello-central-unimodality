"""Compare rational alternating diagonal coinvariant dimensions with enumerated Dyck paths."""

from argparse import ArgumentParser
from collections import defaultdict
from hashlib import shake_256
from itertools import groupby, product
from math import comb

from verify_trapezoids import trapezoid
from verify_type_b_transfer import alternating_character, alternating_relations, insert_relation


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


def dyck_determinants(n):
    """Jiang's ordinary Dyck candidates, up to reordering their columns."""
    by_degree = defaultdict(list)

    def visit(area):
        if len(area) == n:
            dinv = tuple(sum(b == a or b == a-1 for b in area[i+1:])
                         for i, a in enumerate(area))
            points = tuple(sorted(zip(dinv, area)))
            assert len(set(points)) == n
            by_degree[sum(dinv), sum(area)].append((points, area))
            return
        for a in range(area[-1]+2 if area else 1):
            visit(area+(a,))

    visit(())
    assert sum(map(len, by_degree.values())) == comb(2*n, n)//(n+1)
    return by_degree


def low_degree_alternants(n, degree_limit):
    """Enumerate exponent sets by increasing cell degree with an exact cutoff."""
    cells = sorted(product(range(n), repeat=2), key=lambda p: (sum(p), p))
    prefix = [0]
    for cell in cells:
        prefix.append(prefix[-1]+sum(cell))
    by_degree = defaultdict(list)

    def visit(start, left, x, y, points):
        if left == 0:
            by_degree[x, y].append(tuple(sorted(points)))
            return
        for k in range(start, len(cells)-left+1):
            # Sum of the cheapest left cells at or after k.
            if x+y+prefix[k+left]-prefix[k] > degree_limit:
                break
            a, b = cells[k]
            visit(k+1, left-1, x+a, y+b, points+(cells[k],))

    visit(0, n, 0, 0, ())
    return by_degree


def check_determinants(n):
    candidates = dyck_determinants(n)
    ambient = low_degree_alternants(n, max(map(sum, candidates)))
    for degree, paths in candidates.items():
        x, y = degree
        shifts = [(a, b) for a in range(min(x+1, n)) for b in range(min(y+1, n)) if a+b]
        index, pivots = alternating_relations(n, n, ambient, degree, shifts)
        assert len(index)-len(pivots) == len(paths), (n, degree)
        for points, area in paths:
            before = len(pivots)
            insert_relation({index[points]: 1}, pivots)
            if len(pivots) == before:
                raise ArithmeticError(f"Dependent quotient class at n={n}, area word {area}")
        assert len(pivots) == len(index)
    print(f"n={n}  checked {sum(map(len, candidates.values()))} Dyck determinants "
          f"modulo all invariant relations in their bidegrees", flush=True)


PRIME = 65537


def determinant_mod(rows):
    """Determinant over the prime field, by elimination on a fresh matrix."""
    value = 1
    n = len(rows)
    for k in range(n):
        pivot = next((i for i in range(k, n) if rows[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            rows[k], rows[pivot] = rows[pivot], rows[k]
            value = -value
        row = rows[k]
        value = value*row[k] % PRIME
        inverse = pow(row[k], -1, PRIME)
        for i in range(k+1, n):
            if rows[i][k]:
                scale = rows[i][k]*inverse % PRIME
                for j in range(k+1, n):
                    rows[i][j] = (rows[i][j]-scale*row[j]) % PRIME
    return value


def insert_evaluation(row, basis):
    for j in range(len(row)):
        if row[j]:
            if j not in basis:
                inv = pow(row[j], -1, PRIME)
                basis[j] = [entry*inv % PRIME for entry in row]
                return
            scale = row[j]
            for k in range(j, len(row)):
                row[k] = (row[k]-scale*basis[j][k]) % PRIME


def curve_columns(n, coeff):
    """Coefficient vectors of t^(d+a) U(t)^a modulo t^n and PRIME."""
    powers = [[1]+[0]*(n-1)]
    for a in range(1, n):
        powers.append([sum(coeff[k]*powers[a-1][j-k] for k in range(j+1)) % PRIME
                       for j in range(n)])
    return {(d,a): [0 if i < d+a else powers[a][i-d-a] for i in range(n)]
            for d in range(n) for a in range(n)}


def coefficient_from_samples(values, order):
    """Use finite differences and the Newton expansion on 0,...,degree."""
    binomial = [1]
    coefficient = 0
    for j in range(len(values)):
        if order < len(binomial):
            coefficient = (coefficient+binomial[order]*values[0]) % PRIME
        values = [(b-a) % PRIME for a, b in zip(values, values[1:])]
        # binom(X,j+1) = (X-j)*binom(X,j)/(j+1).
        shifted = [0]+binomial
        inv = pow(j+1, -1, PRIME)
        binomial = [(a-j*b)*inv % PRIME for a, b in zip(shifted, binomial+[0])]
    return coefficient


def check_reduction(n, paths):
    """Interpolate the lowest coefficient for U=1+epsilon*t*V in two ways."""
    if not n:
        return
    bound = comb(n, 2)
    V = [1]+[17*i**3-3*i for i in range(1, n)]
    final_columns = curve_columns(n, V)
    samples = [curve_columns(n, [1]+[e*v for v in V[:-1]]) for e in range(bound+1)]
    for group in paths.values():
        for points, _ in group:
            rows = sorted(points, key=lambda p: (sum(p), p[1]))
            blocks = [(s, list(block)) for s, block in groupby(rows, key=sum)]
            if len(blocks) == n:
                continue
            reduced = []
            factor = 1
            power = 0
            for s, block in blocks:
                g = len(block)
                power += comb(g, 2)
                factor *= determinant_mod([[comb(a, h) for h in range(g)] for _, a in block])
                reduced.extend((s, h) for h in range(g))  # t^(s+h) V(t)^h
            assert all(s <= i for i, s in enumerate(sorted(map(sum, reduced))))
            assert factor % PRIME
            expected = factor*determinant_mod([final_columns[p].copy() for p in reduced]) % PRIME
            degree = bound-sum(map(sum, rows))
            values = [determinant_mod([cols[p].copy() for p in rows]) for cols in samples[:degree+1]]
            assert coefficient_from_samples(values, power) == expected
            assert all(coefficient_from_samples(values, k) == 0 for k in range(power))


def check_top_degrees(n, paths):
    """Check the two uniform nonvanishing formulas on every path in those degrees."""
    total = comb(n, 2)
    for (x, y), group in paths.items():
        deficit = total-x-y
        if deficit not in (0, 1):
            continue
        for points, _ in group:
            orders = [d+a for d, a in points]
            if deficit == 0:
                assert sorted(orders) == list(range(n))
                matrix = [[int(k == s) for k in range(n)] for s in orders]
                magnitude = 1
            else:
                doubled = next(s for s in orders if orders.count(s) == 2)
                assert sorted(orders) == sorted(doubled if k == doubled+1 else k for k in range(n))
                a1, a2 = [a for d, a in points if d+a == doubled]
                magnitude = abs(a1-a2)
                assert magnitude > 0
                matrix = [[comb(a, k-d-a) if k >= d+a else 0 for k in range(n)] for d, a in points]
            assert determinant_mod(matrix) in (magnitude % PRIME, -magnitude % PRIME)


def check_curves(n):
    """Full column rank over F_p certifies rational independence in the quotient."""
    paths = dyck_determinants(n)
    check_top_degrees(n, paths)
    pending = {degree: {} for degree in paths}
    for sample in range(max(map(len, paths.values()))+6):
        # A reproducible list of integer curves y=t*U(t), U(0)=1.
        coeff = [1]
        for k in range(1, n):
            raw = shake_256(f"{n}:{sample}:{k}".encode()).digest(4)
            coeff.append(int.from_bytes(raw, "big") % PRIME)
        columns = curve_columns(n, coeff)
        for degree, basis in list(pending.items()):
            values = [determinant_mod([columns[p].copy() for p in points])
                      for points, _ in paths[degree]]
            insert_evaluation(values, basis)
            if len(basis) == len(values):
                del pending[degree]
        if not pending:
            print(f"n={n}  curve minor has full rank in all {len(paths)} bidegrees "
                  f"after {sample+1} evaluations", flush=True)
            return
    raise ArithmeticError(f"Curve evaluations left unresolved bidegrees at n={n}: {list(pending)}")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--basis-through", type=int, default=6,
                        help="largest semilength for exact quotient basis checks (default 6)")
    parser.add_argument("--curves-through", type=int, default=10,
                        help="largest semilength for exact minor certificates (default 10)")
    args = parser.parse_args()
    for n in range(6):
        check(n)
    for n in range(args.basis_through+1):
        check_determinants(n)
        check_reduction(n, dyck_determinants(n))
    for n in range(args.curves_through+1):
        check_curves(n)
