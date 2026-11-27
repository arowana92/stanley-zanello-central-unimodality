"""Check the trapezoidal q,t refinement of the two staircase corank rows."""

from collections import Counter
from itertools import combinations
from math import comb, isqrt

from verify import ballot_ranks, direct_ranks


def trapezoid(downs, endpoint):
    """Enumerate the up-step heights in the reversed walk and track dinv."""
    counts = Counter()
    used = [0] * (endpoint + downs + 1)

    def visit(left, bound, area, dinv):
        if not left:
            counts[area, dinv] += 1
            return
        for h in range(bound + 1):
            extra = used[h] + used[h+1] + max(0, endpoint-h)
            used[h] += 1
            visit(left-1, h+1, area+h, dinv+extra)
            used[h] -= 1

    visit(downs, endpoint, 0, 0)
    return counts


def support_cost(size, p, q, excluded=0):
    """Sum the size lowest weights p*i+q*j with i+j >= excluded."""
    # In column i only the size lowest eligible cells can be needed. After
    # column excluded+size-1 there are size strictly cheaper cells at height 0.
    costs = [p*i + q*j
             for i in range(excluded + size)
             for j in range(max(0, excluded-i), max(0, excluded-i) + size)]
    return sum(sorted(costs)[:size])


def frontier(poly):
    """Coordinatewise minimal bidegrees in increasing first coordinate."""
    result = []
    smallest = None
    for a, b in sorted(poly):
        if smallest is None or b < smallest:
            result.append((a, b))
            smallest = b
    return result


def lowest_diagonal(size):
    """Form the lowest homogeneous component by choosing sites on a diagonal."""
    h = (isqrt(8 * size + 1) - 1) // 2
    r = size - h * (h + 1) // 2
    base = comb(h + 1, 3)
    counts = Counter()
    for sites in combinations(range(h + 1), r):
        weight = sum(sites)
        counts[base + weight, base + h * r - weight] += 1
    return counts


def check(max_n=10):
    layers = schur_tests = 0
    for m, ranks in ballot_ranks(max_n):
        n, parity = divmod(m, 2)
        ell = n + parity
        poly = Counter()
        ordinary = trapezoid(ell, 0)
        boundary = frontier(ordinary)
        for u in range(n + 1):
            e = 2*u + parity
            d = n-u
            offset = u*(u+parity)
            shift = u*(u+1)//2
            layer = trapezoid(d, e)
            assert sum(layer.values()) == comb(m, d) - (comb(m, d-1) if d else 0)
            assert all(layer[b, a] == c for (a, b), c in layer.items())
            top = e * d + comb(d, 2)
            assert max(a + b for a, b in layer) == top
            assert all(layer[a, top - a] == 1 for a in range(top + 1))
            for p, q in ((1, 1), (2, 1), (1, 3), (5, 7)):
                assert min(p*a + q*b for a, b in layer) == support_cost(d, p, q, e)
            for (a, b), c in layer.items():
                assert any(i+shift <= a+offset and j+shift <= b+offset for i, j in boundary)
                assert 9*(2*(a+offset)+ell)*(2*(b+offset)+ell) >= 8*ell**3
                if a <= b:
                    # Coefficients in the two-variable Schur expansion.
                    assert c >= layer[a-1, b+1]
                    schur_tests += 1
                poly[a+offset, b+offset] += c
            # Also check transitions whose ending coefficient is zero.
            for a, b in layer:
                if a+1 <= b-1:
                    assert layer[a+1, b-1] >= layer[a, b]
            layers += 1
        assert frontier(poly) == boundary
        assert all(poly[key] == ordinary[key] for key in boundary)
        diagonal = lowest_diagonal(ell)
        degree = min(a + b for a, b in poly)
        assert {key: c for key, c in poly.items() if sum(key) == degree} == diagonal
        for a in range(degree + 2):
            key = (a, degree + 1 - a)
            assert poly[key] == ordinary[key]
        coranks = [0] * len(ranks)
        for (a, b), c in poly.items():
            coranks[a] += c
        assert coranks == ranks[::-1] == direct_ranks(range(m-1, 0, -2))[::-1]
    print(f"Both families through n={max_n}: {layers} symmetric endpoint layers, "
          f"four weighted minimum checks per layer, {schur_tests} occupied "
          f"lower-half Schur coefficient checks. Frontiers and direct ranks agree.")


if __name__ == "__main__":
    check()
