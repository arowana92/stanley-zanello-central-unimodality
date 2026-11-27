"""Check the boundary characters of the central staircase q,t refinements."""

from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
from math import comb, isqrt

from verify_trapezoids import trapezoid


def shell(size):
    return (isqrt(8*size+1)-1)//2


@lru_cache(maxsize=None)
def rectangle(rows, columns):
    """Gaussian binomial from removing a full row or shortening every row."""
    if rows == 0 or columns == 0:
        return (1,)
    coeffs = [0]*(1+rows*columns)
    for j, count in enumerate(rectangle(rows, columns-1)):
        coeffs[j] += count
    for j, count in enumerate(rectangle(rows-1, columns)):
        coeffs[j+columns] += count
    return tuple(coeffs)


def profile_polynomial(d, e):
    """Sum the insertion formula over unordered height multisets."""
    result = Counter()
    for word in combinations_with_replacement(range(e+d), d):
        counts = Counter(word)
        poly = [1]
        offset = sum(max(0, e-i)*n + comb(n, 2) for i, n in counts.items())
        for i, n in counts.items():
            if i == 0:
                continue
            width = counts[i-1]-1+int(i <= e)
            if width < 0:
                poly = []
                break
            product = [0]*(len(poly)+n*width)
            for j, c in enumerate(rectangle(n, width)):
                for k, a in enumerate(poly):
                    product[j+k] += c*a
            poly = product
        for j, c in enumerate(poly):
            result[sum(word), offset+j] += c
    return result


def lowest_face(d, e, p, v):
    """Choose all cheap sites and a subset of the tied sites at the cutoff."""
    if d == 0:
        return Counter({(0, 0): 1})
    sites = [(i, j) for i in range(e+d)
             for j in range(max(0, e-i), max(0, e-i)+d)]
    costs = [p*i+v*j for i, j in sites]
    cutoff = sorted(costs)[d-1]
    cheap = [site for site, value in zip(sites, costs) if value < cutoff]
    tied = [site for site, value in zip(sites, costs) if value == cutoff]
    x = sum(i for i, _ in cheap)
    y = sum(j for _, j in cheap)
    return Counter((x+sum(i for i, _ in subset), y+sum(j for _, j in subset))
                   for subset in combinations(tied, d-len(cheap)))


def quotient_character(d, e):
    """Torus weights of the quotient by the product of r binary determinants."""
    r = d-1
    target = Counter(sum(u)+j for u in combinations(range(e+1), r)
                     for j in range(e+2))
    source = Counter(r+sum(u)+j for u in combinations(range(e), r)
                     for j in range(e+2-r))
    target.subtract(source)
    assert min(target.values()) >= 0
    return +target


@lru_cache(maxsize=32)
def ordinary(size):
    return trapezoid(size, 0)


def check(max_n=10):
    layers = faces = comparisons = stable_degrees = sparse = profiles = 0
    for delta in (0, 1):
        for n in range(1, max_n+1):
            m = 2*n+delta
            ell = n+delta
            whole = Counter()
            expected = Counter()
            predicted_degrees = set()
            min_degree = min(sum(key) for key in ordinary(ell))
            whole_limit = min_degree+shell(ell)-delta
            for u in range(n+1):
                d, e = n-u, 2*u+delta
                area_shift = u*(u+delta)
                shift = comb(e+1, 3)
                size = d+comb(e+1, 2)
                poly = trapezoid(d, e)
                layers += 1
                if d <= 6 and e <= 5:
                    assert poly == profile_polynomial(d, e)
                    profiles += 1
                for p, v in ((1, 1), (2, 1), (1, 3), (5, 7)):
                    cost = min(p*a+v*b for a, b in poly)
                    face = {key: c for key, c in poly.items() if p*key[0]+v*key[1] == cost}
                    assert face == lowest_face(d, e, p, v)
                    faces += 1
                bottom = min(sum(key) for key in poly)
                if 1 <= d <= e+1:
                    second = {a: c for (a, b), c in poly.items() if a+b == e*d+1}
                    assert second == quotient_character(d, e)
                    sparse += 1
                if size <= 13:
                    cat = ordinary(size)
                    for (a, b), c in poly.items():
                        assert c <= cat[a+shift, b+shift]
                    last = bottom+shell(size)-e
                    actual = {(a+shift, b+shift): c for (a, b), c in poly.items() if a+b <= last}
                    reference = {key: c for key, c in cat.items() if sum(key) <= last+2*shift}
                    assert actual == reference
                    comparisons += 1
                    stable_degrees += last-bottom+1
                if 2*area_shift+bottom <= whole_limit:
                    # Only sizes small enough for direct Catalan enumeration occur here.
                    assert size <= 15, (m, u, size)
                    for (a, b), count in ordinary(size).items():
                        x, y = a+area_shift-shift, b+area_shift-shift
                        if x+y <= whole_limit:
                            expected[x, y] += count
                            predicted_degrees.add(x+y)
                for (a, b), count in poly.items():
                    if a+b+2*area_shift <= whole_limit:
                        whole[a+area_shift, b+area_shift] += count
            assert whole == expected
            for degree in predicted_degrees:
                for a in range(1, degree//2+1):
                    assert whole[a, degree-a] >= whole[a-1, degree-a+1]
    # At (d,e)=(3,2) the stable range ends at degree 7.
    assert trapezoid(3, 2)[2, 6] == 1 and ordinary(6)[3, 7] == 2
    print(f"Both families through n={max_n}: {layers} endpoint classes, {faces} exposed faces, "
          f"{comparisons} whole-polynomial upper bounds, {stable_degrees} stable degrees, "
          f"{sparse} quotient characters, and {profiles} insertion products. Full staircase bands agree.")


if __name__ == "__main__":
    check()
