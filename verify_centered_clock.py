"""Exact excursion coupling and constants for centered-clock.md."""

from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations, product
from math import comb, isqrt

from verify import direct_ranks
from verify_rising import PI_HI, PI_LO, decay, exp_small_upper, sqrt_hi, sqrt_lo


@lru_cache(maxsize=None)
def trees(size):
    if size == 0:
        return (None,)
    return tuple((left, right) for i in range(size)
                 for left in trees(i) for right in trees(size - 1 - i))


def grow(tree):
    yield (tree, None)
    yield (None, tree)
    if tree is not None:
        left, right = tree
        for child in grow(left):
            yield (child, right)
        for child in grow(right):
            yield (left, child)


def word(tree):
    if tree is None:
        return ()
    left, right = tree
    return (1,) + word(left) + (-1,) + word(right)


def areas(steps):
    h = left = corank = 0
    for step in steps:
        left += h
        h += step
        if h < 0:
            return None
        corank += h // 2
    return left, corank, h


def check_excursions():
    for size in range(8):
        multiplicities = Counter()
        total = 0
        for tree in trees(size):
            old = areas(word(tree))[0]
            total += old
            for new_tree in grow(tree):
                assert areas(word(new_tree))[0] >= old
                multiplicities[new_tree] += 1
        assert multiplicities == Counter({tree: size + 2 for tree in trees(size + 1)})
        catalan = comb(2*size, size) // (size + 1)
        assert total == 4**size - (2*size + 1)*catalan


def check_parity_and_permutations():
    for m in range(2, 16):
        shape = list(range(m-1, 0, -2))
        counts = [0] * (sum(shape) + 1)
        for signs in product((-1, 1), repeat=m):
            values = areas(signs)
            if values is not None:
                left, corank, end = values
                assert 2*corank == left + end - (m+1)//2
                counts[corank] += 1
        assert counts == direct_ranks(shape)[::-1]
    for weights in ((1, 1, 1), (3, -2, 1, 3)):
        size = len(weights)
        heights = tuple(range(size))
        values = [sum(h*y for h, y in zip(heights, ys)) for ys in permutations(weights)]
        mean = Q(sum(values), len(values))
        def scatter(xs):
            return sum((x - Q(sum(xs), size))**2 for x in xs)
        assert mean == Q(sum(weights)*sum(heights), size)
        assert sum((x-mean)**2 for x in values)/len(values) == scatter(weights)*scatter(heights)/(size-1)


def check_length_and_clock():
    m = 10**8
    root = isqrt(m)
    height = sqrt_hi(43*m)
    # Constant and linear coefficients of the one-step bound.
    assert 3*height/(2*root) < 11 and Q(20, 2) < 11
    # Quadratic, linear and constant coefficients in the second difference.
    assert 3*((2*height+1)**2+7)/(4*m) < 250
    assert Q(50, root) + 30 < 250 and 70 < 250
    assert 3*height/(2*root)+15 < 100
    assert Q(3*43*(2*m+4), 4*m) < 100
    assert Q(3*4*43, 4) < 130
    assert 2*100 + 2*130 + 2*3 < 500
    assert 4*(Q(5,3)+1) < 11 and 4*(Q(5,3)+96) < 400
    assert (sqrt_hi(Q(2,3)*(2*m+1))+21)**2 < 4*m
    assert (11+3)*13+40+65*(2+Q(4,root))**2+500*4 < 2600
    assert 3*(24*height+11)/root < 480
    assert 9*(2*(43*m+1)*4*m + 8*(400+22+1)*43*m+800) < 3200*m*m
    assert 2600+480//2+3200//8+1 < 4000
    assert 2*4000+3+5 < 10000


def check_peak_inversion():
    rate = Q(".12")
    spacing = Q("3.25")
    z = spacing**3 / 16
    block = Q(3,8) + decay(z)/2 + decay(4*z)/8
    assert block*exp_small_upper(Q(".83")) < 1
    assert Q(63,64)*Q(".83")/(2*(spacing+Q(1,16))) > rate
    assert 16*exp_small_upper(Q(".83")) < 40
    assert 11*(1-Q(1,12))*sqrt_lo(6/PI_HI) > Q("12.3")
    # Integrate against the envelope above s/64 and bound both multiplier errors.
    # The required Gamma values have arguments at most 15/2 and others at least 3/2.
    assert 8*Q(3,2)*200**8*2000*decay(Q(10**19,3200)) < Q(1,10**14)
    assert 8*Q(3,2)*100**5*12/(2*10**28) < Q(1,10**15)
    assert 8*Q(3,2)*100**8*2000/(12*10**56) < Q(1,10**20)
    for m, cutoff, targets in (
        (10**19, 2680, (".000003", ".0054", "12.3")),
        (10**20, 3040, (".0000004", ".00088", "2.3")),
    ):
        scaled = (100*rate)**3 * cutoff**2
        z100 = next(i for i in range(10000) if i**3 > scaled)
        low, high = Q(z100-1,100), Q(z100,100)
        for i, target in enumerate(targets):
            b = Q(3*(i+1),2)
            main = Q(10000,m)/PI_LO * sum(
                Q(c*cutoff**(i+j+1),i+j+1) for j, c in enumerate((1,2,1)))
            tail = (120/PI_LO * sqrt_hi(1/rate)**(3*(i+1))
                    * decay(low)*sqrt_hi(high)**(3*(i+1)-2)/(1-(b-1)/low))
            assert main+tail+Q(1,10**12) < Q(target)


if __name__ == "__main__":
    check_excursions()
    check_parity_and_permutations()
    check_length_and_clock()
    check_peak_inversion()
    print("Verified excursion growth through semilength 8, both area parities, clock and peak bounds.")
