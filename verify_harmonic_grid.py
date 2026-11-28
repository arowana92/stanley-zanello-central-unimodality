"""Independent exact integration of the quarter-unit two-harmonic frequency grid."""

from bisect import bisect_right
from fractions import Fraction as Q
from itertools import accumulate, product
from math import ceil, factorial


# At these upper grid endpoints (quarter units) one more block is used.
BLOCK_CHANGES = (146, 334, 565, 842, 1157, 1469, 1862, 2268, 2656, 3109, 3499,
                 4095, 4608, 5185, 5609, 6311, 6827, 7386, 7990, 8643, 9349,
                 10112, 10938, 11376, 12306, 12799, 13844, 14398, 14974, 15573, 16196)
EPS = Q(1, 4096)
SPAN = Q(17, 20)


def exp_upper(x):
    """Upper bound for exp(-x) from the positive exponential series."""
    assert x >= 0
    return 1 / sum(x**i / factorial(i) for i in range(15))


def weight(lo, hi, blocks):
    width = (SPAN - EPS) / blocks - 2 * EPS
    angle = hi * (SPAN + EPS) / (128 * blocks)
    assert width > EPS
    energy = lo**2 * (width**3 - width * EPS**2) / 120

    def harmonic(j):
        return exp_upper(j*j * energy * max(0, 1 - (j*angle)**2 / 6)**2)

    factor = Q(3, 8) + harmonic(1) / 2 + harmonic(2) / 8
    rounded = Q(ceil(factor * 10**6), 10**6)
    return Q(ceil(rounded**blocks * 10**14), 10**14)


def check_reflection():
    for t in range(13):
        endpoints = []
        minima = []
        for signs in product((-1, 1), repeat=t):
            heights = list(accumulate(signs, initial=0))
            endpoints.append(heights[-1])
            minima.append(min(heights))
        assert sum(y + 1 for y, low in zip(endpoints, minima) if low >= 0) == 2**t
        for a in range(t + 2):
            hits = sum(a + low <= 0 for low in minima)
            assert hits == sum((y >= a) + (y >= a + 1) for y in endpoints)


def main():
    check_reflection()
    moments = [Q(0) for _ in range(3)]
    left = count = 0
    while left < 16384:
        right = min(16384, left + 1 + left // 25)
        k = 1 + bisect_right(BLOCK_CHANGES, right)
        lo, hi = Q(left, 4), Q(right, 4)
        bound = weight(lo, hi, k)
        for r in range(3):
            moments[r] += bound * (hi**(r+1) - lo**(r+1)) / (r+1)
        left = right
        count += 1

    assert count == 180 and exp_upper(Q(21, 4))**2 <= Q(3, 100000)
    for r, (moment, limit, old, target) in enumerate(zip(
            moments, (41, 2454, 402487), (19, 810, 98000), (Q(18, 5), Q(109, 2), Q(3800)))):
        assert moment <= limit
        total = (Q(259, 1000)**(r+1)*limit + Q(1, 2)) / Q(314, 100)
        total += Q(3, 100000) * 8**(r+1) * old
        assert total <= target
        print(f"Order {r}: low-frequency moment {moment} <= {limit}; scaled budget <= {target}")


if __name__ == "__main__":
    main()
