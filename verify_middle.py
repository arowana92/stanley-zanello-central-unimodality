"""Check selected ranks of the two central staircases without storing whole polynomials."""

import argparse
from math import isqrt

from verify import direct_ranks


def rank_window(length, first, last):
    """Compute the inclusive rank window by truncating each prefix at both ends."""
    degree = length ** 2 // 4
    if not 0 <= first <= last <= degree:
        raise ValueError("window outside the rank range")
    width = length // 8 + 1  # A digit exceeds the total number of words.
    bits = 8 * width
    row = [(0, 1)]
    for time in range(1, length + 1):
        remaining = length - time
        if time % 2 == 0:
            row.append((0, 0))
        for downs in range(time // 2, -1, -1):
            height = time - 2 * downs
            descend = min(remaining, height)
            rest = remaining - descend
            max_new = descend * (descend + 1) // 2 + descend * rest + rest ** 2 // 4
            shift = remaining * downs
            low = max(downs * (downs + 1) // 2, first - shift - max_new)
            high = min(downs * (time - downs), last - shift)
            packed = 0
            if low <= high:
                for previous in range(max(0, downs - 1), downs + 1):
                    old_low, old = row[previous]
                    offset = bits * (old_low + downs - low)
                    packed += old << offset if offset >= 0 else old >> -offset
                limit = bits * (high - low + 1)
                if packed.bit_length() > limit:
                    packed &= (1 << limit) - 1
            row[downs] = low, packed
    total = sum(value << (bits * (low - first)) for low, value in row if value)
    data = total.to_bytes(width * (last - first + 1), "little")
    return [int.from_bytes(data[i:i + width], "little")
            for i in range(0, len(data), width)]


def check_small_windows():
    for length in range(2, 22):
        ranks = direct_ranks(range(length - 1, 0, -2))
        degree = len(ranks) - 1
        # Exercise the extremes, disjoint interior windows, and a single rank.
        for first in range(0, degree + 1, 5):
            last = min(first + 4, degree)
            if rank_window(length, first, last) != ranks[first:last + 1]:
                raise ArithmeticError(f"partition enumeration mismatch at {length=}, {first=}")
        if rank_window(length, degree, degree) != [1]:
            raise ArithmeticError(f"full partition missing at {length=}")


def check_middle(n):
    for m in (2 * n, 2 * n + 1):
        degree = m ** 2 // 4
        first = (degree + 1) // 2
        # ceil(4*m**(3/2)), computed with integer arithmetic
        last = degree - isqrt(16 * m ** 3 - 1) - 1
        if last < first:
            print(f"word length {m}: interval empty")
            continue
        ranks = rank_window(m, first - 1, last + 1)
        for j, (left, center, right) in enumerate(zip(ranks, ranks[1:], ranks[2:]), first):
            if center ** 2 <= left * right:
                raise ArithmeticError(f"curvature failure at {m=}, {j=}")
            # 1/(1-x) >= exp(x) for 0 <= x < 1.
            if (m ** 3 - 5 * (degree - j)) * right < m ** 3 * center:
                raise ArithmeticError(f"rational growth certificate failed at {m=}, {j=}")
        print(f"word length {m}: growth and strict log-concavity at ranks {first}..{last}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=512, help="row count for the increasing-side check")
    args = parser.parse_args()
    if args.n < 1:
        parser.error("row count must be positive")
    check_small_windows()
    check_middle(args.n)
