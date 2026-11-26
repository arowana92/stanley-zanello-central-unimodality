"""Certify fixed-corank log-concavity at infinitely many staircase sizes."""

import argparse
from math import comb, isqrt

from verify import direct_ranks


def truncated_coranks(max_n, cap):
    """Yield the two corank rows through degree cap at each positive size."""
    # The n row deficits form a weak composition of their total. Even after
    # summing over endpoints, each retained coefficient fits in one digit.
    width = (comb(max_n + cap, cap).bit_length() + 7) // 8
    bits = 8 * width
    mask = (1 << (bits * (cap + 1))) - 1
    endpoints = [1]
    for length in range(1, 2 * max_n + 2):
        # To reach height 2h or 2h+1 costs at least h**2 units of area.
        top = min(length, 2 * isqrt(cap) + 1)
        following = [0] * (top + 1)
        for height in range(length % 2, top + 1, 2):
            up = endpoints[height - 1] if 0 < height <= len(endpoints) else 0
            down = endpoints[height + 1] if height + 1 < len(endpoints) else 0
            following[height] = ((up + down) << (bits * (height // 2))) & mask
        endpoints = following
        if length >= 2:
            packed = sum(endpoints).to_bytes(width * (cap + 1), "little")
            yield length, [int.from_bytes(packed[i:i + width], "little")
                           for i in range(0, len(packed), width)]


def verify(cap, direct_n):
    # One extra sample checks the predicted vanishing higher difference.
    max_n = max(4, cap + 1) + 2 * cap + 1
    rows = [[None], [None]]
    for length, values in truncated_coranks(max_n, cap + 1):
        n = length // 2
        if n <= direct_n:
            full = direct_ranks(range(length - 1, 0, -2))[::-1]
            expected = (full + [0] * len(values))[:len(values)]
            if values != expected:
                raise ArithmeticError(f"direct corank mismatch at length {length}")
        rows[length % 2].append(values)

    for parity, family in enumerate(("odd-part", "even-part")):
        for k in range(1, cap + 1):
            start = max(4, k + 1)
            samples = rows[parity][start:start + 2 * k + 2]
            differences = [row[k] ** 2 - row[k - 1] * row[k + 1] for row in samples]
            for order in range(2 * k + 1):
                if differences[0] <= 0:
                    raise ArithmeticError(f"{family}, k={k}, n={start}, "
                                          f"Newton coefficient {order} = {differences[0]}")
                differences = [b - a for a, b in zip(differences, differences[1:])]
            if differences != [0]:
                raise ArithmeticError(f"unexpected degree at {family}, k={k}")
        print(f"{family}: positive Newton coefficients for 1 <= k <= {cap} "
              f"at n = max(4, k+1), through order 2k.")
    print(f"Checked one additional size per polynomial and direct ranks through n={direct_n}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-corank", type=int, default=256)
    parser.add_argument("--direct-n", type=int, default=12)
    args = parser.parse_args()
    if args.max_corank < 1 or not 1 <= args.direct_n <= max(4, args.max_corank + 1) + 2 * args.max_corank + 1:
        parser.error("require a positive corank limit and a direct size within the computed range")
    verify(args.max_corank, args.direct_n)
