"""Check the fixed-point endpoint recurrence in RoundedDeficit.lean."""

import argparse
from math import isqrt

from verify import ballot_ranks, direct_ranks


def rounded_rows(last, cap, precision, requested):
    """Return rounded counts by actual corank, including both ends of the cap."""
    unit = 1 << precision
    # One spare bit isolates a possible spill when the whole sum is halved.
    byte_width = (precision + 2 + 7) // 8
    bits = 8 * byte_width
    base = 1 << bits
    slots = (1 << (bits * (cap + 1))) - 1
    mask = (slots // (base - 1)) * (base // 2 - 1)
    endpoints = [unit]
    for m in range(1, last + 1):
        if m % 2 == 0:
            endpoints.append(0)
        for d in range(m // 2, 0, -1):
            height = m - 2 * d
            down = endpoints[d - 1] << (bits * height)
            endpoints[d] = ((endpoints[d] + down) >> 1) & mask
        endpoints[0] //= 2
        if m in requested:
            packed = 0
            for d, endpoint in enumerate(endpoints):
                offset = (m - 2 * d) ** 2 // 4
                if offset <= cap:
                    packed += (endpoint << (bits * offset)) & slots
            data = (packed & slots).to_bytes(byte_width * (cap + 1), "little")
            yield m, [int.from_bytes(data[i:i + byte_width], "little")
                      for i in range(0, len(data), byte_width)]


def check_direct():
    last = 25
    cap = last * last // 4
    for precision in (6, 13, 26):
        unit = 1 << precision
        for m, rounded in rounded_rows(last, cap, precision, range(2, last + 1)):
            shape = tuple(range(m - 1, 0, -2))
            exact = direct_ranks(shape)[::-1]
            for k, count in enumerate(exact):
                lower = (2 * rounded[k]) << m
                upper = (2 * rounded[k] + (m // 2 + 1) * m) << m
                if not lower <= 2 * unit * count <= upper:
                    raise ArithmeticError((precision, m, k, rounded[k], count))
                if precision >= m and rounded[k] != count << (precision - m):
                    raise ArithmeticError(("exact digits", precision, m, k))


def check_pair(n, precision, compare_exact):
    last = 2 * n + 1
    requested = {last - 1, last}
    exact_rows = {}
    if compare_exact:
        exact_rows = {m: ranks for m, ranks in ballot_ranks(n) if m in requested}
    for m, row in rounded_rows(last, last * last // 8, precision, requested):
        start = isqrt(m ** 3) // 10
        end = m * m // 8
        peak = max(range(start, end + 1), key=row.__getitem__)
        error = (m // 2 + 1) * m
        if compare_exact:
            for k in range(end + 1):
                target = exact_rows[m][-1-k] << (precision + 1)
                lower = (2 * row[k]) << m
                upper = (2 * row[k] + error) << m
                if not lower <= target <= upper:
                    raise ArithmeticError(("exact rank outside enclosure", m, k))
            print(f"m={m}: {end + 1} enclosures agree with exact upper-half counts")
        for k in range(start, end):
            gap = row[k + 1] - row[k] if k < peak else row[k] - row[k + 1]
            if 2 * gap <= error:
                raise ArithmeticError(("overlapping enclosures", m, k, precision))
        print(f"m={m}: {end - start} strict comparisons at coranks "
              f"{start}..{end}, peak {peak}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows", type=int, default=192)
    parser.add_argument("--precision", type=int, default=128)
    parser.add_argument("--exact", action="store_true",
                        help="also compare the two upper halves with unrounded integer counts")
    args = parser.parse_args()
    if args.rows < 1 or args.precision < 1:
        parser.error("rows and precision must be positive")
    check_direct()
    print("Direct partition checks passed through 12 rows at three precisions.")
    check_pair(args.rows, args.precision, args.exact)
