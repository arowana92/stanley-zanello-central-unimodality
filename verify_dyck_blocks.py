"""Check reflected area comparisons independently by forward walk enumeration."""

import argparse
from math import isqrt


def dyck_cut(n):
    if n == 0:
        return 0
    return max(0, (isqrt(8 * n**3) + 3) // 3 - n)


def advance(row, width, mask):
    new = []
    for h in range(len(row) + 1):
        up = row[h - 1] if h else 0
        down = row[h + 1] if h + 1 < len(row) else 0
        new.append(((up + down) << (width * (h // 2))) & mask)
    while new and new[-1] == 0:
        new.pop()
    return new


def coefficients(value, width, cutoff):
    size = width // 8
    data = (value & ((1 << (width * (cutoff + 1))) - 1)).to_bytes(size * (cutoff + 1), "little")
    return [int.from_bytes(data[i:i + size], "little") for i in range(0, len(data), size)]


def reflected(digits):
    end = len(digits) - 1
    return (all(digits[i] <= digits[i + 1] for i in range(end // 2))
            and all(digits[i] <= digits[end - i] for i in range(end // 2 + 1)))


def direct(n):
    row = [0] * (n * (n - 1) // 2 + 1)

    def visit(remaining, h, area):
        if remaining < h:
            return
        if not remaining:
            row[area] += 1
            return
        visit(remaining - 1, h + 1, area + (h + 1) // 2)
        if h:
            visit(remaining - 1, h - 1, area + (h - 1) // 2)

    visit(2 * n, 0, 0)
    return row


def block(m, height, cutoff, prefix):
    if prefix > m or 2 * prefix * ((height - prefix) // 2) < cutoff:
        raise ValueError("height threshold does not cover the endpoint tail")
    width = 8 * (m // 8 + 1)
    mask = (1 << (width * (cutoff + 1))) - 1
    for start in range(height):
        row = [0] * start + [1]
        for _ in range(m):
            row = advance(row, width, mask)
        for end, value in enumerate(row[:height]):
            if not reflected(coefficients(value, width, cutoff)):
                raise ArithmeticError((m, start, end, cutoff))
    print(f"All boundary heights pass at {m} steps, reflected cutoff {cutoff}.")


def dycks(max_n):
    width = 8 * (2 * max_n // 8 + 1)
    direct_n = min(10, max_n)
    cutoff = max(dyck_cut(max_n), direct_n * (direct_n - 1) // 2)
    mask = (1 << (width * (cutoff + 1))) - 1
    row = [1]
    for n in range(max_n + 1):
        if n:
            row = advance(advance(row, width, mask), width, mask)
        if n <= direct_n:
            expected = direct(n)
            actual = coefficients(row[0], width, len(expected) - 1)
            if actual != expected:
                raise ArithmeticError(f"direct enumeration disagrees at {n}")
        if not reflected(coefficients(row[0], width, dyck_cut(n))):
            raise ArithmeticError(f"reflected pair fails at {n}")
    print(f"Dyck comparisons pass through semilength {max_n}, with direct enumeration through {direct_n}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=256)
    args = parser.parse_args()
    if args.max_n < 0:
        parser.error("semilength must be nonnegative")
    block(64, 30, 202, 14)
    dycks(args.max_n)
