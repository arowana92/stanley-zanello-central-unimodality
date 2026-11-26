"""Verify the finite bridge inequalities used in finite-tail.md (Python 3)."""

import argparse
from itertools import product

from verify import ballot_ranks


# Each entry is twice a lower bound on the interval centers.
BRIDGE = {48: 124, 96: 398, 192: 1228, 384: 3687}
FREE_END = {384: 5229, 385: 5254}


def minimum_area(length, start):
    return sum(max(0, start - j) // 2 for j in range(1, length + 1))


def walk_rows(start, length, cap, width):
    """Yield endpoint polynomials modulo q**(cap+1), one row per time."""
    bits = 8 * width
    keep = (1 << (bits * (cap + 1))) - 1
    row = {start: 1}
    for time in range(1, length + 1):
        next_row = {}
        for height in range((start + time) % 2, max(row, default=-2) + 2, 2):
            incoming = row.get(height - 1, 0) + row.get(height + 1, 0)
            packed = (incoming << (bits * (height // 2))) & keep
            if packed:
                next_row[height] = packed
        row = next_row
        yield time, row


def coefficients(packed, width, cap):
    mask = (1 << (8 * width * (cap + 1))) - 1
    data = (packed & mask).to_bytes(width * (cap + 1), "little")
    return [int.from_bytes(data[i:i + width], "little")
            for i in range(0, len(data), width)]


def check_small_walks():
    """Compare individual endpoints and truncation with enumerated words."""
    for start in (0, 2, 4):
        for cap in (4, 40):
            for time, row in walk_rows(start, 8, cap, 2):
                direct = {}
                for steps in product((-1, 1), repeat=time):
                    height = start
                    area = 0
                    for step in steps:
                        height += step
                        if height < 0:
                            break
                        area += height // 2
                    else:
                        if area <= cap:
                            counts = direct.setdefault(height, [0] * (cap + 1))
                            counts[area] += 1
                actual = {h: coefficients(p, 2, cap) for h, p in row.items()}
                if actual != direct:
                    raise ArithmeticError(f"direct enumeration failed at {start=}, {time=}, {cap=}")


def check_half_swaps():
    """Check the transposition phase in effective-small-area.md with integer actions."""
    def twice_edge_action(steps):
        height = len(steps)  # Both orders stay above the wall.
        action = 0
        for step in steps:
            following = height + step
            action += min(height, following)
            height = following
        return action

    for length in range(1, 8):
        for steps in product((-1, 1), repeat=2 * length):
            left, right = steps[:length], steps[length:]
            change = twice_edge_action(steps) - twice_edge_action(right + left)
            if change != length * (sum(left) - sum(right)):
                raise ArithmeticError(f"incorrect bridge phase for {steps=}")


class FailedInequality(ArithmeticError):
    """A proposed interval bound exceeds an exact coefficient inequality."""


def check_polynomial(packed, width, s, strict, label):
    a = coefficients(packed, width, s)
    for i in range((s + 1) // 2):
        if a[i] > a[i + 1] or a[i] > a[s - i]:
            raise FailedInequality(f"{label}: interval condition fails at {i=}, {s=}")
    if strict and (a[0] == 0 or any(a[i - 1] >= a[i] for i in range(1, s // 2 + 1))):
        raise FailedInequality(f"{label}: strict initial growth fails")


def verify_table(bridge_bounds, free_end_bounds):
    start = 0
    while True:
        bridges = {length: s for length, s in bridge_bounds.items()
                   if 2 * minimum_area(length, start) < s}
        suffixes = {length: s for length, s in free_end_bounds.items()
                    if 2 * minimum_area(length, start) < s}
        if not bridges and not suffixes:
            break
        length = max([*bridges, *suffixes])
        cap = max([*bridges.values(), *suffixes.values()])
        width = length // 8 + 1  # Base strictly greater than 2**length prevents carries.
        for time, row in walk_rows(start, length, cap, width):
            if time in bridges:
                for end, packed in row.items():
                    check_polynomial(packed, width, bridges[time], start == end == 0,
                                     f"bridge {time=}, {start=}, {end=}")
                if start == 0 and 0 not in row:
                    raise ArithmeticError("missing zero-to-zero bridge")
            if time in suffixes:
                check_polynomial(sum(row.values()), width, suffixes[time], start == 0,
                                 f"free suffix {time=}, {start=}")
        start += 2
    return start


def verify_numerical_bound():
    last_bad = None
    for m, ranks in ballot_ranks(191):
        n = m // 2
        stop = 9 * n + 42
        if stop >= len(ranks) or any(ranks[-k - 2] <= ranks[-k - 1] for k in range(stop)):
            last_bad = n
    if last_bad != 99:
        raise ArithmeticError(f"unexpected last exceptional n for the strict tail: {last_bad}")
    for n in range(192, 384):
        # Increasing n by 192 adds a 384-step bridge with 1843 strict steps.
        remainder = n - 192
        strict_steps = FREE_END[384] // 2
        for length in (192, 96, 48):
            count, remainder = divmod(remainder, length // 2)
            strict_steps += count * (BRIDGE[length] // 2)
        if strict_steps < 9 * n + 42:
            raise ArithmeticError(f"insufficient block coverage at {n=}")
    if BRIDGE[384] // 2 < 9 * 192 or FREE_END[385] < FREE_END[384]:
        raise ArithmeticError("the period increment or odd suffix bound is too small")
    print("The strict tail through corank 9*n+42 holds for every n >= 100.")


def search_linear(slope):
    length = 2
    while True:
        bound = (slope + 1) * length
        try:
            verify_table({length: bound}, {})
        except FailedInequality:
            length *= 2
            continue
        threshold = bound // 2
        print(f"Verified length {length}, twice-center {bound}. "
              f"Strict growth through corank {slope}*n for n >= {threshold}.")
        return


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--slope", type=int, help="search for a certificate at this positive integer slope")
    args = parser.parse_args()
    check_small_walks()
    check_half_swaps()
    if args.slope is None:
        stop = verify_table(BRIDGE, FREE_END)
        print(f"Verified fixed-endpoint bounds {BRIDGE} and free-end bounds {FREE_END}.")
        print(f"The minimum area bound handles every even starting height >= {stop}.")
        verify_numerical_bound()
    elif args.slope < 1:
        parser.error("slope must be positive")
    else:
        search_linear(args.slope)
