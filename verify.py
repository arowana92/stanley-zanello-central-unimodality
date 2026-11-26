"""Exact rank polynomials for both central shifted staircases (Python 3)."""

import argparse
from math import comb


def direct_ranks(shape):
    """Visit each strict partition once, stopping at any occupied row."""
    counts = [0] * (1 + sum(shape))

    def visit(row, upper, weight):
        counts[weight] += 1
        if row < len(shape):
            for part in range(1, min(upper, shape[row]) + 1):
                visit(row + 1, part - 1, weight + part)

    visit(0, shape[0], 0)
    return counts


def ballot_ranks(max_n):
    """Yield (word length, ranks) in increasing length, starting at 2."""
    max_length = 2 * max_n + 1
    # Each base digit is a coefficient. Even the sum over all endpoints
    # counts at most 2**max_length words, strictly less than this base.
    width = max_length // 8 + 1
    bits = 8 * width
    endpoints = [1]
    for length in range(1, max_length + 1):
        previous = endpoints + [0]
        endpoints = [1]
        for downs in range(1, length // 2 + 1):
            # Every existing part increases by one. A last down adds part 1.
            endpoints.append((previous[downs] + previous[downs - 1]) << (bits * downs))
        if length >= 2:
            degree = (length // 2) * ((length + 1) // 2)
            data = sum(endpoints).to_bytes(width * (degree + 1), "little")
            yield length, [int.from_bytes(data[i:i + width], "little")
                           for i in range(0, len(data), width)]


def valley(ranks):
    """Return a descent and a subsequent ascent (their right indices)."""
    descent = None
    for j in range(1, len(ranks)):
        if ranks[j] < ranks[j - 1] and descent is None:
            descent = j
        if ranks[j] > ranks[j - 1] and descent is not None:
            return descent, j
    return None


def verify(max_n, direct_n, verbose):
    # Sensitivity control from Stanley and Zanello, just outside the families.
    control = direct_ranks((9, 7, 5, 3))
    if control[16:19] != [17, 16, 17] or valley(control) != (17, 18):
        raise ArithmeticError("failed to reproduce the published valley")
    for length, ranks in ballot_ranks(max_n):
        n = length // 2
        shape = range(length - 1, 0, -2)
        if len(ranks) != 1 + sum(shape) or ranks[0] != 1 or ranks[-1] != 1:
            raise ArithmeticError(f"wrong degree or extreme rank at length {length}")
        if sum(ranks) != comb(length, n):
            raise ArithmeticError(f"wrong ballot total at length {length}")
        if n <= direct_n and ranks != direct_ranks(shape):
            raise ArithmeticError(f"enumeration mismatch at length {length}")
        witness = valley(ranks)
        if witness:
            d, a = witness
            raise ArithmeticError(f"length {length}: ranks {d-1},{d} give "
                                  f"{ranks[d-1:d+1]}, ranks {a-1},{a} give {ranks[a-1:a+1]}")
        if verbose or n == max_n:
            peak = max(ranks)
            print(f"length {length}, degree {len(ranks)-1}, peak {peak}, "
                  f"ranks {ranks.index(peak)}..{len(ranks)-1-ranks[::-1].index(peak)}")
    print(f"Both families unimodal for 1 <= n <= {max_n}. "
          f"Direct ranks agree through n = {direct_n}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=64)
    parser.add_argument("--direct-n", type=int, default=8)
    parser.add_argument("--verbose", action="store_true", help="show all peak ranks and sizes")
    args = parser.parse_args()
    if not 1 <= args.direct_n <= args.max_n:
        parser.error("require 1 <= direct-n <= max-n")
    verify(args.max_n, args.direct_n, args.verbose)
