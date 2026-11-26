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


def unpack_polynomial(packed, length, width):
    degree = (length // 2) * ((length + 1) // 2)
    data = packed.to_bytes(width * (degree + 1), "little")
    return [int.from_bytes(data[i:i + width], "little")
            for i in range(0, len(data), width)]


def ballot_ranks(max_n):
    """Yield (word length, ranks) in increasing length, starting at 2."""
    max_length = 2 * max_n + 1
    # Each base digit is a coefficient. Even the sum over all endpoints
    # counts at most 2**max_length words, strictly less than this base.
    width = max_length // 8 + 1
    bits = 8 * width
    endpoints = [1]
    for length in range(1, max_length + 1):
        if length % 2 == 0:
            endpoints.append(0)
        # Descending order keeps both predecessor polynomials in the old row.
        for downs in range(length // 2, 0, -1):
            # Every existing part increases by one. A last down adds part 1.
            endpoints[downs] = (endpoints[downs] + endpoints[downs - 1]) << (bits * downs)
        if length >= 2:
            yield length, unpack_polynomial(sum(endpoints), length, width)


def valley(ranks):
    """Return a descent and a subsequent ascent (their right indices)."""
    descent = None
    for j in range(1, len(ranks)):
        if ranks[j] < ranks[j - 1] and descent is None:
            descent = j
        if ranks[j] > ranks[j - 1] and descent is not None:
            return descent, j
    return None


def catalan_coranks(max_n):
    """Evaluate the Dyck, type B and odd-length recurrences at one wide base."""
    width = (2 * max_n + 1) // 8 + 1
    bits = 8 * width
    dyck = [1]
    type_b = [1]
    for n in range(1, max_n + 1):
        dyck.append(sum((dyck[h] * dyck[n - 1 - h]) << (bits * h) for h in range(n)))
        type_b.append(dyck[n] + sum((type_b[h] * dyck[n - h]) << (bits * (2 * h + 1))
                                    for h in range(n)))
        odd = sum((dyck[n - h] * type_b[h]) << (bits * h) for h in range(n + 1))
        yield unpack_polynomial(type_b[n], 2 * n, width)
        yield unpack_polynomial(odd, 2 * n + 1, width)


def verify(max_n, direct_n, verbose, upper_curvature=False):
    # Sensitivity control from Stanley and Zanello, just outside the families.
    control = direct_ranks((9, 7, 5, 3))
    if control[16:19] != [17, 16, 17] or valley(control) != (17, 18):
        raise ArithmeticError("failed to reproduce the published valley")
    catalan = catalan_coranks(direct_n)
    last_curvature_failure = {}
    for length, ranks in ballot_ranks(max_n):
        n = length // 2
        shape = range(length - 1, 0, -2)
        if len(ranks) != 1 + sum(shape) or ranks[0] != 1 or ranks[-1] != 1:
            raise ArithmeticError(f"wrong degree or extreme rank at length {length}")
        if sum(ranks) != comb(length, n):
            raise ArithmeticError(f"wrong ballot total at length {length}")
        if n <= direct_n and ranks != direct_ranks(shape):
            raise ArithmeticError(f"enumeration mismatch at length {length}")
        if n <= direct_n and ranks[::-1] != next(catalan):
            raise ArithmeticError(f"Catalan recurrence mismatch at length {length}")
        witness = valley(ranks)
        if witness:
            d, a = witness
            raise ArithmeticError(f"length {length}: ranks {d-1},{d} give "
                                  f"{ranks[d-1:d+1]}, ranks {a-1},{a} give {ranks[a-1:a+1]}")
        peak = max(ranks)
        if n >= 2:
            first_corank = ranks[::-1].index(peak)
            last_corank = len(ranks) - 1 - ranks.index(peak)
            lower_denominator = 15 if length == 6 else 14
            if ((lower_denominator * first_corank) ** 2 <= length ** 3
                    or (20 * last_corank) ** 2 >= 169 * length ** 3):
                raise ArithmeticError(f"global corank outside the proved bounds at {length=}")
        if upper_curvature:
            for j in range(len(ranks) // 2, len(ranks) - 1):
                if ranks[j] ** 2 <= ranks[j - 1] * ranks[j + 1]:
                    last_curvature_failure[length % 2] = (n, j)
        if verbose or n == max_n:
            print(f"length {length}, degree {len(ranks)-1}, peak {peak}, "
                  f"ranks {ranks.index(peak)}..{len(ranks)-1-ranks[::-1].index(peak)}")
    print(f"Both families unimodal for 1 <= n <= {max_n}. "
          f"Direct ranks and the Catalan recurrences agree through n = {direct_n}.")
    if upper_curvature:
        for parity, family in enumerate(("odd-part", "even-part")):
            failure = last_curvature_failure.get(parity)
            print(f"{family} upper-half strict log-concavity through n={max_n}: "
                  f"last failure (n, rank) = {failure}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=64)
    parser.add_argument("--direct-n", type=int, default=8)
    parser.add_argument("--verbose", action="store_true", help="show all peak ranks and sizes")
    parser.add_argument("--upper-curvature", action="store_true",
                        help="report strict log-concavity failures at interior ranks j >= degree/2")
    args = parser.parse_args()
    if not 1 <= args.direct_n <= args.max_n:
        parser.error("require 1 <= direct-n <= max-n")
    verify(args.max_n, args.direct_n, args.verbose, args.upper_curvature)
