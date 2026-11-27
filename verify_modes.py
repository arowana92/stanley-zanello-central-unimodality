"""Reconstruct central staircase coefficients from the formal q-Airy roots."""

import argparse
from math import isqrt

from verify import ballot_ranks, direct_ranks


def multiply(left, right, size):
    result = [0] * size
    for i, a in enumerate(left[:size]):
        if a:
            for j, b in enumerate(right[:size - i]):
                result[i + j] += a * b
    return result


def divide(top, bottom, size):
    """Series division when the denominator has constant coefficient +/-1."""
    if abs(bottom[0]) != 1:
        raise ArithmeticError("nonunit leading coefficient")
    result = []
    for j in range(size):
        other = sum(result[j - i] * bottom[i] for i in range(1, j + 1))
        result.append((top[j] - other) * bottom[0])
    return result


def evaluate(terms, x, size):
    """Horner evaluation in x, reducing coefficients modulo q**size."""
    value = [0] * size
    for term in reversed(terms):
        value = multiply(value, x, size)
        for j, a in enumerate(term[:size]):
            value[j] += a
    return value


def shifted(series, offset, size):
    if offset >= size:
        return [0] * size
    return [0] * offset + series[:size - offset]


def mode(r, size):
    # After the change z=q**(-2*r)*x, both H and the two numerators
    # are multiplied by q**(r*(r+1)). All remaining exponents are >= 0.
    one = [1] + [0] * (size - 1)
    reciprocal = one[:]
    partial = [0] * size
    denominator = []
    numerators = [[], []]
    for i in range(r + isqrt(size) + 3):
        if i:
            # Divide the previous reciprocal Pochhammer by 1-q**i.
            for j in range(i, size):
                reciprocal[j] += reciprocal[j - i]
        signed = [(-1) ** i * a for a in reciprocal]
        partial = [a + b for a, b in zip(partial, signed)]
        denominator.append(shifted(signed, (i - r) * (i - r - 1), size))
        for parity in range(2):
            offset = (i - r) ** 2 + r + parity * i
            numerators[parity].append(shifted(partial, offset, size))

    derivative = [[i * a for a in term] for i, term in enumerate(denominator) if i]
    x = one[:]
    precision = 1
    while precision < size:
        precision = min(2 * precision, size)
        error = evaluate(denominator, x, precision)
        slope = evaluate(derivative, x, precision)
        step = divide(error, slope, precision)
        for j, a in enumerate(step):
            x[j] -= a
    if any(evaluate(denominator, x, size)):
        raise ArithmeticError(f"root residual at mode {r}")

    growth = divide(one, x, size)
    slope = multiply(x, evaluate(derivative, x, size), size)
    amplitudes = []
    for parity in range(2):
        top = evaluate(numerators[parity], x, size)
        amplitude = divide([-a for a in top], slope, size)
        start = r + r % 2 if parity == 0 else 2 * r
        if start < size and (any(amplitude[:start]) or amplitude[start] != (-1) ** r):
            raise ArithmeticError(f"amplitude leading term at {r=}, {parity=}")
        amplitudes.append(amplitude)
    if r + 1 < size and (growth[0] != 1 or any(growth[1:r + 1]) or growth[r + 1] != 1):
        raise ArithmeticError(f"growth leading term at {r=}")
    return growth, amplitudes


def verify(max_n, cap, direct_n):
    # At small sizes include a few degrees beyond the true support.
    def last_degree(length):
        return min(cap, (length // 2) * ((length + 1) // 2) + 8)

    modes = []
    r = 0
    while True:
        precision = max(last_degree(m) - 2 * r * (m // 2) + 1
                        for m in range(2, 2 * max_n + 2))
        if precision <= r:
            break
        growth, amplitudes = mode(r, precision)
        modes.append((growth, amplitudes, [1] + [0] * (precision - 1)))
        r += 1

    comparisons = 0
    for length, ranks in ballot_ranks(max_n):
        n, parity = divmod(length, 2)
        if n <= direct_n and ranks != direct_ranks(range(length - 1, 0, -2)):
            raise ArithmeticError(f"direct partition mismatch at length {length}")
        end = last_degree(length)
        result = [0] * (end + 1)
        for r, (growth, amplitudes, power) in enumerate(modes):
            if parity == 0:
                power[:] = multiply(power, growth, len(power))
            offset = 2 * r * n
            if offset > end:
                continue
            values = multiply(amplitudes[parity], power, end + 1 - offset)
            for j, a in enumerate(values):
                result[offset + j] += a
            if r == 0:
                principal = result[:]
        exact = (ranks[::-1] + [0] * 8)[:end + 1]
        for k, (a, b) in enumerate(zip(result, exact)):
            if a != b:
                raise ArithmeticError(f"length {length}, corank {k}: roots give {a}, expected {b}")
        if n >= 2:
            errors = [-1, 2, -n - 4 - parity, 3 * n + 8 + 3 * parity]
            for k, error in enumerate(errors, 2 * n + 2):
                if k <= end and exact[k] - principal[k] != error:
                    raise ArithmeticError(f"principal term correction at length {length}, corank {k}")
        comparisons += len(result)
    print(f"Checked {comparisons} coefficients, including zeros beyond support, "
          f"for both families through n={max_n} and corank {cap}.")
    print(f"Used {len(modes)} formal roots. Direct partition ranks agree through n={direct_n}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=48)
    parser.add_argument("--cap", type=int, default=128)
    parser.add_argument("--direct-n", type=int, default=12)
    args = parser.parse_args()
    if not 1 <= args.direct_n <= args.max_n or args.cap < 1:
        parser.error("require 1 <= direct-n <= max-n and a positive corank cap")
    verify(args.max_n, args.cap, args.direct_n)
