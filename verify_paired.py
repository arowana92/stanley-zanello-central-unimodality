"""Certify the bounds in paired-steps.md by exact rational polynomial arithmetic."""

from fractions import Fraction
from functools import lru_cache
from math import comb, lcm

from verify import direct_ranks
from verify_corank import truncated_coranks


DEGREE = 96
CAP = 432
SIZE = 1920
Q = Fraction(9, 25)
RADIUS = Fraction(39, 100)


def log_derivative(row):
    """Coefficients of q Z'(q)/Z(q), with Z(0)=1."""
    values = [0]
    for h in range(1, len(row)):
        values.append(h * row[h] - sum(values[i] * row[h - i] for i in range(1, h)))
    return values


def size_endpoints():
    # The paired-step recurrence makes every retained log coefficient affine
    # in n here. Two successive rows determine it, and a third checks it.
    n0 = CAP + 1
    logs = [[], []]
    small_logs = [[], []]
    for length, row in truncated_coranks(n0 + 2, CAP):
        n = length // 2
        if n <= 10:
            ranks = direct_ranks(range(length - 1, 0, -2))[::-1]
            if row != (ranks + [0] * len(row))[:len(row)]:
                raise ArithmeticError(f"direct partition mismatch at length {length}")
            small_logs[length % 2].append(log_derivative(row[:2 * n + 3]))
        if n >= n0:
            logs[length % 2].append(log_derivative(row))
    result = []
    for parity, (a, b, c) in enumerate(logs):
        slope = [y - x for x, y in zip(a, b)]
        if any(z - y != v for y, z, v in zip(b, c, slope)):
            raise ArithmeticError(f"log coefficients have not stabilized at parity {parity}")
        for n, observed in enumerate(small_logs[parity], 1):
            predicted = [x + (n - n0) * v for x, v in zip(a, slope)][:len(observed)]
            predicted[-1] -= 2 * n + 2  # The first finite-size correction in (3).
            if observed != predicted:
                raise ArithmeticError(f"first correction failed at {parity=}, {n=}")
        if parity == 0:
            result.append(("infinite size", slope, 1))
        elif slope != result[0][1]:
            raise ArithmeticError("stable slopes differ between parities")
        result.append((("odd-part", "even-part")[parity],
                       [x + (SIZE - n0) * v for x, v in zip(a, slope)], SIZE))
    return result


def chebyshev_on_interval(left, right, denominator):
    """Return d**j T_j((left + (right-left)*t)/d) in powers of t."""
    polys = [[1], [left, right - left]]
    for j in range(2, DEGREE + 1):
        current = [0] * (j + 1)
        for k, value in enumerate(polys[-1]):
            current[k] += 2 * left * value
            current[k + 1] += 2 * (right - left) * value
        for k, value in enumerate(polys[-2]):
            current[k] -= denominator ** 2 * value
        polys.append(current)
    return polys


@lru_cache(maxsize=1)
def bernstein_weights():
    # On [0,1], the i-th Bernstein coefficient of t**h at degree D is
    # binom(i,h)/binom(D,h). A common denominator keeps all weights integral.
    scale = lcm(*(comb(DEGREE, j) for j in range(DEGREE + 1)))
    return scale, [[comb(i, h) * (scale // comb(DEGREE, h)) for h in range(i + 1)]
                   for i in range(DEGREE + 1)]


@lru_cache(maxsize=None)
def angular_rows(left, right, denominator, cubic):
    """Convert each angular factor to the common Bernstein basis."""
    cheb = chebyshev_on_interval(left, right, denominator)
    scale_x = denominator ** DEGREE
    common = lcm(*range(1, DEGREE + 1))
    _, weights = bernstein_weights()
    rows = []
    for h in range(1, DEGREE + 1):
        if cubic:
            # h**3 a_h cos(h theta), where logs[h] = h*a_h.
            angular = [v * denominator ** (DEGREE - h) for v in cheb[h]]
            coeff = h ** 2 * common
        else:
            # (1-cos(h theta))/(1-cos theta), including its value h**2 at zero.
            angular = [h * scale_x] + [0] * (h - 1)
            for j in range(1, h):
                factor = 2 * (h - j) * denominator ** (DEGREE - j)
                for k, value in enumerate(cheb[j]):
                    angular[k] += factor * value
            coeff = common // h
        factor = coeff * Q.numerator ** (h - 1) * Q.denominator ** (DEGREE - h + 1)
        rows.append([factor * sum(v * w for v, w in zip(angular, ws)) for ws in weights])

    return rows


def coefficient_box(logs, size, left, right, denominator, cubic):
    """Enclose the truncated polynomial on [0,Q] times a cosine interval."""
    scale_basis, weights = bernstein_weights()
    rows = angular_rows(left, right, denominator, cubic)
    rows = [[v * value for v in row] for row, value in zip(rows, logs[1:])]
    extremes = []
    for ws in weights:
        for i in range(DEGREE + 1):
            extremes.append(sum(row[i] * w for row, w in zip(rows, ws)))
    scale = (size * lcm(*range(1, DEGREE + 1)) * denominator ** DEGREE
             * Q.denominator ** DEGREE * scale_basis ** 2)
    return Fraction(min(extremes), scale), Fraction(max(extremes), scale)


def verify():
    # The zero-free estimate gives |a_h|/n <= 2/RADIUS**h beyond CAP.
    ratio = (Q / RADIUS) * Fraction(CAP + 2, CAP + 1) ** 3
    analytic_tail = (2 / RADIUS) * (CAP + 1) ** 3 * (Q / RADIUS) ** CAP / (1 - ratio)
    for name, logs, size in size_endpoints():
        damping_tail = analytic_tail + sum(Fraction(abs(logs[h]) * h, size) * Q ** (h - 1)
                                           for h in range(DEGREE + 1, CAP + 1))
        cubic_tail = analytic_tail + sum(Fraction(abs(logs[h]) * h ** 2, size) * Q ** (h - 1)
                                         for h in range(DEGREE + 1, CAP + 1))
        mean = sum(Fraction(logs[h], size) * Q ** h for h in range(1, CAP + 1))
        if mean - Q * analytic_tail <= Fraction(1, 3):
            raise ArithmeticError(f"mean bound failed at {name}")
        # Split [-1,1] at multiples of 1/8. The cubic is needed only for
        # cos(theta) >= 15/16 and is certified on that single interval.
        boxes = [coefficient_box(logs, size, i, i + 1, 8, cubic=False)
                 for i in range(-8, 8)]
        lower = min(lo for lo, hi in boxes) - damping_tail
        upper = max(hi for lo, hi in boxes) + damping_tail
        if lower <= Fraction(7, 10) or upper >= Fraction(3, 2):
            raise ArithmeticError(f"Fourier damping bound failed at {name}: {float(lower)}, {float(upper)}")
        lo, hi = coefficient_box(logs, size, 15, 16, 16, cubic=True)
        cubic_bound = max(-lo, hi) + cubic_tail
        if cubic_bound >= 3:
            raise ArithmeticError(f"third derivative bound failed at {name}")
        print(f"{name}: 0.70 < damping < 1.50, cubic < 3, mean at q=9/25 exceeds n/3.")


if __name__ == "__main__":
    verify()
