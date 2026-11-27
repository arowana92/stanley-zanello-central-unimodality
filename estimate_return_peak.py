"""Numerical Airy-integral evaluation of the constants in return-expansion.md."""

import cmath
from math import exp, fsum, gamma, pi, sqrt

from verify import ballot_ranks


def airy_roots(count):
    """Return (a, integral[Ai from -a to infinity] / Ai'(-a)) at Ai(-a)=0."""
    a = 0.0
    value = 1 / (3**(2/3) * gamma(2/3))
    slope = 1 / (3**(1/3) * gamma(1/3))
    integral = 1/3
    roots = []
    while len(roots) < count:
        # Local Taylor solution for g(a)=Ai(-a), with g''=-a*g.
        coeff = [value, slope]
        for j in range(20):
            previous = coeff[j-1] if j else 0
            coeff.append(-(a * coeff[j] + previous) / ((j+1) * (j+2)))

        def evaluate(step):
            return fsum(c * step**i for i, c in enumerate(coeff))

        def derivative(step):
            return fsum(i * coeff[i] * step**(i-1) for i in range(1, len(coeff)))

        def accumulated(step):
            return integral + fsum(c * step**(i+1) / (i+1) for i, c in enumerate(coeff))

        step = 0.125
        end_value = evaluate(step)
        if value * end_value <= 0:
            lo, hi = 0.0, step
            for _ in range(48):
                mid = (lo + hi) / 2
                if value * evaluate(mid) > 0:
                    lo = mid
                else:
                    hi = mid
            root = (lo + hi) / 2
            roots.append((a + root, -accumulated(root) / derivative(root)))
        value, slope, integral = end_value, derivative(step), accumulated(step)
        a += step
    return roots


def mode_constants(contour, spacing, limit, num_roots):
    """Trapezoidal Laplace inversion on the vertical line Re(t)=contour."""
    roots = airy_roots(num_roots)
    nodes = []
    last_node = round(limit / spacing)
    for i in range(last_node + 1):
        t = complex(contour, i * spacing)
        power = t**(2/3) / 2
        terms = [cmath.exp(-a * power) for a, _ in roots]
        weight = sqrt(pi/2) * spacing / pi * (0.5 if i in (0, last_node) else 1)
        meander = weight * t**(1/3) * sum(r * term for (_, r), term in zip(roots, terms))
        excursion = weight * t * sum(terms)
        nodes.append((t, meander, excursion))

    def inverted(x, order, excursion=False):
        terms = ((cmath.exp(1j * t.imag * x) * t**order * (g if excursion else f)).real
                 for t, f, g in nodes)
        return exp(contour*x) * fsum(terms)

    lo, hi = 0.3, 0.5
    if not inverted(lo, 1) > 0 > inverted(hi, 1):
        raise ArithmeticError("root bracket for the limiting mode failed")
    for _ in range(48):
        mid = (lo + hi) / 2
        if inverted(mid, 1) > 0:
            lo = mid
        else:
            hi = mid
    x = (lo + hi) / 2
    second = inverted(x, 2)
    third = inverted(x, 3)
    g_prime = inverted(x, 1, excursion=True)
    dilation_prime = -1.5 * x * second
    dilation_sq_prime = 2.25 * (5 * x * second + x*x * third)
    shifts = []
    for parity in (0, 1):
        correction_prime = ((1/12 + parity/2) * dilation_prime
                            - (dilation_sq_prime - dilation_prime) / 30
                            + (parity/4 - 3/40) * g_prime)
        shifts.append(-correction_prime / second)
    return x, *shifts


def check(max_n=96):
    first = mode_constants(20, 1.0, 1400, 10)
    second = mode_constants(28, 0.75, 1650, 14)
    if max(abs(a-b) for a, b in zip(first, second)) > 1e-9:
        raise ArithmeticError("Airy inversion parameters disagree")
    x, *shifts = second
    print(f"x_* = {x:.10f}, -C'_0/F'' = {shifts[0]:.10f}, -C'_1/F'' = {shifts[1]:.10f}")
    hits = 0
    misses = []
    last_ranks = []
    for m, ranks in ballot_ranks(max_n):
        length = m + 1
        half_length, parity = divmod(length, 2)
        center = (length + (m+1)//2) / 2
        prediction = (2 * half_length)**1.5 * (x + shifts[parity] / half_length) - center
        nearest = round(prediction)
        peak = max(ranks)
        if 0 <= nearest < len(ranks) and ranks[-1-nearest] == peak:
            hits += 1
        else:
            misses.append(m)
        if m // 2 == max_n:
            last_ranks.append((m, prediction, len(ranks)-1-ranks.index(peak)))
    print(f"Nearest predicted corank attains the exact maximum for {hits}/{2*max_n} shapes. "
          f"Missed ballot lengths: {misses}")
    for m, prediction, corank in last_ranks:
        print(f"m={m}, predicted {prediction:.6f}, an exact maximizing corank {corank}")


if __name__ == "__main__":
    check()
