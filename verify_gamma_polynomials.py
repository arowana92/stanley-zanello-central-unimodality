"""Check the polynomial last-return trial on the entire interval 0 <= v <= 256.

All certificate arithmetic uses integers or fractions. The stored coefficients
multiply T_j(1-2v/256), in units of 2^-120. Run with the standard library.
"""

import json
from fractions import Fraction
from math import comb, factorial, lcm
from pathlib import Path


TABLE = Path(__file__).resolve().parent / "research" / "gamma-polynomials.json"


def monomial_coefficients(row, scale):
    """Expand the input in z=v/256 using T_(n+1)=2(1-2z)T_n-T_(n-1)."""
    previous, current = [], [1]
    result = [0] * len(row)
    for coefficient in row:
        for j, value in enumerate(current):
            result[j] += coefficient * value
        if not previous:
            previous, current = current, [1, -2]
            continue
        following = [0] * (len(current) + 1)
        for j, value in enumerate(current):
            following[j] += 2 * value
            following[j + 1] -= 4 * value
        for j, value in enumerate(previous):
            following[j] -= value
        previous, current = current, following
    return [Fraction(value, scale) for value in result]


def split_product(left, right):
    """Multiply z^a and z^b with weight (1/2)_a (1/2)_b / (a+b)!."""
    def scaled(poly):
        denominator = lcm(*(c.denominator for c in poly))
        values = [c.numerator * (denominator // c.denominator)
                  * (factorial(2*j) // factorial(j)) for j, c in enumerate(poly)]
        return denominator, values

    left_den, left_num = scaled(left)
    right_den, right_num = scaled(right)
    result = []
    for j in range(len(left) + len(right) - 1):
        lower = max(0, j - len(right) + 1)
        upper = min(j, len(left) - 1)
        total = sum(left_num[i] * right_num[j-i] for i in range(lower, upper + 1))
        result.append(Fraction(total, left_den * right_den * 4**j * factorial(j)))
    return result


def subtract(poly, *terms):
    result = list(poly) + [Fraction(0)] * (max(map(len, (poly,) + terms)) - len(poly))
    for term in terms:
        for j, value in enumerate(term):
            result[j] -= value
    return result


def chebyshev_coefficients(poly):
    """Transform z^j=((1-cos t)/2)^j into a cosine series with exact coefficients."""
    denominators = [c.denominator * 4**j for j, c in enumerate(poly)]
    denominator = lcm(*denominators)
    row = [0] * len(poly)
    for j, (c, d) in enumerate(zip(poly, denominators)):
        factor = c.numerator * (denominator // d)
        if not factor:
            continue
        choose = 1
        for k in range(j, -1, -1):
            multiplier = 1 if k == 0 else (-2 if k % 2 else 2)
            row[k] += multiplier * choose * factor
            choose = choose * (j + k) // (j - k + 1)
    return row, denominator


def derivative_coefficients(row):
    """Differentiate a Chebyshev series in its unshifted argument."""
    derivative = [0] * (len(row) + 1)
    for k in range(len(row) - 1, 0, -1):
        derivative[k-1] = derivative[k+1] + 2*k*row[k]
    # dT_k/dy = k U_(k-1)(y). The constant cosine has half weight.
    assert derivative[0] % 2 == 0
    derivative[0] //= 2
    return derivative[:-2] or [0]


def uniform_bounds(poly, width):
    """Triangle bounds for the value and v derivative using |T_j| <= 1."""
    row, denominator = chebyshev_coefficients(poly)
    return (Fraction(sum(map(abs, row)), denominator),
            Fraction(2 * sum(map(abs, derivative_coefficients(row))), width * denominator))


def gaussian_defect(poly, width, divisor):
    """Residual for g'(z)+(3 width^3/divisor) z^2 g(z)=0."""
    result = [Fraction(0)] * (len(poly) + 2)
    for j, c in enumerate(poly):
        if j:
            result[j-1] += j*c
        result[j+2] += Fraction(3*width**3, divisor) * c
    return result


def correction(poly, width, quadratic, quintic):
    result = [Fraction(0)] * (len(poly) + 5)
    for j, c in enumerate(poly):
        result[j+2] += quadratic * width**2 * c
        result[j+5] += quintic * width**5 * c
    return result


def check_identities():
    row = [4, -6, 3, 0, 5, -2, 1]
    poly = monomial_coefficients(row, 8)
    recovered, denominator = chebyshev_coefficients(poly)
    assert [Fraction(c, denominator) for c in recovered] == [Fraction(c, 8) for c in row]
    slope = [j*c for j, c in enumerate(poly) if j]
    assert uniform_bounds(poly, 1)[1] == uniform_bounds(slope, 1)[0]
    left = [Fraction(2, 3), -1, 3, -5]
    right = [1, Fraction(7, 4), 0, 2, -1]
    product = split_product(left, right)

    def rising(x, degree):
        value = 1
        for j in range(degree):
            value *= x+j
        return value

    def gamma(poly, shape, step):
        return sum(c * step**j * rising(shape, j) for j, c in enumerate(poly))

    def survival(n):
        return Fraction(comb(2*n, n), 4**n)

    for n in range(11):
        for step in (Fraction(0), Fraction(3, 17), Fraction(-2, 9)):
            exact = sum(survival(k) * survival(n-k)
                        * gamma(left, k + Fraction(1, 2), step)
                        * gamma(right, n-k + Fraction(1, 2), step) for k in range(n + 1))
            assert gamma(product, n+1, step) == exact


def check(label, value, limit):
    if value >= limit:
        raise ArithmeticError(f"{label} exceeds its certified limit")
    print(f"{label}: {float(value):.6g} < {limit}")


def check_amplitude_bound(width, trial, free_error, bridge_error, base, base_slope):
    """Apply the finite-size arcsine residual theorem on the full scaled window."""
    denominator = 2**120
    norms = []
    for order in range(3):
        norms.append(Fraction(sum(map(abs, trial)) * 2**order, denominator * width**order))
        trial = derivative_coefficients(trial)
    value, slope, curvature = norms
    # The ODE defect is in the unit variable z; the derivative in v gains 1/width.
    def derivative_error(error, divisor):
        return error * (Fraction(1, width) + Fraction(3 * width**2, divisor))

    endpoint = base + free_error + bridge_error*value
    lipschitz = (base_slope + derivative_error(free_error, 24)
                 + derivative_error(bridge_error, 96)*value + bridge_error*slope)
    bridge_slope = Fraction(width**2, 32)
    bridge_curvature = bridge_slope**2 + Fraction(width, 16)
    split_curvature = bridge_curvature*value + 2*bridge_slope*slope + curvature
    check("split second derivative divided by v^2", split_curvature, 9_000_000)
    # N >= 10^54, u <= 256, xi <= 4096. omega^2 = (u/N)^3/32.
    root_n = 10**27
    assert Fraction(9 * width**3, 32*root_n**2) <= 1
    discretization = (1+value)*(width**3 + width**6) + split_curvature*width**2/8
    error = (1+4096//2)*endpoint + width*lipschitz + 4*discretization/root_n
    check("conditional amplitude error for N >= 10^54", error, Fraction(1, 10**10))
    return error


def main():
    check_identities()
    record = json.loads(TABLE.read_text())
    width = record["width"]
    assert width == 256 and record["denominatorBits"] == 120
    rows = record["polynomials"]
    keys = ("free", "bridge", "trial", "evenCorrection", "oddCorrection")
    assert [len(rows[k]) for k in keys] == [601, 601, 421, 421, 421]
    free, bridge, trial, even, odd = [
        monomial_coefficients(rows[k], 2**record["denominatorBits"]) for k in keys]
    errors = {}
    for label, poly, divisor in (("free", free, 24), ("bridge", bridge, 96)):
        defect = gaussian_defect(poly, width, divisor)
        error = abs(poly[0] - 1) + uniform_bounds(defect, width)[0]
        check(f"{label} Gaussian error", error, Fraction(1, 10**21))
        errors[label] = error

    residual = subtract(free, split_product(bridge, trial))
    value, slope = uniform_bounds(residual, width)
    check("base residual", value, Fraction(2, 10**15))
    check("base residual v derivative", slope, Fraction(4, 10**13))
    check_amplitude_bound(width, rows["trial"], errors["free"], errors["bridge"], value, slope)
    bridge_correction = correction(bridge, width, Fraction(1, 24), Fraction(-1, 1920))
    bridge_term = split_product(bridge_correction, trial)
    for parity, candidate in enumerate((even, odd)):
        free_correction = correction(free, width, Fraction(7-2*parity, 32), Fraction(-1, 120))
        residual = subtract(free_correction, split_product(bridge, candidate), bridge_term)
        value, slope = uniform_bounds(residual, width)
        check(f"parity {parity} correction residual", value, Fraction(3, 10**14))
        check(f"parity {parity} correction v derivative", slope, Fraction(6, 10**12))


if __name__ == "__main__":
    main()
