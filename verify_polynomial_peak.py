"""Enclose the first two Fourier derivatives of the polynomial trial.

Run after verify_gamma_polynomials.py. All decisions use rational arithmetic.
The integration variable w satisfies xi=w^3 and v=w^2. Composite Simpson
quadrature handles 0 <= w <= 8, with a uniform allowance for 8 <= w <= 16.
"""

from fractions import Fraction as Q
from math import ceil, comb, factorial, floor

from verify_gamma_polynomials import (
    chebyshev_coefficients, derivative_coefficients, monomial_coefficients, read_rows,
)


FREQUENCY_MESH = 256
SPACE_MESH = 4096
SCALE = 2**120
WINDOWS = ((1, Q(".1359"), Q(".339"), 1),
           (2, Q(".333"), Q(".404"), -1),
           (1, Q(".398"), Q(".631"), -1))


def restricted_norms(power, lower, upper, count):
    """Bounds for F and its derivatives on the specified interval in v."""
    # Horner substitution z=(lower+(upper-lower)t)/256 with integer arithmetic.
    degree = len(power) - 1
    result = [power[-1]]
    for j in range(degree-1, -1, -1):
        following = [lower*c for c in result] + [0]
        for k, c in enumerate(result):
            following[k+1] += (upper-lower)*c
        following[0] += power[j] << (8*(degree-j))
        result = following
    common = SCALE << (8*degree)
    row, denominator = chebyshev_coefficients([Q(c, common) for c in result])
    norms = []
    for order in range(count):
        norms.append(Q(sum(map(abs, row))*2**order, denominator*(upper-lower)**order))
        row = derivative_coefficients(row)
    return norms


def product(left, right):
    """First five coefficients of the product of two Taylor series."""
    return [sum(left[i]*right[k-i] for i in range(k+1)) for k in range(5)]


def integrand_fourth(order, end, norms):
    """Leibniz bound at each point of the bin ending at w=end."""
    exponent = 3*order+2
    weight = [3*comb(exponent, k)*end**(exponent-k) for k in range(5)]
    # Taylor majorant for F((w+h)^2) with increment 2wh+h^2.
    area = [0]*5
    change = [0, 2*end, 1, 0, 0]
    power = [1, 0, 0, 0, 0]
    for i, norm in enumerate(norms):
        for k in range(5):
            area[k] += power[k]*norm/factorial(i)
        power = product(power, change)
    # Absolute coefficients of exp(i*x*((w+h)^3-w^3)) for |x| <= 1.
    phase = [0, 3*end**2, 3*end, 1, 0]
    exponential = [Q(1)]
    for k in range(1, 5):
        exponential.append(sum(i*phase[i]*exponential[k-i] for i in range(1, k+1))/k)
    return 24*product(product(weight, area), exponential)[4]


def quadrature_cost(power):
    bins = [restricted_norms(power, a*a, (a+1)**2, 5) for a in range(8)]
    tail = restricted_norms(power, 64, 256, 1)[0]
    costs = {}
    for order in (1, 2):
        simpson = sum(integrand_fourth(order, a+1, norms) for a, norms in enumerate(bins))
        # Taylor's cubic at the midpoint of a two-step panel. Integrating
        # the fourth-order remainder and charging both endpoint remainders
        # gives the conservative global factor 1/45.
        simpson /= 45*FREQUENCY_MESH**4
        # The second derivative in x adds a factor w^6. Integrate the weight exactly.
        curvature = sum(norms[0]*Q((a+1)**(3*order+9)-a**(3*order+9), order+3)
                        for a, norms in enumerate(bins))
        interpolation = curvature/(8*SPACE_MESH**2)
        omitted = tail*Q(4096**(order+1)-512**(order+1), order+1)
        # Each node has absolute amplitude <=2, phase error <=8H/D, and
        # amplitude rounding error <=1/D. Bound every weight by its largest.
        rounding = Q(24*8**(3*order+2)*(16*SPACE_MESH+2), SCALE)
        costs[order] = simpson+interpolation+omitted+rounding
        print(f"order {order} quadrature, interpolation, trial tail: "
              f"{float(simpson):.6g}, {float(interpolation):.6g}, {float(omitted):.6g}", flush=True)
    return costs


def scaled_at_node(power, k):
    """Exact dyadic Horner evaluation at z=k^2/(256 J^2), rounded once."""
    denominator = 256*FREQUENCY_MESH**2
    shift = denominator.bit_length()-1
    assert 1 << shift == denominator
    result = power[-1]
    for i, c in enumerate(reversed(power[:-1]), 1):
        result = result*k*k + (c << (shift*i))
    return result >> (shift*(len(power)-1))


def rotation(angle):
    """Dyadic sine and cosine of an angle in [0,1/8], within 2/D each."""
    assert 0 <= angle <= Q(1, 8)
    assert Q(1, 8)**29/factorial(29) < Q(1, SCALE)
    cosine, sine = Q(0), Q(0)
    term = Q(1)
    for i in range(29):
        if i % 2 == 0:
            cosine += (-1)**(i//2)*term
        else:
            sine += (-1)**(i//2)*term
        term *= angle/(i+1)
    return floor(SCALE*cosine), floor(SCALE*sine)


def node_values(power):
    last = max(ceil(right*SPACE_MESH) for _, _, right, _ in WINDOWS)
    accum = {1: [0]*(last+1), 2: [0]*(last+1)}
    j = FREQUENCY_MESH
    assert j % 2 == 0 and 8*SPACE_MESH < SCALE
    for k in range(8*j+1):
        f = scaled_at_node(power, k)
        c, s = rotation(Q(k**3, j**3*SPACE_MESH))
        weight = 1 if k in (0, 8*j) else (4 if k % 2 else 2)
        # Minus sine for the first derivative and minus cosine for the second.
        first = -weight*k**5*f
        second = -weight*k**8*f
        x, y = SCALE, 0
        for i in range(last+1):
            accum[1][i] += first*y
            accum[2][i] += second*x
            x, y = (x*c-y*s)//SCALE, (x*s+y*c)//SCALE
    return accum


def omitted_lattice_tail():
    # On the inner arc use u=xi^(2/3), u^(7/2) <= u^4, and
    # (256+y)^4 <= 256^4 exp(4y/256).
    rate = Q(157, 1000)
    argument = rate*256
    exp_lower = sum(argument**i/factorial(i) for i in range(101))
    inner = 150*256**4 / (exp_lower*(rate-Q(4, 256)))
    # The 216-step bound is 16 exp(.0078*216-.0078*(63/64)*m).
    # m >= N, pi*S <= 12N^2, exp(2) < 9, exp(N/200) >= (N/200)^8/8!.
    n_min = 10**54
    assert Q(78, 10000)*216 < 2 and Q(78, 10000)*Q(63, 64) > Q(1, 200)
    outer = Q(16*9*12**3*factorial(8)*200**8, n_min**2)
    total = inner+outer
    assert total < Q(1, 1000)
    return total


def main():
    row = read_rows()["trial"]
    power = [int(c) for c in monomial_coefficients(row, 1)]
    assert sum(map(abs, row)) < 2*SCALE
    costs = quadrature_cost(power)
    values = node_values(power)
    high_frequencies = omitted_lattice_tail()
    for order, left, right, sign in WINDOWS:
        lo, hi = floor(left*SPACE_MESH), ceil(right*SPACE_MESH)
        raw = min(sign*value for value in values[order][lo:hi+1])
        raw = Q(raw, FREQUENCY_MESH**(3*order+3)*SCALE**2)
        trial_margin = raw - costs[order]
        # The compact-frequency conditional amplitude error is <= 10^-10.
        lattice = Q(4096**(order+1), (order+1)*10**10)
        margin = trial_margin-lattice-high_frequencies
        print(f"order {order}, {float(left)}..{float(right)}: "
              f"trial margin {float(trial_margin):.9g}, lattice allowance {float(lattice):.9g}, "
              f"full margin {float(margin):.9g}", flush=True)
        if margin <= Q(1, 100):
            raise ArithmeticError("insufficient lattice sign margin")


if __name__ == "__main__":
    main()
