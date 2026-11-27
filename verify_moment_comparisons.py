"""Certify reflected coefficient comparisons under unimodality in both families."""

from fractions import Fraction as Q
from math import comb, isqrt

from verify import ballot_ranks, direct_ranks, valley
from verify_airy_grid import add
from verify_moments import add as sum_laurents
from verify_moments import collect, moment_polynomials, scale as laurent_scale
from verify_return_bounds import scale, times, weight
from verify_rising import sqrt_hi, sqrt_lo

MIN_INDEX = 96
WITNESSES = (
    ('.262', '.355', '1.0825',
     ('.142', '.215', '.562', '.716', '.873', '1.010', '1.307', '1.578', '1.894')),
    ('.169', '.524', '.9365', ('.335', '1.191')),
)


def evaluate(poly, x):
    return sum(c*x**j for j, c in enumerate(poly))


def upper_on_interval(poly):
    """Upper bound on 0 <= x <= 1/MIN_INDEX, including the constant exactly."""
    return poly[0] + sum(max(c, 0)*Q(1, MIN_INDEX)**j for j, c in enumerate(poly) if j)


def centered_moments(rows, parity):
    """Laurent numerators for K + (3N+1-parity)/2 plus uniform cell noise."""
    orders = [[] for _ in rows]
    for j, poly in enumerate(rows):
        for r in range(j, len(rows)):
            orders[r].append(laurent_scale(poly, comb(r, j)))
            # Apply (3/2) z d/dz + (1-parity)/2 to the full generating numerator.
            poly = collect([(h, c*(Q(3*h, 4)+Q(1-parity, 2))) for h, c in poly.items()]
                           + [(h-2, -c*Q(3*h, 4)) for h, c in poly.items()])
    raw = [sum_laurents(terms) for terms in orders]
    return [sum_laurents(laurent_scale(raw[r-j], Q(comb(r, j), 2**j*(j+1)))
                         for j in range(0, r+1, 2)) for r in range(len(rows))]


def scaled_moments(rows, parity):
    """Ordinary polynomials in 1/N, factoring out the Wallis ratio at odd orders."""
    result = []
    for r, coeffs in enumerate(centered_moments(rows, parity)):
        half_power = 3*r//2
        total = []
        for h, value in coeffs.items():
            if h == 0:
                continue  # Its z^N coefficient vanishes for N >= 1.
            assert h < 0 and (h+r) % 2 == 1
            a = (-h-1-r%2)//2
            assert 0 <= a <= half_power
            term = [Q(value, 2**half_power)]
            for j in range(1, a+1):
                factor = Q(1, j) if r%2 else Q(2, 2*j-1)
                term = times(term, [factor, 1])
            total = add(total, [0]*(half_power-a) + term)
        result.append(total)
    return result


def ratio_difference(poly):
    """Clear the denominator in (1+x)p(x)^2 - (1+x/2)^2 p(x/(1+x))^2."""
    degree = len(poly)-1
    shifted = []
    for j, c in enumerate(poly):
        shifted = add(shifted, [0]*j + scale(weight(degree-j), c))
    return add(times(weight(2*degree+1), times(poly, poly)),
               scale(times([1, 1, Q(1, 4)], times(shifted, shifted)), -1))


def wallis_bounds():
    """Rational polynomial brackets for 4^N / (binom(2N,N) sqrt(2N))."""
    trial = [Q(1)]
    for j in range(1, 10):
        zero = ratio_difference(trial+[0])[j+1]
        one = ratio_difference(trial+[1])[j+1]
        trial.append(-zero/(one-zero))
    lower, higher = trial+[-1], trial+[1]
    for sign, poly in [(1, lower), (-1, higher)]:
        remainder = scale(ratio_difference(poly), sign)
        first = next(j for j, c in enumerate(remainder) if c)
        assert upper_on_interval(remainder[first:]) < 0
        assert upper_on_interval(scale(poly, -1)) < 0
    k = 8192
    ratio = Q(4**k, 128*comb(2*k, k))
    lo = ratio/evaluate(higher, Q(1, k))
    hi = ratio/evaluate(lower, Q(1, k))
    units = 10**23
    return (scale(lower, Q((units*lo).__floor__(), units)),
            scale(higher, Q((units*hi).__ceil__(), units)))


def check_witnesses(moments, bounds):
    margins = [(Q('1e-10'), Q('1e-10')), (Q('1e-5'), Q('7e-6'))]
    for (left, turn, minimum, roots), (area_margin, mean_margin) in zip(WITNESSES, margins):
        a, b, t = map(Q, (left, turn, minimum))
        square_root = [1]
        for root in roots:
            square_root = times(square_root, [-Q(root), 1])
        g = times([b*t, -b-t, 1], times(square_root, square_root))
        assert 0 < a < b < t
        integral = sum(c*(t**(j+1)-a**(j+1))/(j+1) for j, c in enumerate(g))
        assert integral > area_margin
        parts = [[], []]
        for r, c in enumerate(g):
            parts[r%2] = add(parts[r%2], scale(moments[r], c))
        for wallis in bounds:
            assert upper_on_interval(add(parts[0], times(parts[1], wallis))) < -mean_margin
    a, b = map(Q, WITNESSES[0][:2])
    a2, b2 = map(Q, WITNESSES[1][:2])
    assert 2*a == b2 == Q('.524') and a2+b == b2


def check_small_rows(families):
    for m, ranks in ballot_ranks(MIN_INDEX-1):
        n, parity = divmod(m, 2)
        index = n+parity
        twice_shift = 3*index+1-parity
        row = ranks[::-1]
        if n <= 12:
            assert ranks == direct_ranks(range(m-1, 0, -2))
            # The integral over each jittered cell is exact. Remove sqrt(2N)
            # from both sides at odd orders before comparing rational numbers.
            for r, poly in enumerate(families[parity]):
                numerator = sum(count*((2*k+twice_shift+1)**(r+1)
                                       -(2*k+twice_shift-1)**(r+1))
                                for k, count in enumerate(row))
                raw = Q(numerator, (r+1)*2**(r+1)*sum(row))
                expected = evaluate(poly, Q(1, index))*(2*index)**(3*r//2)
                if r%2:
                    expected *= Q(4**index, comb(2*index, index))
                assert raw == expected
        assert valley(row) is None
        limit = isqrt(131**2*(2*index)**3)//250 - twice_shift
        assert limit < len(row)
        for i in range((limit+1)//2):
            assert row[i] <= row[limit-i]
    print('Small reflected comparisons verified in both families through n=95. '
          'All ranks and all 21 moments agree with direct enumeration through n=12.')


def check_induction_window():
    c2 = Q(8, 9)
    combined = 1/sqrt_hi(1/c2 + 1/(8*Q('.524')**2))
    for n, cutoff in [(2049, Q('.1366')), (4096, Q('.1378'))]:
        assert (combined - (1+Q(2, n))/sqrt_lo(n)
                > 2*cutoff*(2+Q(1, n))*sqrt_hi(2+Q(1, n)))


if __name__ == '__main__':
    bounds = wallis_bounds()
    families = [scaled_moments(rows, parity)
                for parity, rows in enumerate(moment_polynomials(20))]
    for family in families:
        check_witnesses(family, bounds)
    print('Both polynomial witnesses certified for each parity at every N >= 96.')
    check_small_rows(families)
    check_induction_window()
    print('The induction window starts at .1366 m^(3/2) for n >= 2049 '
          'and .1378 m^(3/2) for n >= 4096.')
