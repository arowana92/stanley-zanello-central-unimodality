"""Rational bounds for the first-passage estimates in rising-window.md."""

from fractions import Fraction as Q
from math import isqrt
import argparse


PI_LO, PI_HI = Q("3.14159"), Q("3.14160")
M0 = 770


def sqrt_lo(x):
    x = Q(x)
    scale = 10**8
    return Q(isqrt(x.numerator * scale**2 // x.denominator), scale)


def sqrt_hi(x):
    return sqrt_lo(x) + Q(1, 10**8)


def decay(x):
    """Upper bound for exp(-x) from the positive exponential series."""
    term = total = Q(1)
    for j in range(1, 101):
        term *= x / Q(j)
        total += term
    return 1 / total


def exp_small_upper(x):
    """Upper bound for exp(x) at the small positive block exponents."""
    assert 0 <= x <= 2
    term = total = Q(1)
    for j in range(1, 17):
        term *= x / j
        total += term
    return total + term * x / 17 / (1 - x / 18)


def exp_negative_lower(x):
    return 1 - x + x**2 / 2 - x**3 / 6


def drift_bounds(tilt):
    """Enclose tanh(tilt/2) for 0 <= tilt <= 2."""
    lower = 1 / decay(tilt)
    upper = exp_small_upper(tilt)
    return (lower-1)/(lower+1), (upper-1)/(upper+1)


def check_tilt_bounds():
    m = Q(M0)
    assert (1 + 1/m)*(2 + 1/m)/24 < 1/Q("11.9")
    for upper, drift, variance in [
        (Q(1), Q(".463"), Q(".196")),
        (Q("1.5"), Q(".636"), Q(".149")),
        (Q(2), Q(".762"), Q(".104")),
    ]:
        _, high = drift_bounds(upper)
        assert high < drift and (1-high**2)/4 > variance
    for last_label, variance in [(191, Q(".234")), (383, Q(".196"))]:
        _, high = drift_bounds(2*last_label/m)
        assert (1-high**2)/4 > variance
    for upper, lower_p, upper_p in [(Q(1), Q(".36"), Q(".62")), (Q(2), Q(".22"), Q(".68"))]:
        low, high = drift_bounds(upper)
        # -alpha + .98*tanh(alpha/2) decreases with alpha.
        assert 1/(1 + exp_small_upper(upper-Q(".98")*low)) > lower_p
        odds = exp_small_upper(Q(".98")*high)
        assert odds/(1+odds) < upper_p
    assert sqrt_lo(m) > Q("27.74") and Q("1.5")*sqrt_lo(m) > Q("41.62")
    assert (1 - Q("1.063")**2/6)**2 > Q(".65")
    for x, bound in [(Q(1, 2), Q(".45")), (Q(1), Q(".35"))]:
        # sin(y)/y >= 1-y^2/6+y^4/120-y^6/5040, decreasing for 0 <= y <= x.
        assert (1-x**2/6+x**4/120-x**6/5040)**2 / 2 > bound


def gamma_half(n):
    """Upper bound for Gamma(n/2), n a positive integer."""
    if n == 1:
        return sqrt_hi(PI_HI)
    if n == 2:
        return Q(1)
    return Q(n - 2, 2) * gamma_half(n - 2)


def gaussian_moment(j, b):
    return gamma_half(j + 1) / (2 * sqrt_lo(b)**(j + 1))


def gaussian_tail(j, a, b):
    factors = (1 / (2*b*a), 1 / (2*b), a / (2*b) + 1 / (4*b*b*a))
    return decay(b*a*a) * factors[j]


def suffix_tail(B, p, j):
    """Scaled integral outside the innermost arc, for any suffix of length >= B."""
    a = sqrt_lo(p * B / 3)
    inner = gaussian_tail(j, a, Q(".35")) + gaussian_tail(j, 2*a, 2 / PI_HI**2)
    middle = (Q(".30") * sqrt_hi(B) * 8 * PI_HI)**(j+1) * decay(p*B/2) / (j+1)
    outer = 2**j * (Q(".30") * B * sqrt_hi(B))**(j+1) * decay(15*p*B/16)
    return (inner + middle) / PI_LO + outer


def check_suffixes():
    for B, p in [(95, Q(".234")), (192, Q(".196")), (384, Q(".104"))]:
        for j in range(3):
            bound = gaussian_moment(j, Q(".45")) / PI_LO + suffix_tail(B, p, j)
            limit = Q(".46") if j < 2 else (Q("1.6") if B == 95 else Q(".56"))
            assert bound < limit
    for j in (0, 1, 2):
        a = sqrt_lo(Q(".104") * 736 / 3)
        tail = suffix_tail(736, Q(".104"), j) + gaussian_tail(j, a, Q(".5")) / PI_LO
        assert tail + Q(".00001") < Q(".002")
    assert gaussian_moment(1, Q(".45")) / PI_LO + Q(".002") < Q(".37")


# Frequency thresholds for nearest-integer spacings. Rates are per step.
ARCS = [
    (Q(1, 8), Q(".18"), 25, Q(".99"), Q(".013"), Q(".012")),
    (Q(".18"), Q(1, 4), 17, Q(".99"), Q(".019"), Q(".016")),
    (Q(1, 4), Q(1, 2), 13, Q(".98"), Q(".022"), Q(".019")),
    (Q(1, 2), PI_HI, 6, Q(".75"), Q(".028"), Q(".019")),
]


def check_blocks():
    for small in (True, False):
        p, upper = (Q(".36"), Q(".62")) if small else (Q(".22"), Q(".68"))
        mixed = Q(".20") if small else Q(".12")
        for x in (p, upper):
            for y in (p, upper):
                a, b = x*(1-y), y*(1-x)
                assert 2*a*b / (a+b) >= mixed
        loss = Q(".56") if small else Q(".41")
        rho = decay(mixed * Q(".65") * 4**3 / 4)
        assert (1 + rho) * exp_small_upper(loss) < 2
        scale = Q(".054") if small else Q(".039")
        assert (Q(7,8)-Q(1,24)-Q(1,M0))*loss / Q("8.5") > scale
        for lo, hi, length, sine_sq, fast, slow in ARCS:
            assert PI_HI / lo + Q(1, 2) < length + 1
            rate = fast if small else slow
            rho = decay(mixed * length * sine_sq)
            assert (1+rho) * exp_small_upper(2*length*rate) < 2


def late_bound(j, prefix, kappa, small):
    scale = Q(".054") if small else Q(".039")
    base = 3 * Q(".30")**(j+1) * gamma_half(3*(j+1)) / (PI_LO * sqrt_lo(scale)**(3*(j+1)))
    for lo, hi, _, _, fast, slow in ARCS:
        rate = fast if small else slow
        volume = 2 * (Q(".30")*M0*sqrt_hi(M0))**(j+1) * (hi**(j+1)-lo**(j+1)) / ((j+1)*PI_LO)
        exponent = rate * (Q(7,8)-prefix) * M0
        assert exponent > Q(3*(j+1),2)  # polynomial times exponential decreases
        base += volume * decay(exponent)
    return base * decay((Q(".49")*kappa)**2 / 2)


def first_hit_bound(j, divisor, prefix, gamma, kappa, dmax):
    result = Q(0)
    for v, end in [(Q(1,divisor), Q(1,8)), (Q(1,8), Q(1,4)), (Q(1,4), Q(1,2))]:
        b = v + Q(1,M0)
        z = decay((Q(".1075")*(1-b)**2 - b*b/8)*gamma**2*v)
        loss = z * Q(".81")*(1+dmax) / (2*(1-prefix)*kappa*sqrt_lo(v))
        norm = Q(".46") if j < 2 else Q(".56")
        result += loss * norm / sqrt_lo(1-end-Q(1,M0))**(3*(j+1))
    for v, end in [(Q(1,2), Q(5,8)), (Q(5,8), Q(3,4)), (Q(3,4), Q(13,16)), (Q(13,16), Q(7,8))]:
        loss = decay((kappa*v*(1-v/2))**2 / (2*(end+Q(1,M0))))
        norm = Q(".46") if j < 2 else Q("1.6")
        result += loss * norm / sqrt_lo(1-end-Q(1,M0))**(3*(j+1))
    return result


def check_case(divisor, gamma, kappa, dmax, p, small):
    gamma, kappa, dmax, p = map(Q, (gamma, kappa, dmax, p))
    # sqrt(m)*tanh(gamma/(2*sqrt(m))) is increasing in m.
    t = decay(gamma / sqrt_hi(M0))
    assert sqrt_lo(M0) * (1-t)/(1+t) > kappa
    prefix = Q(1,divisor) + Q(1,M0)
    sig = sqrt_lo(p*(1-prefix)**3 / 3)
    a = sqrt_lo(p*(1-prefix)*M0 / 3)
    v = kappa / sqrt_hi(divisor)
    ratio = (1 + (1 + decay(v*v/2))/v)/(1-prefix)
    variance = prefix * ((1+ratio)*Q("1.649")/2 - 1) / (2*sig**2)

    def approximation(j):
        return ((Q(".187")*dmax/a*gaussian_moment(j+3,Q(".45"))
                 + Q(".047")/a**2*gaussian_moment(j+4,Q(".45"))) / PI_LO
                + Q(".002"))

    def loss(j):
        return first_hit_bound(j, divisor, prefix, gamma, kappa, dmax) + late_bound(j, prefix, kappa, small)

    if divisor == 24:
        mass = Q(".3989")*exp_negative_lower(variance/2) - approximation(0) - loss(0)
        difference = Q(".37") + loss(1)
        assert mass > Q(".21") and difference < Q(".70")
        assert Q(".997")*sig*gamma*mass - difference > Q(".20")
    else:
        central = variance/(1+variance/2) - exp_negative_lower(variance/2)
        assert central < 0
        curvature = Q(".3989") * central + approximation(2) + loss(2)
        assert curvature < -Q(".01")


def check_constants():
    check_tilt_bounds()
    check_suffixes()
    check_blocks()
    check_case(24, "17.85", "8.62", ".463", ".196", True)
    check_case(24, "27.74", "12.81", ".762", ".104", False)
    check_case(48, "23.80", "11.21", ".463", ".196", True)
    check_case(48, "27.74", "12.81", ".636", ".149", False)
    check_case(48, "41.62", "17.61", ".762", ".104", False)
    print("Verified suffix bounds, block damping and all five first-passage cases.")


def check_exact(n):
    from verify_middle import rank_window

    for m in (2*n, 2*n+1):
        degree = m*m//4
        for a, b in ((3,2), (2,1)):
            corank = isqrt((a*a*m**3-1)//(b*b)) + 1
            rank = degree-corank
            if rank < (degree+1)//2:
                continue
            left, center, right = rank_window(m, rank-1, rank+1)
            if right <= center or (a == 2 and center**2 <= left*right):
                raise ArithmeticError(f"failed at {m=}, {rank=}")
            print(f"length {m}, rank {rank}, corank boundary {a}/{b} checked", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact-n", type=int, help="check the boundary ranks at this row count")
    args = parser.parse_args()
    check_constants()
    if args.exact_n is not None:
        if args.exact_n < 1:
            parser.error("--exact-n must be positive")
        check_exact(args.exact_n)
