"""Rational sign bounds with separate label and height tilts for first hits."""

from fractions import Fraction as Q
from functools import lru_cache

from verify import ballot_ranks, direct_ranks
from verify_rising import (ARCS, PI_LO, PI_HI, decay, gamma_half, gaussian_moment,
                           gaussian_tail, sqrt_hi, sqrt_lo, suffix_tail)

M = 4096
eps = Q(1, M)
h = Q(15, 16)
c2 = (1 + eps) * (2 + eps) / 6
shifts = (0, 1, 2, 4, 6, 9, 12, 16, 20, 24, 28, 32)


@lru_cache(maxsize=None)
def exp_grid(index):
    """Upper bound for exp(-index/1024), including arbitrarily small probabilities."""
    unit = 10**24
    # 1 + 1/1024 <= exp(1/1024). Round up after each product.
    base = (1024 * unit + 1024) // 1025
    result = unit
    while index:
        if index % 2:
            result = (result * base + unit - 1) // unit
        base = (base * base + unit - 1) // unit
        index //= 2
    return Q(result, unit)


def exp_bound(exponent):
    if exponent > 0:
        return None  # This candidate need not be used.
    return exp_grid((-1024 * exponent).__floor__())


def drift(g):
    """Lower bound for sqrt(m) tanh(g/(2 sqrt(m)))."""
    return g / 2 * (1 - g*g*eps / 12)


def main_suffix_bounds():
    assert 4 / c2 > Q("11.99")
    assert Q(25, 12) * (1 - Q(625, 12*M)) - (1+eps)/(4*sqrt_lo(M)) > 2
    # All first-hit suffixes have length at least M/16 - 1.
    assert (1 - Q(57, 128)**2) / 4 > Q(".196")
    # Bound the unrestricted core point mass at the matching endpoint.
    assert (1 - (Q(57, 256)*(h + eps))**2) / 4 > Q(".238")
    assert 1 / sqrt_lo(2 * Q(".238") * PI_LO) * Q(6, 5) + Q(".001") < 1
    # exp(-2*w*r*sin(1)^2) sqrt(r) is decreasing from r=80.
    assert sqrt_hi(80) * exp_bound(-2*Q(".238")*80*Q(5,6)**2) < Q(".001")
    # Gaussian approximation of the main suffix and its first two differences.
    B = 3685
    p = Q(".24")
    a = sqrt_lo(p*B/3)  # sigma / B
    max_drift = Q(25,128)
    for r, tol in enumerate((Q(".005"), Q(".007"), Q(".010"))):
        tail = suffix_tail(B, p, r) + gaussian_tail(r, a, Q(".5")) / PI_LO
        err = (Q(".187")*max_drift/a * gaussian_moment(r+3,Q(".45"))
               + Q(".047")/a**2 * gaussian_moment(r+4,Q(".45"))) / PI_LO
        multiplier = Q(".0001") if r else 0
        assert tail + err + multiplier < tol
    assert Q(".2421")**2 * 2 * PI_LO > exp_bound(-Q(1))
    assert (1-Q(25,128)**2)/4 > p


def middle_losses(g, top, fraction, denom, z_hi):
    losses = [Q(0)] * 3
    v = fraction
    while v < h:
        end = min(h, v + Q(1, 80))
        # t is an odd hitting time in (ceil(vm), ceil(end*m)].
        e = end + eps
        chunk = v/3 - 2*eps
        assert chunk * M >= 80
        count = (end-v)/2 + eps
        best = [None] * 3
        for delta in shifts:
            lam = top + delta
            b = lam*e/4
            front = 2*b + Q(".8")/sqrt_lo(chunk)
            back = (Q(1,2) + b/128) * front
            pin = 1 / sqrt_lo(chunk)
            exponent = (delta**2 * c2/8
                        - v*(1-e/2)**2 * (g+delta)*(g*(1-g*g*eps/6)+delta)/8)
            norm = exp_bound(exponent)
            if norm is None:
                continue
            prob = count * front * back * pin * norm / denom
            z = sqrt_lo((1 - (lam*(1-v)/128)**2) * (1-e)**3 / 12)
            ratio = z_hi / z
            mass = Q(".46") * ratio
            diff = Q(".46") * ratio**2
            curv = Q(".56") * ratio**3
            # First difference upper bound and centered second difference lower bound.
            d = Q("1.001") * delta * z_hi
            vals = (mass, Q("1.001")*diff + d*mass, curv + 2*d*diff)
            for r, val in enumerate(vals):
                cost = prob * val
                if best[r] is None or cost < best[r]:
                    best[r] = cost
        for r in range(3):
            losses[r] += best[r]
        v = end
    return losses


def fourier_integrals(fraction, z_hi):
    span = h - fraction - eps
    eta = span * Q(".56") / Q("8.5")
    bounds = []
    for r in (0, 1, 2):
        base = (3 * z_hi**(r+1) * gamma_half(3*(r+1)) /
                (PI_LO * sqrt_lo(eta)**(3*(r+1))))
        for lo, hi, _, _, rate, _ in ARCS:
            volume = 2*(z_hi*M*sqrt_hi(M))**(r+1) * (hi**(r+1)-lo**(r+1))/((r+1)*PI_LO)
            assert rate*span*M > Q(3*(r+1),2)
            # Analytic exponential here must decay faster than a fixed absolute floor.
            base += volume * decay(rate*span*M)
        bounds.append(base)
    return bounds


def late_losses(g, top, fraction, denom, z_hi):
    i0, i1, i2 = fourier_integrals(fraction, z_hi)
    best = [None] * 3
    for delta in shifts:
        a = (drift(g) + Q(delta,2)) * h * (1-h/2)
        # Maximum absolute single-step natural parameter in the auxiliary prefix.
        umax = (top + delta)/2 - a
        assert (g + delta)/2 - a >= 0
        if max(a, umax) > Q(".24")*64:
            continue  # Only use the .36--.62 pair-probability block estimate.
        assert (1-Q(".24"))/2 >= Q(".36") and (1+Q(".24"))/2 <= Q(".62")
        norm = exp_bound(delta**2 * c2/8 - a**2/2)
        if norm is None:
            continue
        prob = norm * (2*umax + Q(".8")/sqrt_lo(fraction)) / denom
        d = Q("1.001") * delta * z_hi
        for r, val in enumerate((i0, Q("1.001")*i1+d*i0, i2+2*d*i1)):
            cost = prob * val
            if best[r] is None or cost < best[r]:
                best[r] = cost
    return best


def case(g, top, divisor):
    fraction = Q(1, divisor)
    f = fraction + eps
    z_lo = sqrt_lo((1-(top/128)**2)*(1-f)**3 / 12)
    z_hi = sqrt_hi((1-fraction+eps)**3 / 12)
    kappa = drift(g)
    denom = 2*kappa*(1-f)/(1+top/128)
    V = (f + (1+top/128)/(1-f)*(f*f + 1/(2*kappa**2))) / (4*z_lo**2)
    # Alternating Taylor lower bound for exp(-V/2).
    x = V/2
    gauss = 1-x+x*x/2-x**3/6
    early = middle_losses(g, top, fraction, denom, z_hi)
    late = late_losses(g, top, fraction, denom, z_hi)
    mass = Q(".3989")*gauss-Q(".005")-early[0]-late[0]
    diff = Q(".25")+early[1]+late[1]
    central = V/(1+V/2)-gauss
    assert central < 0
    curvature = Q(".3989")*central + Q(".010") + early[2]+late[2]
    assert mass > 0
    return Q(".999")*z_lo*g*mass-diff, curvature


def check_coefficients(max_n=96, direct_n=10):
    growth_tests = curvature_tests = 0
    for m, ranks in ballot_ranks(max_n):
        if m // 2 <= direct_n and direct_ranks(range(m-1, 0, -2)) != ranks:
            raise ArithmeticError(f"direct partition counts disagree at {m=}")
        degree = len(ranks) - 1
        for j in range((degree+1)//2, degree):
            k = degree - j
            if (4*k)**2 >= 9*m**3:
                if ranks[j+1] <= ranks[j]:
                    raise ArithmeticError(f"rank growth failed at {m=}, {j=}")
                growth_tests += 1
            if (16*k)**2 >= 225*m**3:
                if ranks[j]**2 <= ranks[j-1]*ranks[j+1]:
                    raise ArithmeticError(f"curvature failed at {m=}, {j=}")
                curvature_tests += 1
    print(f"Exact rows through n={max_n}: {growth_tests} increasing steps, "
          f"{curvature_tests} positive determinants. Direct partitions agree through n={direct_n}.")


def check():
    main_suffix_bounds()
    for divisor, start, order in ((10, Q(3,4), 1), (14, Q(15,16), 2)):
        g = start * Q("11.99")
        margins = []
        while g < 25:
            top = min(Q(25), g + Q(1,2))
            growth, curvature = case(g, top, divisor)
            margin = growth if order == 1 else -curvature
            if margin <= 0:
                raise ArithmeticError(f"order {order}, gamma in [{g}, {top}], margin {float(margin)}")
            margins.append(margin)
            g = top
        print(f"Order {order}, corank >= {start} m^(3/2), "
              f"minimum certified margin > {int(1000*min(margins))/1000:.3f}")
    check_coefficients()


if __name__ == "__main__":
    check()
