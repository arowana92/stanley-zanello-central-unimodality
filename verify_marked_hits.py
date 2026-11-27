"""Rational first-difference and curvature certificates for marked-excursion bounds."""

from fractions import Fraction as Q
from math import ceil, comb

from verify import ballot_ranks, direct_ranks
from verify_hit_tilts import M, c2, drift, eps, exp_bound
from verify_rising import (ARCS, PI_HI, PI_LO, decay, exp_negative_lower,
                           gaussian_moment, gaussian_tail, sqrt_hi, sqrt_lo, suffix_tail)

H = Q(37, 40)
SHIFTS = (0, 1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32)
UNIT = 10**18


def up(x):
    """Round upward on a fixed grid after integration or exponentiation."""
    return Q(ceil(x * UNIT), UNIT)


def check_suffix():
    for low, high in ((255, 512), (512, 1024), (1024, 2048), (2048, 4096), (4096, 4096)):
        u = Q(57*high, 128*M)
        p = (1-u*u)/4
        a = sqrt_lo(p*low/3)
        sigma = a * low
        for r, limit in enumerate((Q(".007"), Q(".0138"), Q(".030"))):
            err = (Q(".187")*u/a*gaussian_moment(r+3,Q(".45")) +
                   Q(".047")/a**2*gaussian_moment(r+4,Q(".45")))/PI_LO
            err += (suffix_tail(low,p,r) + gaussian_tail(r,a,Q(".5"))/PI_LO)
            if r == 1:
                err += gaussian_moment(2,Q(".5"))/(2*PI_LO*sigma)
            if r == 2:
                err += gaussian_moment(4,Q(".5"))/(12*PI_LO*sigma**2)
            assert err < limit
    assert 1/sqrt_lo(2*PI_LO) < Q(".399")
    # Lattice errors in completing the square for a changed rank tilt.
    u = Q(32, M*64)
    exp_u = 1/(1-u)
    assert (1+exp_u)/(2*(1-u)) <= Q("1.001")
    assert 1/(1-u)**2 < Q("1.001")
    assert ((exp_u+1)**2/4-1)/(1-u)**2 < Q(".0002")
    assert Q(".030")+Q(".399") == Q(".429")
    assert 2*Q("1.001")*Q(".0138") < Q(".028")
    assert Q("1.001")*Q(".007")+Q(".0002")*Q(".399") < Q(".0072")
    assert 2/(2-u*u) < Q("1.001")  # 2(cosh(u)-1)/u^2 by the even series.
    # Substitute x=sin(theta) in the point norm; the far arc starts at x=3/5.
    assert Q(1)/(1-Q(3,5)**2) <= (1+Q(3,5)**2)**2
    for steps, p, bound in [(80,Q(".238"),Q(".831")), (255,Q(".235"),Q(".84"))]:
        central = (1+1/(4*p*steps))/sqrt_lo(2*PI_LO*p)
        far = sqrt_hi(steps)*exp_bound(-2*p*steps*Q(3,5)**2)
        assert central+far < bound


def fourier_norms(fraction):
    span = H-fraction-eps
    zs = sqrt_hi((1-fraction+eps)**3/12)
    endpoints = [Q(0), Q(1)]
    while endpoints[-1] < 4096:
        endpoints.append(min(Q(4096), up(endpoints[-1]*Q("1.04")+Q(".25"))))
    integrals = [Q(0)]*3
    for lo, hi in zip(endpoints, endpoints[1:]):
        best = Q(1)
        for b in range(1, 65):
            width = span/b-2*eps
            angle = hi*(H-fraction+eps)/(128*b)
            if angle > Q("1.4") or width <= 0:
                continue
            energy = Q(".20")*lo**2*(width**3-width*eps**2)/24
            if energy <= 0:
                continue
            ex1 = energy*(1-angle**2/6)**2
            ex2 = 4*energy*max(0,1-(2*angle)**2/6)**2
            block = Q(3,8)+exp_bound(-ex1)/2+exp_bound(-ex2)/8
            best = min(best, up(block**b))
        for r in range(3):
            integrals[r] += up(best*(hi**(r+1)-lo**(r+1))/(r+1))
    # At theta <= 1/8, 2*ceil(3.5 theta^(-2/3)) consecutive labels.
    first = (1-Q(15,16)**2/6)**2
    second = (1-Q(15,8)**2/6)**2
    block = (Q(3,8)+exp_bound(-Q(".2")*first*Q("3.5")**3/4)/2
             + exp_bound(-Q(".2")*second*Q("3.5")**3)/8)
    assert block < exp_negative_lower(Q(".65"))
    rate = span*Q(".65")/Q("7.5")
    for r in range(3):
        b = Q(3*(r+1),2)
        lower = rate*256  # 4096^(2/3)
        assert lower > b-1
        # t=4096*(x/lower)^(3/2); (x/lower)^(b-1) <= exp((b-1)*(x/lower-1)).
        tail = (3*4096**(r+1)*exp_bound(-lower)/(lower-(b-1)))
        integrals[r] = up(zs**(r+1)*(integrals[r]+tail)/PI_LO)
        for lo, hi, _, _, rate_hi, _ in ARCS:
            assert rate_hi*span*M > b
            volume = 2*(zs*M*sqrt_hi(M))**(r+1)*(hi**(r+1)-lo**(r+1))/((r+1)*PI_LO)
            integrals[r] += up(volume*decay(rate_hi*span*M))
    return integrals


def first_hit_losses(g, top, fraction, z_hi, denom):
    """Bound the signed contributions from contacts through the cut H."""
    early = [Q(0), Q(0)]
    left = fraction
    while left < H+2*eps:
        end = min(H+2*eps, left+Q(1,256))
        v, e = left-eps, end+eps
        count = (end-left)/2
        best = [None,None]
        for shift in SHIFTS:
            lam = top+shift
            b = lam*e/4
            energy = (shift**2*c2/8 -
                      v*(1-e/2)**2*(g+shift)*(g*(1-g*g*eps/6)+shift)/8)
            norm = exp_bound(energy)
            if norm is None:
                continue
            pinned = None
            for split in (3,5,8):
                outer = v/split-2*eps
                inner = v*(1-Q(2,split))-eps
                assert inner*M >= 80
                if outer*M < 40:
                    continue
                front = 2*b+Q(".8")*exp_bound(-b*b*outer/2)/sqrt_lo(outer)
                cost = front**2*(Q(1,2)+b/128)*Q(".831")/sqrt_lo(inner)*norm
                pinned = cost if pinned is None else min(pinned,cost)

            assert pinned is not None
            y = lam*e*sqrt_hi((e+eps)/2)/2
            saving = (g+shift)**2*v*(v*v-eps**2)/96*(1-(lam*e/256)**2/6)
            marked_norm = exp_bound(energy+lam*e/256-saving+y*y/4)
            if marked_norm is not None:
                mgf = 1+y*(sqrt_hi(PI_HI)/2+min(sqrt_hi(PI_HI),y)/2)
                marked = Q(".8")*mgf*marked_norm/sqrt_lo(v-eps)**3
                pinned = min(pinned,marked)
            prob = count*pinned/denom
            z = sqrt_lo((1-(lam*(1-v)/128)**2)*(1-e)**3/12)
            ratio = z_hi/z
            w = lam*z
            root_lo = 2/(sqrt_hi(w*w+4)+w)
            root_hi = 2/(sqrt_lo(w*w+4)+w)
            mixed = Q(".399")*(w+root_hi)*exp_bound(-root_lo**2/2)
            signed = ratio**2*(mixed+Q(".0138")+w*Q(".007"))
            tilt_width = shift*z
            # Complete the square in the normal density and its two derivatives.
            bend = ratio**3*(Q(".429")+Q(".028")*tilt_width+Q(".0072")*tilt_width**2)
            costs = (Q("1.001")*signed, bend)
            for r in range(2):
                val = up(prob*costs[r])
                if best[r] is None or val < best[r]:
                    best[r] = val
        for r in range(2):
            early[r] += best[r]
        left = end
    return early


def late_hit_losses(g, top, fraction, z_hi, denom, norms):
    """Use endpoint reflection and the killed-prefix Fourier integrals."""
    late = [None, None]
    i0, i1, i2 = norms
    for shift in SHIFTS:
        a = (drift(g)+Q(shift,2))*H*(1-H/2)
        u = (top+shift)/2-a
        assert (g+shift)/2 >= a
        if max(a,u) > Q(".24")*64:
            continue
        norm = exp_bound(shift**2*c2/8-a*a/2)
        if norm is None:
            continue
        # Reflection, followed by summation of a span-two geometric series.
        reflection = min(1, Q(".84")/(a*sqrt_lo(1-H-eps)))
        prob = norm*reflection*(2*u+Q(".8")*exp_bound(-u*u*fraction/2)/sqrt_lo(fraction))/denom
        w = shift*z_hi
        bend = i2+min(Q("2.002")*w*i1,Q("1.001")*w*w*i0)
        costs = (Q("1.001")*(i1+(top+shift)*z_hi*i0), bend)
        for r in range(2):
            val = up(prob*costs[r])
            if late[r] is None or val < late[r]:
                late[r] = val
    return late


def signs(g, top, fraction, norms):
    f = fraction+eps
    z_lo = sqrt_lo((1-(top/128)**2)*(1-f)**3/12)
    z_hi = sqrt_hi((1-fraction+eps)**3/12)
    denom = 2*drift(g)*(1-f)/(1+top/128)
    V = (f+(1+top/128)/(1-f)*(f*f+1/(2*drift(g)**2)))/(4*z_lo**2)
    gaussian = exp_negative_lower(V/2)
    mass = Q(".3989")*gaussian-Q(".005")
    central = V/(1+V/2)-gaussian
    assert central < 0
    assert mass > 0
    early_first, early_second = first_hit_losses(g, top, fraction, z_hi, denom)
    late_first, late_second = late_hit_losses(g, top, fraction, z_hi, denom, norms)
    first, second = early_first + late_first, early_second + late_second
    return (Q(".999")*g*z_lo*mass-Q(".25")-first,
            -(Q(".3989")*central+Q(".010")+second))


def check_peak_bound():
    # After division by ell^3 the variance numerator has positive coefficients
    # in 1/ell. Both parity bounds are largest at the indicated lower limit.
    ell = Q(128)
    constant = Q(472,15)-9*PI_LO
    for parity, rest in enumerate(((Q(228,5)-12*PI_LO)/ell +
                                   (Q(344,15)-4*PI_LO)/ell**2 + 4/ell**3,
                                   Q(44,15)/ell + Q(8,5)/ell**2)):
        variance = (constant+rest)/(16*(2-parity/ell)**3)
        assert (12*variance+Q(1,256**3))*Q("1.805")**2 < 1
    assert Q(".79")**2*PI_HI*(1+Q(2,256)) < 2
    assert Q(".78")**2*PI_HI*(1+Q(2,50)) < 2
    p = (1-Q(9,256))/4
    a = sqrt_lo(p*229/3)
    point_error = (Q(".187")*Q(3,16)*gaussian_moment(3,Q(".45"))/a+
                   Q(".047")*gaussian_moment(4,Q(".45"))/a**2)/PI_LO
    point_error += suffix_tail(229,p,0)+gaussian_tail(0,a,Q(".5"))/PI_LO
    assert Q(".399")+point_error < Q(".410")
    x = Q(9,20)
    e_hi = exp_bound(-x)
    e_lo = exp_negative_lower(x/4)**4
    tail = Q(".8")*e_hi
    for i in range(2,21):
        tail -= Q(".78")*e_lo**(i-1)*(1-e_hi)/sqrt_hi(i)
    survival = (6+tail/sqrt_lo(Q(1,10)))/Q(".79")
    z = sqrt_lo(p*(Q(9,10)-Q(1,256))**3/3)
    cost = Q(36,48)*(1+Q(1,256))*(2+Q(1,256))
    for corank, level in [(Q(3,5), 1), (Q(18,25), Q(1,2))]:
        bound = Q(".410")*survival*exp_bound(cost-6*corank)/z
        assert bound < Q("1.805")*level
    print("Mode below 3/5 and upper half-maximum boundary below 18/25 for m >= 256.")


def check_rows(max_n=127, direct_n=12):
    growth = curvature = 0
    for m, ranks in ballot_ranks(max_n):
        degree = len(ranks)-1
        peak = max(ranks)
        if m//2 <= direct_n and direct_ranks(range(m-1,0,-2)) != ranks:
            raise ArithmeticError(f"direct partition counts disagree at {m=}")
        for j, count in enumerate(ranks):
            k = degree-j
            if (5*k)**2 >= 9*m**3 and count == peak:
                raise ArithmeticError(f"mode bound failed at {m=}, {k=}")
            if (25*k)**2 >= 324*m**3 and 2*count >= peak:
                raise ArithmeticError(f"half-maximum bound failed at {m=}, {k=}")
            if 2*j < degree:
                continue
            if (5*k)**2 >= 9*m**3:
                assert ranks[j+1] > count
                growth += 1
            if (4*k)**2 >= 9*m**3:
                assert count**2 > ranks[j-1]*ranks[j+1]
                curvature += 1
    print(f"Exact rows through n={max_n}: {growth} growth and {curvature} curvature checks. "
          f"Direct partitions agree through n={direct_n}.")


def centered_first_hit(d):
    """Exact first-hit probability at 2d+1 for the slope log(2)."""
    surviving = {0: Q(1)}
    normalizer = Q(1)
    for index in range(2*d+1):
        up_weight = Q(2)**(d-index)
        step_total = up_weight + 1/up_weight
        normalizer *= step_total
        p_up = up_weight / step_total
        hit = surviving.get(0, 0) * (1-p_up)
        following = {}
        for height, mass in surviving.items():
            following[height+1] = following.get(height+1, 0) + mass*p_up
            if height:
                following[height-1] = following.get(height-1, 0) + mass*(1-p_up)
        surviving = following
    return hit, normalizer


def check_marked(max_d=10):
    for d in range(max_d+1):
        counts = [0]*(d+1)
        area_weight = 0

        def visit(path, ups):
            nonlocal area_weight
            height = path[-1]
            if len(path) == 2*d+1:
                area_weight += 2**sum(path)
                for y in path:
                    counts[y] += 1
                return
            if ups < d:
                visit(path+[height+1],ups+1)
            if height:
                visit(path+[height-1],ups)

        visit([0],0)
        for h in range(d+1):
            assert sum(counts[h:]) == comb(2*d+1,d-h)
        hit, normalizer = centered_first_hit(d)
        assert hit * normalizer == 2**d * area_weight
    print(f"Marked heights and exact tilted first-hit probabilities agree through semilength {max_d}.")


if __name__ == "__main__":
    check_suffix()
    check_marked()
    check_peak_bound()
    cases = [(Q(3, 5), Q(9), 0, Q(3, 40)), (Q(3, 4), Q("11.25"), 1, Q(1, 16))]
    for start, stop, order, fraction in cases:
        bounds = fourier_norms(fraction)
        print("Scaled late Fourier integrals:",*[round(float(x),4) for x in bounds],flush=True)
        g = start*Q("11.99")
        margins = []
        while g < stop:
            top = min(stop,g+Q(1,8))
            margin = signs(g,top,fraction,bounds)[order]
            if margin <= 0:
                raise ArithmeticError(f"order {order+1}, {float(g)=}, {float(top)=}, {float(margin)=}")
            margins.append(margin)
            g = top
        print(f"Order {order+1}, corank >= {start} m^(3/2), minimum margin > "
              f"{int(1000*min(margins))/1000:.3f}",flush=True)
    check_rows()
