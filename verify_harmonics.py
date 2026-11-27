"""Exact endpoint and small-block checks for two-harmonics.md."""

from fractions import Fraction as Q
from itertools import product

from verify_rising import PI_LO, PI_HI, decay, exp_small_upper, sqrt_hi, sqrt_lo


def phase_powers(count):
    """Powers of exp(i theta / 2) for one rational point on the unit circle."""
    result = [(Q(1), Q(0))]
    for _ in range(count):
        x, y = result[-1]
        result.append(((24*x-7*y)/25, (7*x+24*y)/25))
    return result


def check_retained_rows():
    for pairs in range(1, 6):
        phases = phase_powers(2*pairs*(2*pairs+6))
        radii = [((1+abs(phases[d*pairs][0]))/2)**pairs for d in (1, 2)]
        bound = (radii[0]+sqrt_lo((1+radii[1])/2))/2
        for start in (0, 2, 6):
            by_end = {}
            for steps in product((-1, 1), repeat=2*pairs):
                height, action = start, 0
                for step in steps:
                    action += min(height, height+step)
                    height += step
                    if height < 0:
                        break
                else:
                    x, y = phases[action]
                    w = Q(9,10)**action / 4**pairs
                    a, b = by_end.get(height, (0, 0))
                    by_end[height] = a+w*x, b+w*y
            assert sum(sqrt_hi(a*a+b*b) for a, b in by_end.values()) < bound


def check_boundary_identity():
    for radius in (Q(1,3), Q(9,10)):
        for index in range(9):
            # Finite-support basis vector, with room on both sides of its last edge.
            v = [int(i == index) for i in range(12)]
            def apply_transfer(values, j):
                down = radius**(j-1)*values[j-1] if j else 0
                return down + radius**j*values[j+1]
            shifted = v[1:]
            for j in range(10):
                assert apply_transfer(v,j+1)-radius*apply_transfer(shifted,j) == (v[0] if j == 0 else 0)


def check_spectrum():
    h = 10**12
    angle = PI_LO/(Q("1.5")*h+1)
    assert h**2*(angle-angle**3/6)**2 > Q("4.30")
    assert (1-Q("2.60")/h**2)*(Q("1.5")-Q("1.5")**2/(2*h**2)) > Q("1.48")
    norm = 2+Q("2.60")/Q(".74")
    assert norm < Q("5.52") and Q(".16")*norm < Q(".884")
    overlap = Q(".08")*norm/(1-Q(".08")*norm)
    assert -Q("1.97")*(1-overlap**2)+Q(".624")*overlap**2 < -Q(".32")
    inner, outer = Q(".000000076"), Q(".000086")
    assert (inner/2)**25 > Q(12,h)**17  # exponent .68
    assert (outer/2)**5 > Q(12,h)**2     # exponent .40
    assert inner/Q(".04") < Q(".001")
    err2 = 2*inner/Q(".04")**2
    assert Q(2,9)*Q("1.65")-err2 > Q(".35")
    assert Q(2,9)*Q("2.60")+err2 < Q(".60")
    assert Q(8,27)*Q("2.60")/Q(".99")**3+6*inner/Q(".03")**3 < 1
    assert Q(1,9)-Q(56,81)*Q(".08")**2/24 > Q(".109")
    assert (inner+Q(12,h))/Q(".01")**2 < Q("1.65")*Q(".109")-Q(".12")
    assert (outer+Q(12,h))/Q(".04")**2 < Q("1.65")*Q(".109")-Q(".12")


def check_saddle():
    nblocks = 2*10**7
    z = Q(".2499")**3*45**2/16
    retained = (decay(z)+sqrt_hi((1+decay(4*z))/2))/2
    assert exp_small_upper(Q("2.61")/4)*retained < Q(".815")
    for end, rate in [(1, Q(".000345")), (45, Q(".00009"))]:
        assert Q("3.99")*Q(".185")/(45+end)**2 > rate
    dmin = sqrt_lo(Q(".35")*nblocks)
    y = 6/dmin
    err = 216/(6*Q(".35")*dmin)
    assert Q(".001")+160*y < Q(".365")
    amp = exp_small_upper(401*(Q(".30")*y*y+y**3/6))
    assert amp*Q(".366")+(amp-1) < Q(".37")
    assert 1-Q(".37")-Q("1.37")*(exp_small_upper(err)-1) > Q(".57")
    assert Q("1.002")*exp_small_upper(401*(Q(".30")*Q(".01")**2+Q(".01")**3/6)) < Q("1.02")
    assert Q("1.001")*(12+Q(".7"))/Q(".08") < 160
    assert 103*exp_small_upper(Q("5.23")/4)**4*exp_small_upper(Q(".34")*401*Q(".08")**2) < 1/decay(11)

    # Gaussian tail after y=.08, retaining its polynomial prefactor.
    c = Q(".000345")*nblocks
    a = Q(".08")
    d = sqrt_hi(Q(".60")*nblocks)
    volume = d/(2*c*a)+d**3*(a/(2*c)+1/(4*c*c*a))
    assert 2*volume*decay(c*a*a-20) < Q(".001")

    s = Q("1.65")/3
    assert 6500**2*(2*s-Q(".001"))**2 / ((s+Q(".003"))**2*Q("2.001")**3) > nblocks


def check_fourier_tails():
    # For small positive tilts use the gamma integral at i=2 to bound
    # the weight 1+xi^2 by 2 xi^2, on both sides for both transforms.
    for rate, zmin, zmax, excess, pref in (
        (Q(".035"), 350, 350, 350, 4*1252),
        (Q(1,150), 105, 107, 73, 24),
        (Q(1,150), 444, 7800, 149, 16),
    ):
        bound = (12*pref*sqrt_hi(1/rate)**9*sqrt_hi(zmax)**7*decay(Q(excess))
                 / (1-Q(7,2*zmin)))
        assert bound < Q(".001")
    assert Q(2000000)**2 > (105*150)**3
    assert Q(10000)**2 > (Q("3.09")*150)**3
    assert Q("3.09")*12**2-Q("1.31")*15**2 > 149
    assert Q(".00009")*Q(".49") > Q(".000044")
    assert Q(".000033")*2000**2 == 132
    assert 4*10**8*6500**6*decay(Q(132-20)) < Q(".001")
    assert 8*(1+10**4*6500**3)**3*decay(Q(".73")*Q(".49")*50**2-20) < Q(".001")


def check_bounded_height():
    n = 10**88
    variance_floor = Q(".000002")
    assert 2*Q(1,3)/512**2 > variance_floor
    assert 2*Q(".19")**2/3**8 > variance_floor
    sigma = sqrt_lo(variance_floor*n)
    assert 16/sigma < Q(1,10**39)
    assert 3*10**27*n*(16/sigma)**3/6 < Q(".001")
    assert 4*10**17*16/sigma < Q(".001")
    assert Q(".99")/(3**8*(1+Q(1,3**8))**2*PI_HI**2) > Q(".00001")
    assert Q(".00001")*n/10**78 > 1000
    assert 10**10*(1+10**8*10**44)**3*decay(Q(10**5)) < Q(".001")


def check_inversion():
    # Bounds at the largest tilt radius, before the decrease in epsilon.
    for n, order in ((10**46, 0), (10**46, 1), (10**88, 2)):
        eps = 1/sqrt_lo(2*n)
        pref = 6*PI_HI*(2,5,11)[order]*eps
        r = 6500
        cutoff = 2000*r*r
        large = pref*60*r*r*(1+r**3+2*cutoff)*cutoff**order
        if order == 1:
            large /= r**3
        negative = pref*600*1250**2*(1+1250+2*10**6)*10**(6*order)
        small = pref*600*50**2*(1+50**3+2*1250*10**6)*(1250*10**6)**order
        if order == 1:
            negative = pref*600*2500*(1+1250+2*10**6)*10**6
            small = pref*600*50**2*(2*10**6+1250*10**6+2*125*10**11)
        assert max(large, negative, small) < (Q(".31"), Q(".24"), Q("11.8"))[order]
    assert 2*(Q(".24")+Q(".011")) < 1-Q(".31")-Q(".011")
    for r, tilt, t, weight in [(1250,1250,10**6,600),(50,50**3,1250*10**6,600),
                               (6500,6500**3,2000*6500**2,60)]:
        assert weight*r**2*(Q(".1")+Q("2.002")*tilt+Q("3.003")*t)/sqrt_lo(2*10**46) < Q(".05")


if __name__ == "__main__":
    check_retained_rows()
    check_boundary_identity()
    check_spectrum()
    check_saddle()
    check_fourier_tails()
    check_bounded_height()
    check_inversion()
    print("Two harmonics, spectral estimates, signed integrals and both size thresholds verified.")
