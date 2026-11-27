"""Rational endpoint checks and finite block checks for holder-blocks.md."""

from fractions import Fraction as Q
from itertools import product
from math import comb

from verify_harmonics import phase_powers
from verify_rising import (PI_LO, PI_HI, decay, exp_negative_lower,
                           exp_small_upper, gamma_half, gaussian_tail,
                           sqrt_hi, sqrt_lo)


def check_path_blocks():
    # W=(9/10)^(5*action) makes W^(6/5) rational on every surviving path.
    for pairs in range(1, 6):
        phases = phase_powers(2*pairs*(6+2*pairs))
        radii = [((1+abs(phases[d*pairs][0]))/2)**pairs for d in range(13)]
        harmonic = sum(comb(24, 12+d)*radii[abs(d)] for d in range(-12, 13))/2**24
        for vector in ((1, 1, 1, 1), (1, 4, 3, 2), (1, 0, 2, 1)):
            norm2 = sum(a*a for a in vector)
            lhs = tilted = 0
            for i, a in enumerate(vector):
                endpoints = {}
                for word in product((-1, 1), repeat=2*pairs):
                    h, action = 2*i, 0
                    for step in word:
                        action += min(h, h+step)
                        h += step
                        if h < 0:
                            break
                    else:
                        if h//2 >= len(vector):
                            continue
                        mass = Q(a*vector[h//2], 4**pairs)
                        x, y = phases[action]
                        weight = mass*Q(9, 10)**(5*action)
                        u, v = endpoints.get(h, (0, 0))
                        endpoints[h] = u+weight*x, v+weight*y
                        tilted += mass*Q(9, 10)**(6*action)
                lhs += sum(sqrt_hi(u*u+v*v) for u, v in endpoints.values())
            assert lhs**6 < tilted**5 * norm2 * harmonic


def check_block_bound():
    b = Q(6, 5)
    z = Q(".999")**3*Q("4.5")**2/16
    moment = (comb(24, 12)+2*sum(comb(24, 12+d)*decay(d*d*z)
                                  for d in range(1, 13)))/Q(2**24)
    assert Q(".941")**3 < 1/b
    exponent = Q("2.60")*(1-Q(".941"))+Q(20, 10**7)
    assert exp_small_upper(6*exponent)*moment < Q(".924")**6
    for end, rate in ((".2", ".0034"), ("1", ".00249"), ("4.5", ".00093")):
        assert Q(".996")*Q(".076")/(Q("4.5")+Q(end))**2 > Q(rate)
    assert Q(".996")*Q(".076") > Q(".075")


def check_spectral_disk():
    h = 10**7
    angle = PI_LO/(Q("1.5")*h+1)
    assert h**2*(angle-angle**3/6)**2 > Q("4.30")
    assert (1-Q("2.60")/h**2)*(Q("1.5")-Q("1.5")**2/(2*h*h)) > Q("1.48")
    error = Q(".000189")
    assert (error/2)**25 > Q(12,h)**17
    err2 = 2*error/Q(".04")**2
    assert Q(2,9)*Q("1.65")-err2 > Q(".13")
    assert Q(2,9)*Q("2.60")+err2 < Q(".82")
    assert Q(8,27)*Q("2.60")/Q(".99")**3+6*error/Q(".03")**3 < 44
    assert Q(".13")/2-44*Q(".003")/6 > Q(".04")
    assert Q(".92")**4*(Q(".92")/Q(".82"))**3 > 1
    assert 103*exp_small_upper(Q("5.23")/4)**4*exp_small_upper(
        Q(".46")*401*Q(".08")**2) < 1/decay(12)
    assert Q("1.001")*(1+12+Q(".7"))/Q(".08") < 180


def half_tail(a, b):
    return gaussian_tail(0, Q(a), Q(b)) + gaussian_tail(2, Q(a), Q(b))


def check_saddles():
    for large in (True, False):
        nblocks = 1700000 if large else 10**11
        low, high = (Q(".35"), Q(".60")) if large else (Q(".13"), Q(".82"))
        cubic, lipschitz = (1, 160) if large else (44, 180)
        v = Q(".08") if large else Q(".003")
        core = 3 if large else 6
        d = sqrt_lo(low*nblocks)
        high_d = sqrt_hi(high*nblocks)
        loss = cubic*core**3/(6*low*d)
        assert (1-Q(".002")-lipschitz*core/d
                -Q("1.002")*(exp_small_upper(loss)-1)) > Q(".35" if large else ".85")
        central_end = Q(".01") if large else v
        central_rate = (1-Q(401,nblocks))*(Q(1,2)-cubic*central_end/(6*low))
        assert central_rate > Q(".49" if large else ".32")
        if large:
            assert Q(".01")*d > Q("7.7")
            assert (1-Q(401,nblocks))*Q(".12")/high > Q(".199")
            assert 2*Q("1.002")*(half_tail(3,".49")+half_tail("7.7",".199")) < Q(".12")
            damping = Q(".0034")*nblocks
            volume = (high_d/(2*damping*v)
                      +high_d**3*(v/(2*damping)+1/(4*damping**2*v)))
            assert 2*volume*decay(damping*v*v-20) < Q(".001")
            middle_rate = Q(".00249")*Q(".2")**2
        else:
            assert 2*Q("1.002")*half_tail(6,".32") < Q(".001")
            middle_rate = Q(".0034")*v*v
        volume = 2*(1+10**4*high_d)**3
        assert volume*(decay(middle_rate*nblocks-20)+decay(Q(".16")*nblocks-20)) < Q(".001")
        # In the remaining stretched exponential substitute t=y^(2/3).
        moments = Q(3,2)*(gamma_half(3)+gamma_half(9))
        assert 2*high_d*(1+high_d**2)*moments*decay(Q(nblocks*400,160)-20) < Q(".001")
        assert Q("1.002")*exp_small_upper(loss)*2/(2*Q(".49"))+1 < 10
    for i in (0, 2):
        assert sqrt_lo(2*PI_LO)-2*gaussian_tail(i, Q(3), Q(1,2)) > Q("2.3")
    assert Q(".35")*Q(".99")*Q("2.3")-Q(".132") > Q(".5")
    assert 1900**2*(Q("1.10")-Q(".001"))**2/(
        Q("2.001")**3*Q(".555")**2) > 1700000


def check_cutoffs():
    # The bounds below include both laws, both signs of frequency, and
    # the possible factor 1.4 in the unnormalized lattice mass.
    rate = Q(".035")
    for lower_z, upper_z, excess, prefactor in (
        (75, 76, 75, 4*1252), (138, 140, 106, 24), (350, 8750, 55, 16)
    ):
        assert lower_z > 0
        assert 12*prefactor*(upper_z**2+2*upper_z+2)*decay(Q(excess))/rate**3 < Q(".001")
    for T, low_z, high_z in ((10**5,75,76), (250000,138,140)):
        assert low_z**3 < rate**3*T**2 < high_z**3
    assert Q("3.5")*100-Q("1.31")*225 > 55
    assert Q(".49")*Q(".00093") > Q(".000455")
    assert Q(".49")*Q(".00249") > Q(".00122")
    for lower, rate, slope, target in (
        (500, Q(".000455"), Q("1.001")/50, Q(".001")/500**2),
        (170, Q(".00122"), Q(".0021"), Q(".00009")),
    ):
        assert (12*decay(rate*lower**2-20)*(Q(1,lower)+slope)
                /(2*rate) < target)
    assert 12*10**4*50**3*(1+Q("1.001")*10**4)*decay(Q(".075")*Q(".49")*50**2-20) < Q(".001")
    z = 6000
    assert Q(10**4*50**3)**2 > (170*z)**3
    assert 36*170**3*(z*z+2*z+2)*decay(Q(z-20)) < Q(".001")


def check_kernel():
    norms = []
    for i, variation in enumerate((4, 10, 28, 60)):
        a = Q(2**(i+2)-1,(i+1)*(i+2))/PI_LO
        b = variation/(2*PI_LO)
        norms.append(4*sqrt_hi(a*b))
        assert a < 1
    assert norms[0]+norms[2]/9 < Q("2.81")
    assert norms[1]+norms[3]/9 < Q("4.06")


def check_clock_and_sign():
    eps = 1/sqrt_lo(2*10**36)
    def upper_sinh(u):
        return (exp_small_upper(u)-exp_negative_lower(u))/2
    for r, T, ratio in (
        (4,250000,250000), (10,10**6,Q(10**6,64)), (50,125*10**6,1000),
        (500,125*10**6,10), (1900,170*1900**2,Q(170,1900)),
    ):
        X = Q("1.31")*max(15,r)**2+424
        eta = Q("9.36")*eps*X
        u = (eta+eps)*(r**3+3*T)+3*eps*max(50,r)**2
        assert u < Q(".28")
        assert upper_sinh(u)*(Q("2.81")+Q("4.06")*Q("1.001")*ratio) < Q(".88")
    X = 2*(1250+Q(1250**2,4)+424)
    u = eps*((Q("9.36")*X+1)*(1250+3*10**5)+3*1250**2)
    X_ratio = 2*(1+Q(1250,4)+424)
    u_ratio = eps*((Q("9.36")*X_ratio+1)*(1250+3*10**5)+3*2500)
    assert upper_sinh(u)/u*(Q("2.81")*u+Q("4.06")*Q("1.001")*10**5*u_ratio) < Q(".002")
    assert exp_small_upper(Q(".28"))+3*eps**8 < Q("1.4")
    assert exp_negative_lower(Q(".28"))-3*eps**8 > Q(".7")
    assert 18*eps**8*7*10**8*(1+Q("1.001")*7*10**8) < Q(".001")
    assert 4*(2*7*10**8)**3*eps**3 < Q(".001")


if __name__ == "__main__":
    check_path_blocks()
    check_block_bound()
    check_spectral_disk()
    check_saddles()
    check_cutoffs()
    check_kernel()
    check_clock_and_sign()
    print("Verified the two-tilt blocks, both saddle ranges, inversion tails and 10^36 size bound.")
