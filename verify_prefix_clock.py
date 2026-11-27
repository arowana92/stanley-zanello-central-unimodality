"""Rational checks for the shorter-walk and first-hit estimates."""

from fractions import Fraction as Q
from itertools import product
from math import comb

from verify_rising import PI_HI, PI_LO, decay, exp_small_upper, sqrt_hi, sqrt_lo
from verify_variation import BANDS, CUTOFFS

MIN_M = 2 * 10**17
EPS = 1 / sqrt_lo(MIN_M)


def check_first_hit():
    for length in range(1, 12):
        counts = [0] * (length + 1)
        for signs in product((-1, 1), repeat=length):
            height = lowest = 0
            edge_sum = 0
            for i, step in enumerate(signs):
                previous = height
                height += step
                edge_sum += min(previous, height)
                if i + 1 < length:
                    lowest = min(lowest, height)
            if height < lowest:
                counts[-height] += 1
            # Four times the symmetric edge area, with starting height zero.
            assert 2*edge_sum == -length + sum(
                (2*(length-i)-1)*step for i, step in enumerate(signs))
        for distance in range(1, length + 1):
            expected = (distance * comb(length, (length - distance) // 2)
                        if (length - distance) % 2 == 0 else 0)
            assert length * counts[distance] == expected

    # Uniform point mass of the hitting time on its parity class.
    assert (2 * Q(201, 199) * exp_small_upper(Q(1, 201)) * decay(1)
            / PI_LO < Q(".49")**2)
    # Natural parameters change the two mixed pair probabilities only slightly.
    lower, upper = Q(".4999"), Q(".5001")
    assert 2 * lower**4 / (2*upper**2) * (1-Q(".01")**2/6)**2 > Q(".99")/4
    c = Q(".99") * 9**3 / 96
    rounding = exp_small_upper(Q(".000001"))
    rho = rounding * decay(c)
    hit = decay(c * Q(".9")**3)
    for i in range(10, 100):
        a, b = Q(i, 100), Q(i+1, 100)
        hit += Q(".49") * (Q(".005") + Q(1, 10**6)) / a * decay(c * (1-b)**3)
    assert rounding * hit < Q(".171") and rho < Q(".00055")
    assert (Q(".171")+Q(".00055")) * exp_small_upper(Q(".19")*Q("9.01")*64/63) < 1

    for y, divisor, p, rate in [(40, 12, 10, ".15"), (60, 12, 14, ".16"),
                                (40, 48, 19, ".17")]:
        variance = Q("9.01")**3 / (divisor*y*y)
        # Allow the positive-tilt starting factor also in the negative-tilt row.
        allowed = 1 / exp_small_upper(Q(".001") + Q(rate)*Q("9.01")*64/63)
        remainder = allowed - Q(".00055") * exp_small_upper(variance/2)
        assert remainder > 0
        assert Q(".171")**(p-1) * exp_small_upper(p*variance/2)**p < remainder**p
    assert 16 * exp_small_upper(Q(".19")*Q("9.01")*64/63) < 100
    assert 8 * exp_small_upper(Q(".16")*Q("9.01")*64/63) / Q(".7")**2 < 100
    assert 52 * exp_small_upper(Q(".17")*Q("9.01")*64/63) < 300


def check_peak():
    rate, cutoff = Q(".19"), 1250
    scaled = (100*rate)**3 * cutoff**2
    z100 = next(i for i in range(10000) if i**3 >= scaled)
    lo, hi = Q(z100-1, 100), Q(z100, 100)
    for i, target in enumerate((".000013", ".012", "12.6")):
        b = Q(3*(i+1), 2)
        main = Q(10000, MIN_M)/PI_LO * sum(
            Q(c*cutoff**(i+j+1), i+j+1) for j,c in enumerate((1,2,1)))
        tail = (300/PI_LO * sqrt_hi(1/rate)**(3*(i+1)) * decay(lo)
                * sqrt_hi(hi)**(3*(i+1)-2)/(1-(b-1)/lo))
        assert main + tail + Q(1, 10**10) < Q(target)
    assert 11*Q("1.78")/exp_small_upper(Q(1,12))-10**9*EPS > Q("12.6")
    assert 13*sqrt_lo(6/PI_HI)/exp_small_upper(Q(13,8))**4-3300000*EPS > Q(".012")
    for q in (1, 7):
        exponent = Q(".65")*q + Q(q*q,24) + 12*Q("1.501")*EPS + 6*EPS**2
        assert Q("1.78")*q/exp_small_upper(exponent/4)**4 > Q(".012")
    # The old full-period envelope controls the difference multipliers.
    assert 8*Q(3,2)*100**5*12*EPS**3 < Q(1,10**10)
    assert 8*Q(3,2)*100**8*2000*EPS**6 < Q(1,10**10)


def check_tails():
    for rate, hmin, max_z, margin, prefactor in [
        (".17", 7, 25, 25, 300), (".15", 13, 92, 27, 100)
    ]:
        rate, z = Q(rate), Q(max_z)
        integral = (Q("1.5")*(z+1)/(sqrt_lo(rate)**3*5)
                    + Q("1.5015")*(z*z+2*z+2)/(hmin*rate**3))
        assert 8*prefactor*decay(Q(margin))*integral < Q(".003")
    # At r=8 the intermediate-frequency table already permits a cutoff of 25.
    N, cost = Q(".49")*64, Q(0)
    for i, (y, _, _, rate) in enumerate(BANDS):
        if Q(y) < 25:
            continue
        upper = Q(BANDS[i+1][0]) if i+1 < len(BANDS) else 150
        envelope = min(20000*decay(Q(rate)*(N-4)), Q("1.03")*decay(Q(rate)*(N-20)))
        cost += 12*8/Q(".21")*(upper-Q(y))*(1+Q("1.001")*upper)*envelope
    assert cost < Q(".022")
    # Beyond theta=10^-9 the weakest full-period exponent already exceeds
    # 10^7 after extracting half for integration.
    assert Q(MIN_M, 2*4000*10**6) > 10**7
    assert 10**6 * 3**100 * 8000**5 * 2000 * decay(10**7) < Q(1,10**12)


def check_clock():
    assert (exp_small_upper(Q(1))**39 < MIN_M and 1/decay(40) > MIN_M)
    assert 175**3 < (60*39)**2 and (60*40)**2 < 180**3
    assert sqrt_lo(MIN_M)/60 > 7000000
    assert Q(1,4)-Q(1,4*7000000)-Q("1.305")/175 > Q(".22")
    assert Q(".45")/2-Q("1.30")*Q("1.001")/175 > Q(".21")
    assert Q(175**2,8192*60**2)>Q(1,10**7)
    assert 5*60**3*EPS < Q(".01")
    assert Q("9.49")**2/(2*Q("1.001")) > 44
    assert Q("2.01") > 2*Q("1.001")
    assert Q(".5") + Q("3.01")/2 + Q(".76")*Q("2.01") < 4
    assert Q(".5") + 1 + Q(".76") < Q("2.27")
    for j in range(70, 180):
        lo, hi = Q(j,10), Q(j+1,10)
        coarse = 2*(1+Q(".084")*hi**2+64)
        height = sqrt_hi(Q("2.01")*coarse) + Q(".00001")
        cutoff = sqrt_hi((25/Q(".17"))**3)
        assert cutoff/hi >= 40
        check_interval(hi, coarse, height, cutoff, cutoff/lo, 0)

    for j in range(235, 700):
        lo, hi = Q(j,100), Q(j+1,100)
        hlo, hhi = max(13,lo**3), hi**3
        if hhi < hlo:
            continue
        rate, min_ratio = (Q(".16"), 60) if hi <= 4 else (Q(".15"), 40)
        B = min(hhi/2,Q("1.31")*hi*hi)
        cutoff = sqrt_hi(((27+B)/rate)**3)
        low_B = min(hlo/2,Q("1.31")*lo*lo)
        assert ((27+low_B)/rate)**3 >= (min_ratio*hhi)**2
        check_interval(hhi, B+64, Q("10.00001"), cutoff, cutoff/hlo, hi)

    bands = [(7,8,35),(8,9,25)] + CUTOFFS[1:]
    for start,end,ratio in bands:
        for j in range(20*start,20*end):
            lo, hi = Q(j,20), Q(j+1,20)
            height = (10 if lo<21 else 180/lo) + Q(".00001")
            check_interval(hi**3, Q("1.31")*hi**2+64, height, ratio*hi**3, ratio, hi)


def check_interval(h, coarse, height, cutoff, ratio, r):
    R = max(50, r)
    vc = 2*sqrt_hi(coarse)
    assert 5*vc < R**2 and Q("2.01")*vc*EPS < Q(".001")
    assert 2*h*(4+4*vc*height)*EPS < 2
    assert (h + 3*R**2)*EPS < Q(".0006")
    shift = (4+Q("4.54")*height*sqrt_hi(41))*EPS
    u = h*shift + 3*EPS*R**2
    t = Q("1.001")*ratio
    loss = (u*exp_small_upper(u*u)*(Q("1.76")+Q("1.63")*t)
            + exp_small_upper(u)*shift*cutoff*(Q("1.63")+Q("1.69")*t))
    assert u < Q(".14") and loss < Q(".95"), (float(h),float(loss))
    assert cutoff < 500000 and ratio < 500


if __name__ == "__main__":
    check_first_hit()
    check_peak()
    check_tails()
    check_clock()
    print("Verified first-hit, shorter-walk and inversion bounds at every n >= 10^17.")
