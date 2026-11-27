"""Rational endpoint checks for centered-displacement.md."""

from fractions import Fraction as Q

from verify_rising import PI_HI, decay, exp_small_upper, sqrt_hi, sqrt_lo
from verify_variation import CUTOFFS

M0 = 2 * 10**16
EPS = 1 / sqrt_lo(M0)
HEIGHT = Q("10.00001")


def check_duration():
    radius = Q(".001")
    k = Q(1, 6)-Q(".0001")
    # cos(sqrt(2v)) = 1-v+v^2/6+..., with absolute tail from degree 3.
    assert radius/90/(1-radius/28) < Q(".0001")
    scale = 1 + k*radius
    assert -k + scale**2/(2*(1-scale*radius)) < Q(".336")
    assert Q("1.16")**2 >= 4*Q(".336")
    # For |t/m-1| <= .001, t*|1-(m/t)^(3/2)| / |t-m|.
    assert 1 + 1/(2*Q(".999")*sqrt_lo(Q(".999"))) < Q("1.51")
    assert (Q(".5")+1+Q("1.01"))/2 < Q("1.26")


def check_range():
    assert Q("2.339")/(3*31) + Q("2.7")/31**2 < Q(1,35)
    assert sqrt_lo(6/PI_HI)/exp_small_upper(Q(13,8))**4 > Q(".002")
    assert Q(".002")*exp_small_upper(Q("1.5"))**4 < Q("1.78")
    assert Q(".002")*6/Q(".65") > Q(".015")
    assert Q(".15")*12*Q(".009") > Q(".015")
    assert 1/decay(38) > M0 and EPS < Q(".000001")
    assert HEIGHT > 10 + 5*EPS
    assert sqrt_lo(M0)/31 > 4500000
    # Even the crude real-energy remainder 20/H fits the allowance.
    assert Q(20,4500000) < Q(".00001") and 100*150 < 3*4500000
    assert Q(M0, 8000*10**6) >= 2*10**6
    assert 10**6 * 3**1000 * 8000**5 * 2000 * decay(10**5)**20 < Q(1,10**10)
    assert 2*100*decay(38)*500000*501 < Q(".001")
    assert 4*(2*500000)**3*EPS**3 < Q(".001")


def check_interval(hmax, coarse_x, cutoff, ratio):
    # R=50 at M0. Products involving log(m) times epsilon decrease hereafter.
    coarse_v = 2*sqrt_hi(coarse_x)
    assert coarse_v*5 < 2500 and Q("2.01")*coarse_v*EPS < Q(".001")
    assert 2*hmax*(4+4*coarse_v*HEIGHT)*EPS < 2
    assert (hmax + 3*2500)*EPS < Q(".0006")
    assert Q("1.16")*sqrt_hi(41)*EPS/Q(".672") < Q(".001")
    shift = (4+Q("1.26")*Q("1.16")*HEIGHT*sqrt_hi(41))*EPS
    u = hmax*shift + 3*EPS*2500
    t = Q("1.001")*ratio
    loss = (u*exp_small_upper(u*u)*(Q("1.76")+Q("1.63")*t)
            + exp_small_upper(u)*shift*cutoff*(Q("1.63")+Q("1.69")*t))
    assert u < Q(".14") and loss < Q(".963"), (float(hmax), float(loss))
    assert cutoff < 500000 and ratio < 500


def check_bands():
    for j in range(235, 700):
        lo, hi = Q(j,100), Q(j+1,100)
        hlo, hhi = max(13,lo**3), hi**3
        if hhi < hlo:
            continue
        rate, min_ratio = (Q(".16"), 60) if hi <= 4 else (Q(".15"), 40)
        B = min(hhi/2, Q("1.31")*hi*hi)
        cutoff = sqrt_hi(((27+B)/rate)**3)
        low_B = min(hlo/2, Q("1.31")*lo*lo)
        assert ((27+low_B)/rate)**3 >= (min_ratio*hhi)**2
        check_interval(hhi, B+63, cutoff, cutoff/hlo)

    for start, end, ratio in [(7,8,35),(8,9,25)] + CUTOFFS[1:]:
        for j in range(20*start,20*min(end,31)):
            hi = Q(j+1,20)
            check_interval(hi**3, Q("1.31")*hi**2+63, ratio*hi**3, ratio)
    assert Q(".963")+Q("1.01")*(Q(".022")+Q(".003")+Q(".001"))+Q(".002") < 1


if __name__ == "__main__":
    check_duration()
    check_range()
    check_bands()
    print("Verified centered clock bounds and all positive-tilt bands from n=10^16.")
