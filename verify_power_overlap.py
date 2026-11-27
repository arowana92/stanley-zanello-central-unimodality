"""Rational inequalities for the peak comparison at n >= 10^22."""

from fractions import Fraction as Q
from math import comb

from verify_rising import PI_LO, PI_HI, decay, exp_small_upper, sqrt_hi, sqrt_lo


M = 2*10**22


def check_fair_peak():
    t = 4000
    rate = Q(".12")
    zl, zh = Q("30.23"), Q("30.24")
    assert zl**3 < rate**3*t*t < zh**3
    tail = 120/PI_LO/rate**3*decay(zl)*zh**2/(1-2/zl)
    central = Q(10000,M)/PI_LO*(Q(t**2,2)+Q(2*t**3,3)+Q(t**4,4))
    assert central+tail+Q(1,10**12) < Q(".000012")
    lower = Q("1.78")
    assert lower/exp_small_upper(6*Q("1.37")**2/10)**10 > Q(".000012")
    assert 12*(Q("1.37")-Q(".65"))*lower/exp_small_upper(6*Q("1.501")**2/10)**10 > Q(".000012")
    assert sqrt_lo(6/PI_HI)/exp_small_upper(1)**10-3300000/sqrt_lo(M) > Q(".000012")
    assert Q(10**9)/sqrt_lo(M) < Q(".01")


def check_height():
    assert exp_small_upper(1)**51 < M < 1/decay(Q(52))
    assert 210**3 < (60*51)**2 and (60*52)**2 < 215**3
    assert Q(210**2,8192*100**2) > Q(1,10**7)
    assert Q(1,4)-Q(1,4*10**9)-Q("1.305")/210 > Q(".22")
    assert Q(".45")/2-Q("1.30")*Q("1.001")/210 > Q(".21")
    assert 5*100**3/sqrt_lo(M) < Q(".01")
    assert 20000*decay(Q("1.48")*(Q("4.5")**2/2-Q("2.01"))) < Q(".20")
    assert Q(".08")*Q("4.5") > Q(".35")
    assert Q("2.60")/300+Q(7,10000) < Q(".01")
    # Real moment comparison at r >= 100.
    assert Q("1.06")*Q("1.001")/Q(".999")*exp_small_upper(Q(".34")/2) < 8


def check_blocks():
    # c, Holder exponent, frequency, certified rate per H^2, upper bound
    # on 1-b^(-1/3) for the conjugate Holder exponent b.
    for c,p,y,rate,q in ((".45",2,20,".72",".207"),(".5",2,15,".50",".207"),
                         (".7",3,10,".28",".127"),(".25",2,45,"1.60",".207")):
        c, rate, q = Q(c), Q(rate), Q(q)
        assert (1-q)**3 < Q(p-1,p)
        z = (Q(".999")*c)**3*y*y/16
        moment = (comb(4*p,2*p)+2*sum(comb(4*p,2*p+j)*decay(j*j*z)
                                     for j in range(1,2*p+1)))/Q(2**(4*p))
        assert moment*exp_small_upper(c*(rate+Q("2.60")*q+Q(".00001"))*p) < 1
    assert Q(12*10**4,10**9) < PI_LO
    # Two boundaries of ceil(H^2) pairs for r >= 11. Each cost decreases
    # with r beyond the indicated minimum.
    for r,rate in ((11,Q(".72")),(15,Q(".50")),(20,Q(".28"))):
        n = Q(".49")*r*r
        assert 12*20000*r**3*45*(1+Q("1.001")*45)*decay(rate*(n-3)) < Q(".001")
    n = Q(".49")*121
    assert 12*20000*11**3*10**4*(1+Q("1.001")*10**4)*decay(Q("1.60")*(n-3)) < Q(".001")
    assert 2*(1-Q("2.001")/n) > Q("1.93")
    assert (Q("1.93")/75-Q(1,80))**3*10**8 > Q("2.61")**3
    assert n/160 > Q(1,4)
    assert 10**9*11**3*decay(n*460/160) < Q(".001")
    # The warmed Gaussian band at 50 <= r <= 100.
    c = Q(".00093")*(Q(".49")-Q(42,50**2))
    assert 12*100**2*(Q(1,225)+Q("1.001")/50)*decay(c*225**2)/(2*c) < Q(".001")


def check_tests():
    eps = 1/sqrt_lo(M)
    def test(hlo, hhi, T, ratio, eta, rhi):
        u = eps*((eta+1)*(hhi+3*T)+3*max(50,rhi)**2)
        mass = eps*((eta+1)*hhi+3*max(50,rhi)**2)
        assert Q(0) < hlo <= hhi and T < 2300000 and ratio < 1000
        assert mass < Q(".02") and u < Q(".08")
        # sinh(u) <= u exp(u^2) by the positive power series.
        assert u*exp_small_upper(u*u)*(Q("2.81")+Q("4.065")*ratio) < Q(".94")

    # In each rational interval bound T and eta above and h below.
    for i in range(20,92):
        lo, hi = Q(i), min(Q(i+1),Q("4.5")**3)
        if hi < lo:
            continue
        power = ((55+hi/2)/Q(".115"))**3
        T = sqrt_hi(power)
        test(lo,hi,T,T/lo,Q("9.36")*(hi/2+64),5)
    for i in range(90,220):
        lo,hi = Q(i,20),Q(i+1,20)
        b = Q("1.31")*hi**2
        T = sqrt_hi(((55+b)/Q(".115"))**3)
        test(lo**3,hi**3,T,T/lo**3,Q("9.36")*(b+64),hi)
    for start,end,t in ((11,15,20),(15,20,15),(20,30,10),(30,50,Q("4.5")),(50,100,225)):
        for j in range(start,end):
            lo,hi = Q(j),Q(j+1)
            if j<15:
                eta = Q("9.36")*(Q("1.31")*hi**2+64)
            else:
                eta = 3+Q("4.81")*215*sqrt_hi(Q("1.31")+64/lo**2)
            T = t*hi**(3 if j<50 else 2)
            test(lo**3,hi**3,T,t if j<50 else t/lo,eta,hi)
    assert 600*2300000*(1+Q("1.001")*1000)*decay(Q(38)) < Q(".001")
    assert 4*(2*2300000)**3*eps**3 < Q(".001")


if __name__ == "__main__":
    check_fair_peak()
    check_height()
    check_blocks()
    check_tests()
    print("Verified the Fourier cutoffs, positive tests and integer sign overlap at n >= 10^22.")
