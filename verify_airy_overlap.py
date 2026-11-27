"""Check the Airy-saddle overlap and the decreasing-side density bound."""

from fractions import Fraction as Q

from verify_rising import PI_LO, PI_HI, decay, exp_negative_lower, exp_small_upper, sqrt_hi, sqrt_lo


def check_fair_side():
    rate = Q(".12")
    cutoff = 4800
    assert 60/PI_LO*sqrt_hi(1/rate)**9*12 < 3300000
    assert 60/PI_LO/rate**6*120 < 10**9
    zl, zh = Q("34.14"), Q("34.16")
    assert zl**3 < rate**3*cutoff**2 < zh**3
    tail = 120/PI_LO/rate**3*decay(zl)*zh**2/(1-2/zl)
    for m, target in ((10**23,".000005"),(2*10**24,".0000003")):
        central = Q(10000,m)/PI_LO*sum(Q(c*cutoff**(j+2),j+2) for j,c in enumerate((1,2,1)))
        assert central + tail + Q(1,10**12) < Q(target)
    mode = sqrt_lo(6/PI_HI)
    assert mode/exp_small_upper(6*Q("1.4")**2/10)**10 > Q(".000005")
    assert mode*12*(Q("1.4")-Q(".75"))/exp_small_upper(6*Q("1.501")**2/10)**10 > Q(".000005")
    assert mode/exp_small_upper(Q(1))**10 > Q(".0000003")+3300000/sqrt_lo(2*10**24)
    assert 10**9/sqrt_lo(2*10**24) < Q(".001")


def check_height_and_normalization():
    assert 20000*decay(Q("1.48")*(Q(25,2)-Q("2.01"))) < Q(".01")
    assert (60*55)**2 > 220**3 and (60*56)**2 < 225**3
    assert Q(1,4)-Q(1,4*10**9)-Q("1.305")/220 > Q(".22")
    assert Q(".45")/2-Q("1.30")*Q("1.001")/220 > Q(".21")
    assert Q(220**2,8192*500**2) > Q(1,10**7)
    assert 5*500**3/sqrt_lo(2*10**24) < Q(".01")
    assert Q("9.36")*(Q("1.31")*225+284) < 5500
    for r, bound in ((15,1740),(50,1300),(250,1250)):
        assert 3+Q("4.81")*225*sqrt_hi(Q("1.31")+Q(284,r*r)) < bound


def check_fourier_tails():
    rate = Q(".115")
    assert 12*100*(350**2+2*350+2)*decay(Q(55))/rate**3 < Q(".001")
    # N >= .49 r^2 for the peak transforms. The middle fraction is
    # >= 1.80 n steps after the two real boundary powers from r >= 30.
    r = 30
    n = Q(".49")*r*r
    assert 2*(1-Q("40.001")/n) > Q("1.80")
    assert (Q(".124")*Q("1.80")-Q(1,80))**3*45**2 > Q("2.61")**3
    assert 12*45*r**3*(1+Q("1.001")*45)*decay(Q(".075")*(n-42)) < Q(".001")
    # Substitute v=|xi|/r^2 in the Gaussian bands.
    for left, rate, max_r, min_r in (
        (250,Q(".00093"),250,50),
        (150,Q(".00249"),500,250),
        (250,Q(".00093"),500,250)
    ):
        c = rate*(Q(".49")-Q(42,min_r**2))
        assert 12*max_r**2*(Q(1,left)+Q("1.001")/min_r)*decay(c*left**2)/(2*c) < Q(".001")
    # Above 45 the full physical exponent is N |xi/r^3|^(2/3)/80.
    # Extract half the exponent at the left endpoint, integrate the rest in y.
    assert Q(".49")*30**2/160 > 1
    assert 36*30**3*(4+Q("1.001")*4)*decay(Q(".49")*30**2*12/160) < Q(".001")


def check_signed_kernel():
    eps = 1/sqrt_lo(2*10**24)
    def upper_sinh(v):
        return (exp_small_upper(v)-exp_negative_lower(v))/2
    # Small tilt cutoff is real. T^2/h has no interior maximum
    # on either interval, by its explicit formula.
    for low, high, low_b, high_b in (
        (20,125,10,Q(125,2)), (125,3375,Q("1.31")*25,Q("1.31")*225)
    ):
        tt_low = ((55+low_b)/Q(".115"))**3
        tt_high = ((55+high_b)/Q(".115"))**3
        T = sqrt_hi(tt_high)
        ratio2 = max(tt_low/low,tt_high/high)
        u = eps*(5501*(high+3*T)+7500)
        scale = eps*(5501*(Q("2.81")*high+Q("12.51")*T+Q("12.20")*ratio2)
                     +7500*(Q("2.81")+Q("4.065")*T/low))
        assert 3*Q("4.06")*Q("1.001") < Q("12.20")
        assert upper_sinh(u)/u*scale < Q(".88")
    for r, T, eta, ratio in (
        (30,45*30**3,1740,45),(50,Q("4.5")*50**3,1740,Q("4.5")),
        (250,250*250**2,1300,Q(250,250)),(500,150*500**2,1250,Q(150,500))
    ):
        u = eps*((eta+1)*(r**3+3*T)+3*max(50,r)**2)
        assert u < Q(".22")
        assert upper_sinh(u)*(Q("2.81")+Q("4.06")*Q("1.001")*ratio) < Q(".88")
    tmax = 4*10**7
    assert 60*eps**8*tmax*(1+Q("1.001")*tmax) < Q(".001")
    assert 4*(2*tmax)**3*eps**3 < Q(".001")
    assert Q(".023")*200**2/110**4 > Q(".0000017")
    assert 10**24//20**2 >= 10**21 and 10**24//110**2 >= 25*10**18


if __name__ == "__main__":
    check_fair_side()
    check_height_and_normalization()
    check_fourier_tails()
    check_signed_kernel()
    print("Verified both staircase sign joins at n >= 10^24 and the fair decreasing side.")
