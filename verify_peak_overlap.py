"""Rational bounds for the signed inversion and the join in peak-overlap.md."""

from fractions import Fraction as Q

from verify_holder import half_tail
from verify_rising import PI_LO, decay, exp_negative_lower, exp_small_upper, sqrt_hi, sqrt_lo


def check_height_and_frequency():
    m = 2*10**28
    assert (60*65)**2 > 240**3 and (60*66)**2 < 251**3
    assert Q(1,4)-Q(1,4*10**10)-Q("1.305")/240 > Q(".22")
    assert Q(".45")/2-Q("1.30")*Q("1.001")/240 > Q(".21")
    assert Q(240**2,8192*1900**2) > Q(1,10**7)
    assert 5*1900**3/sqrt_lo(m) < Q(".01")
    for r, bound in ((15,2150),(50,1530)):
        assert 3+Q("4.81")*251*sqrt_hi(Q("1.31")+Q(334,r*r)) < bound
    # l*theta <= .33 for theta <= 1/1024.
    assert Q("3.25")/10 + Q(1,1024) < Q(".33")
    assert (1-Q(".33")**2/6)**2 > Q(".95")
    z = Q(".24")*Q(".95")*Q("3.25")**3/4
    assert (Q(3,8)+decay(z)/2+decay(4*z)/8)*exp_small_upper(Q(".80")) < 1
    assert Q(63,64)*Q(".8")/(2*(Q("3.25")+Q(".01"))) > Q(".115")
    rate = Q(".115")
    for T, loss, prefactor in ((20000,0,8*1258),(22000,32,100),
                              (110000,Q(343,2),100),(190000,Q("1.31")*225,100)):
        scaled = rate**3*T*T
        z_high = next(i for i in range(1000) if i**3 > scaled)
        assert (12*prefactor*(z_high**2+2*z_high+2)
                *decay(z_high-1-loss)/rate**3 < Q(".001"))


def check_kernel_loss():
    eps = 1/sqrt_lo(2*10**28)
    def sinh_bound(x):
        return (exp_small_upper(x)-exp_negative_lower(x))/2
    for r, T, ratio, eta_factor in (
        (4,22000,22000,6100), (7,110000,Q(110000,64),6100),
        (15,190000,Q(190000,343),6100), (50,45*50**3,45,2150),
        (500,500*500**2,10,1530), (1900,170*1900**2,Q(170,1900),1530),
    ):
        u = eps*((eta_factor+1)*(r**3+3*T)+3*max(50,r)**2)
        assert u < Q(".10")
        assert sinh_bound(u)*(Q("2.81")+Q("4.06")*Q("1.001")*ratio) < Q(".50")
    assert Q("9.36")*(Q("1.31")*225+334) < 6100
    h, T = 1250, 20000
    x = 2*(h+Q(h*h,4)+334)
    x_by_h = 2*(1+Q(h,4)+334)
    u = eps*((Q("9.36")*x+1)*(h+3*T)+3*h*h)
    ratio = eps*((Q("9.36")*x_by_h+1)*(h+3*T)+3*2500)
    assert u < Q(".10")
    assert sinh_bound(u)/u*(Q("2.81")*u+Q("4.06")*Q("1.001")*T*ratio) < Q(".50")
    assert 4*(2*7*10**8)**3*eps**3 < Q(".001")
    assert 60*eps**8*7*10**8*(1+Q("1.001")*7*10**8) < Q(".001")
    assert 60*120/PI_LO/Q(".12")**6 < 10**9


def check_moderate_heights():
    # The wide contour separates the real spectrum at H >= 2*10^5.
    h = 2*10**5
    v = PI_LO/(Q("1.5")*h+1)
    assert h*h*(v-v**3/6)**2 > Q("4.3")
    assert (1-Q("2.6")/h**2)*(Q("1.5")-Q("1.5")**2/(2*h*h)) > Q("1.48")
    for h, error, cubic in ((2*10**5,".0027",610),(2*10**6,".000564",130)):
        assert (Q(error)/2)**25 > Q(12,h)**17
        assert Q(8,27)*Q("2.60")/Q(".99")**3+6*Q(error)/Q(".03")**3 < cubic
    assert 9*Q(".2")/Q("200.2")**2 > Q(".00004")
    assert Q(9)*Q(".2")*(Q(".2")/Q("200.2"))**2 > Q(".0000017")
    for nblocks, cubic, edge, rate in (
        (25*10**18,4600,".0000015",".00004"),
        (25*10**14,610,".00001",".003"),
        (25*10**12,130,".00005",".003")
    ):
        edge, rate = Q(edge), Q(rate)
        d = sqrt_lo(Q(".0084")*nblocks)
        error = 27*cubic/(6*Q(".0084")*d)
        assert 1-Q(".002")-4800/d-Q("1.002")*(exp_small_upper(error)-1) > Q(".80")
        assert (1-Q(401,nblocks))*(Q(1,2)-cubic*edge/(6*Q(".0084"))) > Q(".35")
        assert 2*(1+10**4*sqrt_hi(116*nblocks))**3*decay(rate*nblocks*edge**2-20) < Q(".001")
    assert 2*Q("1.002")*half_tail(3,".35") < Q(".50")
    assert Q(".80")*Q(".99")*Q("2.3")-Q(".52") > Q(".5")


def check_large_heights():
    for h, error, vmin, vmax, cubic, disk in (
        (29*10**7,".0000193",".34",".61",16,".02"),
        (19*10**9,".00000112",".35",".60",Q("1.1"),".01")
    ):
        error, vmin, vmax, disk = map(Q,(error,vmin,vmax,disk))
        assert (error/2)**25 > Q(12,h)**17
        assert Q(2,9)*Q("1.65")-2*error/Q(".04")**2 > vmin
        assert Q(2,9)*Q("2.60")+2*error/Q(".04")**2 < vmax
        assert Q(8,27)*Q("2.60")/(1-disk)**3+6*error/(Q(".04")-disk)**3 < cubic
        assert error/Q(".04") < Q(".001")
    h = 19*10**9
    for start, err, rate in ((".01",Q(".00000112"),".12"),
                             (".04",2*sqrt_hi(Q(12,h)),".05"),(".065",Q(".000421"),".05")):
        assert err+Q(12,h) < (Q("1.65")*Q(".109")-Q(rate))*Q(start)**2
    assert (Q(".000421")/2)**5 > Q(12,h)**2
    assert Q(".0000193")+Q(12,29*10**7) < (Q("1.65")*Q(".109")-Q(".11"))*Q(".02")**2
    assert Q(".92")**4*Q(".69")**3 > Q(".61")**3
    assert Q(".345")*401*Q(".08")**2+Q("5.23")+Q("4.64") < 11
    for nblocks, low, high, cubic, core_bound, damping in (
        (25*10**6,Q(".34"),Q(".61"),16,Q(".70"),Q(".42")),
        (1700000,Q(".35"),Q(".60"),Q("1.1"),Q(".35"),Q(".49")),
    ):
        d = sqrt_lo(low*nblocks)
        error = 27*cubic/(6*low*d)
        assert 1-Q(".002")-480/d-Q("1.002")*(exp_small_upper(error)-1) > core_bound
        assert (1-Q(401,nblocks))*(Q(1,2)-cubic*Q(".01")/(6*low)) > damping
        if nblocks > 1700000:
            assert low/2-cubic*Q(".02")/6 > Q(".11")
            assert (1-Q(401,nblocks))*Q(".11")/high > Q(".18")
            assert 2*Q("1.002")*(half_tail(3,".42")+half_tail(29,".18")) < Q(".24")
            freq = Q(".04")
        else:
            assert (1-Q(401,nblocks))*Q(".05")/high > Q(".083")
            assert 2*Q("1.002")*half_tail(30,".083") < Q(".001")
            freq = Q(".08")
        c = Q(".0034")*nblocks
        hi = sqrt_hi(high*nblocks)
        volume = hi/(2*c*freq)+hi**3*(freq/(2*c)+1/(4*c**2*freq))
        assert 2*volume*decay(c*freq*freq-20) < Q(".001")
    assert Q(".35")*Q(".99")*Q("2.3")-Q(".135") > Q(".5")


if __name__ == "__main__":
    check_height_and_frequency()
    check_kernel_loss()
    check_moderate_heights()
    check_large_heights()
    print("Verified the tilted cutoffs and small-corank overlaps at n >= 10^28.")
