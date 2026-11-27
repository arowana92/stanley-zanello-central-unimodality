"""Rational bounds for variation-overlap.md."""

from fractions import Fraction as Q
from math import comb

from verify_airy_grid import finite_norm_bracket
from verify_rising import PI_LO, PI_HI, decay, exp_small_upper, sqrt_hi, sqrt_lo


MIN_N = 5*10**18
MIN_M = 2*MIN_N


def band_norm(poly, left, right):
    """Integral of the square of a polynomial on a frequency interval."""
    return sum(a*b*(right**(i+j+1)-left**(i+j+1))/Q(i+j+1)
               for i,a in enumerate(poly) for j,b in enumerate(poly))


def check_kernel():
    for order, bound in enumerate(("1.76","1.63","1.69")):
        polys = [[Q(0)]*order+[Q(1)], [Q(0)]*order+[Q(3),Q(-2)]]
        norm = slope = 0
        for poly,lo,hi in zip(polys,(Q(0),Q(1)),(Q(1),Q("1.5"))):
            norm += 2*band_norm(poly,lo,hi)
            slope += 2*band_norm([j*c for j,c in enumerate(poly) if j],lo,hi)
        assert norm*slope < Q(bound)**4


def check_corank_range():
    # Descending from the infinite lattice norm to an interval for the Airy
    # energy. Bound -log(1-v) between v and v/(1-v), entirely rationally.
    h = 100
    lo,hi,scale = finite_norm_bracket(h)
    lower = 1-Q(hi,2*scale)
    upper = 1-Q(lo,2*scale)
    assert 2*h*h*lower+Q(3,2*h)-Q(2000,h**4)-Q("2.60")**2/(30*h*h) > Q("2.337")
    assert 2*h*h*upper/(1-upper)+Q(3,2*h)+Q(2000,h**4) < Q("2.339")
    assert 70**2*(2*Q("2.337")/3-Q(".016"))**2/Q("2.001")**3 > 1450
    # The intermediate-height block reaches a scaled frequency in [80,81].
    c = Q(1,6)-Q(1,64)
    block = (1+decay(c**3*80**2/16))/2*exp_small_upper(Q("2.72")/6)
    assert block < Q(".99") and Q("5.99")*(1-block)/81**2 > Q(".000009")
    assert Q(81,6*8) < PI_LO
    y = Q(".0005")
    displacement = y*(2+Q("2.60")/Q(".30"))
    assert displacement/(1-displacement) < Q(".006")
    assert 2*Q(".844")*Q(".60")-Q(".60")**2/16-3*y*Q("3.20") > Q(".95")
    assert Q(".844")**2-Q(".95")/16 > 3*y
    assert Q(".95")*(1-Q(".006")**2)-3*y*Q("2.60")*Q(".006")**2 > Q(".80")
    for hmin,hmax,variance,y,dec,rate in (
        (4,8,".0084",".0003",".40",Q(".023")/8**4),
        (8,20,".015",".0005",".34",Q(".000009")),
        (20,110,".017",".0005",".36",Q(".00004"))
    ):
        variance, y, dec = Q(variance), Q(y), Q(dec)
        assert 2*(1/(4*Q("2.60"))-Q(1,2*hmin*hmin))**2 > variance
        assert Q(".37")*y**2/(Q(".08")**4*(1-(y/Q(".08"))**2)) < (Q(".5")-dec)*variance
        N = Q(10**17,hmax*hmax)
        d = sqrt_lo(variance*(N-401))
        assert Q("1.001")*4600/(6*variance*d*dec**2) < Q(".95")
        assert 2300/(dec*d) < Q(".018") and y*d > 10
        assert (2*(1+Q("1.01")*10000)*10000*sqrt_hi(116*N)*3**20
                *decay(rate*N*y*y)) < Q(".001")
    assert Q(10**17,10000**2) > 100000


def check_mode():
    assert Q("2.339")/180 + Q("2.7")/60**2 < Q(1,70)
    # Auxiliary real-tilt moments at every r >= 7.
    assert Q(8,7) < Q("1.05")**3 and Q(6,7)**2 > Q(".90")**3
    assert Q(".60")**3 < Q(".76")**3*Q(6,7)**4
    assert 20000*decay(Q("1.48")*(Q(".49")*49*Q(".90")-Q("2.01"))) < Q(".001")
    assert Q("1.01")/Q(".99")*Q("1.05")*Q("1.001")/Q(".999")*exp_small_upper(Q(".76")/4) < Q("1.4")
    assert Q(".4")/(1+Q(2)**2/2+Q(2)**4/24+Q(2)**6/720-1) < Q(".146")
    assert (1-Q(".146"))/4 > Q(".21") and Q(".7")*Q(".21") > Q(".146")
    # Curvature and fair derivatives use the centered-clock table at m >= 10^19.
    eps = 1/sqrt_lo(MIN_M)
    assert 11*sqrt_lo(6/PI_HI)/exp_small_upper(Q(1,12)) - 10**9*eps > Q("12.3")
    assert 16*sqrt_lo(6/PI_HI)/exp_small_upper(Q(1))**8 - 3300000*eps > Q(".0054")
    for slope in (1,8):
        extra = 12*Q("1.501")*eps+6*eps*eps
        exponent = Q(".65")*slope+Q(slope*slope,24)+extra
        assert Q("1.78")*slope/exp_small_upper(exponent/8)**8 > Q(".0054")


# |y|, fraction of a height block, Holder exponent, rate per height block.
BANDS = [
    ("1.5", "1", 50,".0095"), ("2","1",25,".016"), ("2.5","1",16,".025"),
    ("3","1",12,".036"), ("4.5","1",6,".075"), ("6",".8",6,".12"),
    ("8",".7",4,".20"), ("10",".7",3,".28"), ("12",".6",3,".37"),
    ("15",".5",2,".50"), ("20",".45",2,".72"), ("25",".35",2,".92"),
    ("30",".35",2,"1.10"), ("35",".3",2,"1.30"), ("45",".25",2,"1.60"),
]
# Bounds for r; the cutoff is y times r^3.
CUTOFFS = [(7,9,35), (9,12,20), (12,14,12), (14,15,10), (15,21,8), (21,30,Q("4.5")),
           (30,42,3), (42,54,2), (54,60,Q("1.5"))]


def check_blocks():
    for y,c,p,C in BANDS:
        y,c,C = Q(y),Q(c),Q(C)
        # Upper bound for 1-(1-1/p)^(1/3), by bisection.
        lo,hi = Q(0),Q(1)
        for _ in range(24):
            mid = (lo+hi)/2
            if (1-mid)**3 > Q(p-1,p):
                lo = mid
            else:
                hi = mid
        z = y*y*(Q(".999")*c)**3/16
        moment = (comb(4*p,2*p)+2*sum(comb(4*p,2*p+j)*decay(j*j*z)
                                      for j in range(1,2*p+1)))/Q(2**(4*p))
        exponent = p*c*(C+Q("2.60")*hi+Q(".00001"))
        assert moment*exp_small_upper(exponent/4)**4 < 1
    assert sqrt_lo(1+(20000*decay(Q("1.48")*Q("7.999")))**2)+Q(1,10**8) < Q("1.03")
    # The first two boundary powers cost at most 20000 with loss of < 4 units
    # of length, or 1.03 with loss of < 20. Check every frequency band.
    for r,_,cut in CUTOFFS:
        N = Q(".49")*r*r
        cost = 0
        for i,(y,_,_,C) in enumerate(BANDS):
            l = Q(y)
            if l < cut:
                continue
            u = Q(BANDS[i+1][0]) if i+1<len(BANDS) else Q(150)
            envelope = min(20000*decay(Q(C)*(N-4)),Q("1.03")*decay(Q(C)*(N-20)))
            cost += 12*r/Q(".21")*(u-l)*(1+Q("1.001")*u)*envelope
        assert cost < Q(".022"), (r, float(cost))
    # Above 150 the two short end blocks leave at least 1.82n steps.
    N = Q(".49")*49
    assert 2*(1-Q("2.001")/N) > Q("1.82")
    assert (Q(".124")*Q("1.82")-Q(".10"))**3*150**2 > Q("2.61")**3
    assert (Q("1.82")/75-Q(1,80))**3*10**8 > Q("2.61")**3
    assert 150**2 > 28**3 and N/20 > 1
    assert 16*10**6*7*decay(N*28/20) < Q(".001")
    assert 12*20000*2*7/Q(".21")*1200*decay(N*460/160) < Q(".001")


def check_small_tails():
    rate = Q(".115")
    # Integrate 1+1.001 xi/|h|. Use Gamma(3/2,z) <= Gamma(2,z)/sqrt(z).
    for u,z,P,margin in ((8,25,208,25), (16,92,100,27)):
        # z above bounds the polynomial at the far endpoint in each range;
        # the exponent here is the smallest z-B in that range.
        integral = (Q("1.5")*(z+1)/(sqrt_lo(rate)**3*5)
                    + Q("1.5015")*(z*z+2*z+2)/(u*rate**3))
        assert 8*P*decay(Q(margin))*integral < Q(".003")
    assert 27+Q("1.31")*49 < 92
    assert 100*150*60/sqrt_lo(MIN_M) < PI_LO


def check_displacements():
    eps = 1/sqrt_lo(MIN_M)
    assert exp_small_upper(Q(1))**43 < MIN_M < 1/decay(Q(44))
    assert 185**3 < (60*43)**2 and (60*44)**2 < 192**3
    assert Q(185**2,8192*60**2)>Q(1,10**7)
    assert Q(1,4)-Q(1,4*10**7)-Q("1.305")/185 > Q(".22")
    assert Q(".45")/2-Q("1.30")*Q("1.001")/185 > Q(".21")
    assert 5*60**3*eps < Q(".01")
    # v is the area error in units m^(-1/2). The displacement includes the
    # radial starting-height comparison. ratio bounds T/|h|.
    def check(h,T,ratio,v,r):
        shift = eps*(v+1)
        u = h*shift+3*eps*max(50,r)**2
        assert u < Q(".14")
        q = Q("1.001")*ratio
        loss = (u*exp_small_upper(u*u)*(Q("1.76")+Q("1.63")*q)
                + exp_small_upper(u)*shift*T*(Q("1.63")+Q("1.69")*q))
        assert loss < Q(".96"), (float(h),float(T),float(loss))
        assert T < 500000 and ratio < 500
    for j in range(8*10,18*10):
        lo,hi = Q(j,10),Q(j+1,10)
        X = 2*(1+Q(".084")*hi**2+60)
        T = sqrt_hi((25/Q(".115"))**3)
        check(hi,T,T/lo,Q("9.36")*X,0)
    # Enclose h^(2/3) by subdividing in r, using both normalizations.
    for j in range(251,700):
        lo,hi = Q(j,100),Q(j+1,100)
        hlo,hhi = max(16,lo**3),hi**3
        if hhi < 16:
            continue
        B = min(hhi/2,Q("1.31")*hi*hi)
        T = sqrt_hi(((27+B)/Q(".115"))**3)
        check(hhi,T,T/hlo,Q("9.36")*(B+60),hi)
    for start,end,ratio in CUTOFFS:
        for j in range(20*start,20*end):
            lo,hi = Q(j,20),Q(j+1,20)
            X = Q("1.31")*hi*hi+60
            v = Q("9.36")*X if j < 300 else 3+Q("4.81")*192*sqrt_hi(Q("1.31")+60/lo**2)
            check(hi**3,ratio*hi**3,ratio,v,hi)
    assert 600*500000*(1+Q("1.001")*500)*decay(Q(38)) < Q(".001")
    assert 4*(2*500000)**3*eps**3 < Q(".001")


if __name__ == "__main__":
    check_kernel()
    check_corank_range()
    check_mode()
    check_blocks()
    check_small_tails()
    check_displacements()
    print("Verified the variation bound and the staircase sign intervals for every n >= 5*10^18.")
