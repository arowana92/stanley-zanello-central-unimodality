"""Check the height, cutoff and intermediate-saddle bounds in tilted-height.md."""

from fractions import Fraction as Q
from itertools import product
from math import comb

from verify_holder import half_tail
from verify_rising import PI_LO, decay, exp_negative_lower, exp_small_upper, sqrt_hi, sqrt_lo


def check_climbs():
    q = Q(3,4)

    def advance(row, bottom, top):
        following = {}
        for h, mass in row.items():
            for j in (h-1,h+1):
                if bottom <= j <= top:
                    following[j] = following.get(j,0)+mass*q**min(h,j)/2
        return following

    for target in range(2,7):
        start = target//2
        pre, bridge, tail = {0:1}, {start:1}, {target:1}
        prefixes, segments, suffixes = [0], [0], [1]
        for length in range(1,13):
            pre = advance(pre,0,target-1)
            bridge = advance(bridge,start+1,target)
            tail = advance(tail,0,target+12)
            prefixes.append(pre.get(start,0))
            segments.append(bridge.pop(target,0))
            suffixes.append(sum(tail.values()))
            # Every constrained bridge pays at least start per edge.
            ups, parity = divmod(length+target-start,2)
            unrestricted = comb(length,ups) if not parity and ups <= length else 0
            assert segments[-1] <= Q(unrestricted,2**length)*q**(start*length)
        for length in (7,10,12):
            direct = 0
            for signs in product((-1,1),repeat=length):
                h = area = maximum = 0
                for step in signs:
                    area += min(h,h+step)
                    h += step
                    if h < 0:
                        break
                    maximum = max(maximum,h)
                else:
                    if maximum >= target:
                        direct += q**area/2**length
            # Independently reconstruct all paths hitting the target.
            split = sum(prefixes[u]*segments[v-u]*suffixes[length-v]
                        for v in range(1,length+1) for u in range(v))
            assert split == direct


def check_height_costs():
    # log(m)>69, U=(60 log(m))^(2/3), H=sqrt(m)/r.
    assert (60*69)**2 > 250**3
    assert Q(1,4)-Q(1,4*10**11)-Q("1.305")/250 > Q(".22")
    assert 4*Q(".22")/8 > Q(".30")**2
    assert Q(".45")/2-Q("1.30")*Q("1.001")/250 > Q(".21")
    assert 4*Q(".21")*Q(".4")**2/2 > Q(".25")**2*Q("1.001")**3
    assert Q(250**2,8192*1900**2) > Q(1,10**7)
    assert 5*1900**3/sqrt_lo(2*10**30) < Q(".01")
    assert Q(".30")*60-Q("3.25") > 5
    assert Q(".25")*60-3 > 5
    assert Q(2*10**30, 10**7) > Q("1.30")*1900**2+10*70
    # The fixed-time normalization change and the time-end errors.
    assert Q(1,2)+1+Q("1.51")*Q("1.001")/2 < Q("2.4")
    assert Q("2.4")*2*Q("1.001") < Q("4.81")
    assert (60*70)**2 < 261**3
    for r, bound in ((15,2150),(50,1530)):
        assert 3+Q("4.81")*261*sqrt_hi(Q("1.31")+Q(354,r*r)) < bound


def check_peak():
    eps = 1/sqrt_lo(2*10**30)
    def sinh_upper(u):
        return (exp_small_upper(u)-exp_negative_lower(u))/2
    for left, r, T, ratio in (
        (1,4,120000,120000), (4,7,600000,Q(600000,64)),
        (7,15,10**6,Q(10**6,343)), (15,50,45*50**3,45),
        (50,500,500*500**2,10), (500,1900,170*1900**2,Q(170,1900)),
    ):
        if left < 15:
            eta = Q("9.36")*(Q("1.31")*225+354)*eps
        else:
            eta = (2150 if left == 15 else 1530)*eps
        u = (eta+eps)*(r**3+3*T)+3*eps*max(50,r)**2
        assert u < Q(".02")
        assert sinh_upper(u)*(Q("2.81")+Q("4.06")*Q("1.001")*ratio) < Q(".76")
    T = 80000
    X = 2*(1250+Q(1250**2,4)+354)
    X_ratio = 2*(1+Q(1250,4)+354)
    u = eps*((Q("9.36")*X+1)*(1250+3*T)+3*1250**2)
    u_ratio = eps*((Q("9.36")*X_ratio+1)*(1250+3*T)+3*2500)
    assert u < Q(".02")
    assert sinh_upper(u)/u*(Q("2.81")*u+Q("4.06")*Q("1.001")*T*u_ratio) < Q(".70")
    assert 60*eps**8*7*10**8*(1+Q("1.001")*7*10**8) < Q(".001")
    assert 4*(2*7*10**8)**3*eps**3 < Q(".001")

    rate = Q(".035")
    for cutoff, z, end, loss, pref in (
        (80000,64,66,0,4*1252), (120000,85,86,32,24),
        (600000,248,250,Q(343,2),24), (10**6,350,350,Q("1.31")*225,16),
    ):
        assert z**3 <= rate**3*cutoff**2 <= end**3
        assert 12*pref*(end**2+2*end+2)*decay(z-loss)/rate**3 < Q(".001")
    r = 15
    nblocks = Q(".49")*r*r
    assert 4*nblocks-Q("9.01") > Q("3.9")*nblocks
    assert Q(".185")*Q("3.9") > Q(".70")
    assert (Q("1.96")/75-Q(1,80))*400 > Q("2.61")
    assert 12*10**4*r**3*(1+Q("1.001")*10**4)*decay(Q(".7")*nblocks-20) < Q(".001")
    assert (10**4*r**3)**2 > (600*170)**3
    assert 36*170**3*(600**2+2*600+2)*decay(Q(580)) < Q(".001")


def check_intermediate_saddles():
    z = Q(".999")**3*Q("4.5")**2/16
    moment = (comb(24,12)+2*sum(comb(24,12+d)*decay(d*d*z)
                                for d in range(1,13)))/Q(2**24)
    assert exp_small_upper(6*(Q("2.60")*(1-Q(".941"))+Q(".001")))*moment < Q(".926")**6
    assert Q(".996")*Q(".074")/Q("4.7")**2 > Q(".003")
    assert Q(".996")*Q(".074")*(Q(".2")/Q("5.5"))**2 > Q(".00008")
    h = 10**6
    angle = PI_LO/(Q("1.5")*h+1)
    assert h*h*(angle-angle**3/6)**2 > Q("4.30")
    assert (1-Q("2.60")/h**2)*(Q("1.5")-Q("1.5")**2/(2*h*h)) > Q("1.48")
    error = Q(".00093")
    assert (error/2)**25 > Q(12,h)**17
    assert 6*error/Q(".03")**3+Q(8,27)*Q("2.60")/Q(".99")**3 < 210
    assert Q(".96")**4 * Q(123,116)**3 > 1
    assert 1/decay(Q(6)) > 204
    assert Q(123,2)*401*Q(".04")**2+Q("5.5")+6 < 54
    assert Q("1.001")*(1+54+Q(".7"))/Q(".04") < 1600
    for nblocks, cubic, edge in ((25*10**16,4600,Q(".0000015")),
                                (25*10**14,210,Q(".00002"))):
        d = sqrt_lo(Q(".0084")*nblocks)
        err = 27*cubic/(6*Q(".0084")*d)
        assert (1-Q(".002")-4800/d-Q("1.002")*(exp_small_upper(err)-1)) > Q(".92")
        assert (1-Q(401,nblocks))*(Q(1,2)-cubic*edge/(6*Q(".0084"))) > Q(".35")
        assert 2*(1+10**4*sqrt_hi(116*nblocks))**3*decay(Q(".003")*nblocks*edge**2-20) < Q(".001")
    assert 2*Q("1.002")*half_tail(3,".35") < Q(".50")


def check_wider_disks():
    for h, bound, radii in ((10**9,Q(".0000083"),(".015",)),
                            (10**11,Q(".00000036"),(".01",".04",".065"))):
        assert (bound/2)**25 > Q(12,h)**17
        assert Q(2,9)*Q("1.65")-2*bound/Q(".04")**2 > Q(".35")
        assert Q(2,9)*Q("2.60")+2*bound/Q(".04")**2 < Q(".60")
        assert bound/Q(".04") < Q(".001")
        if h == 10**9:
            assert Q(8,27)*Q("2.60")/Q(".985")**3+6*bound/Q(".025")**3 < 4
            errors = [bound]
        else:
            assert Q(8,27)*Q("2.60")/Q(".99")**3+6*bound/Q(".03")**3 < 1
            assert (1+Q(".065")/Q(".16"))**2 < 2
            outer = Q(".000216")
            assert (outer/2)**5 > Q(12,h)**2
            errors = [bound, 2*sqrt_hi(Q(12,h)), outer]
        for radius, error in zip(radii,errors):
            assert error+Q(12,h) < (Q("1.65")*Q(".109")-Q(".12"))*Q(radius)**2
    nblocks = 25*10**6
    d = sqrt_lo(Q(".35")*nblocks)
    assert (1-Q(".002")-480/d-Q("1.002")*(exp_small_upper(4*27/(6*Q(".35")*d))-1)) > Q(".8")
    assert (1-Q(401,nblocks))*(Q(1,2)-4*Q(".01")/(6*Q(".35"))) > Q(".48")
    damp = Q(".0034")*nblocks
    v = Q(".04")
    high_d = sqrt_hi(Q(".60")*nblocks)
    volume = high_d/(2*damp*v)+high_d**3*(v/(2*damp)+1/(4*damp**2*v))
    assert 2*volume*decay(damp*v*v-20) < Q(".001")
    assert 2*Q("1.002")*half_tail(3,".48") < Q(".12")


if __name__ == "__main__":
    check_climbs()
    check_height_costs()
    check_peak()
    check_intermediate_saddles()
    check_wider_disks()
    print("Verified the tilted height estimates, clock comparison and 10^30 join for both families.")
