"""Exact tree-growth checks and rational bounds for tilted-thinning.md."""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial

from verify_rising import PI_HI, PI_LO, decay, exp_small_upper, sqrt_hi, sqrt_lo
from verify_variation import BANDS


@dataclass(frozen=True)
class TiltRange:
    min_length: int
    max_root: Q
    length_window: Q
    shifted_tilt: int
    log_floor: int
    placement_log: Q
    variance_cost: Q
    quadratic_cost: Q


ORIGINAL = TiltRange(2*10**13, 31, Q('.00001'), 29800, 30, Q('1.57'), Q('1.12'), Q(5))
SHORT = TiltRange(10**12, 16, Q('.00003'), 4100, 27, Q('.55'), Q('.41'), Q(2))

CUTS = [(7, 35), ('7.5', 30), (8, 25), (9, 20), ('10.2', 15),
        ('11.1', 12), (12, 10), ('13.6', 8), ('16.7', 6),
        ('20.2', '4.5'), ('28.4', 3)]


@lru_cache(maxsize=None)
def trees(d):
    if d == 0:
        return (None,)
    return tuple((a, b) for k in range(d) for a in trees(k) for b in trees(d-1-k))


def grow(tree):
    yield tree, None
    yield None, tree
    if tree is not None:
        left, right = tree
        for new in grow(left):
            yield new, right
        for new in grow(right):
            yield left, new


@lru_cache(maxsize=None)
def depths(tree, left=0, right=0):
    if tree is None:
        return left, right
    a, b = depths(tree[0], left+1, right)
    c, d = depths(tree[1], left, right+1)
    return left+a+c, right+b+d



def dyck_word(tree):
    if tree is None:
        return ()
    left, right = tree
    return (1,) + dyck_word(left) + (-1,) + dyck_word(right)


def word_area(tree):
    height = area = 0
    for step in dyck_word(tree):
        area += height
        height += step
    return area


def check_growth():
    for d in range(8):
        counts = Counter()
        crossings = Counter()
        old_areas = Counter()
        for old in trees(d):
            s, mirror = depths(old)
            assert s == word_area(old)
            k = (s-d)//2
            old_areas[k] += 1
            increments = []
            for new in grow(old):
                counts[new] += 1
                increment = word_area(new)-s
                increments.append(increment)
                assert increment % 2 == 1
                crossings.update(range(k, k+(increment-1)//2))
            j = 2*d
            assert len(increments) == 2*(j+1) and min(increments) > 0
            assert sum(increments) == 2*(j+1) + 5*s + mirror
        assert set(counts) == set(trees(d+1)) and set(counts.values()) == {d+2}
        new_areas = Counter((word_area(tree)-d-1)//2 for tree in trees(d+1))
        for k in range(max(new_areas)+1):
            assert (crossings[k]-crossings[k-1]
                    == 2*(2*d+1)*old_areas[k]-(d+2)*new_areas[k])


def check_lengths(bounds=ORIGINAL, *, real_mass_bound=None):
    M, r = bounds.min_length, bounds.max_root
    EPS = 1/sqrt_lo(M)
    local = 1+bounds.length_window+Q('.000001')
    scale = 1+bounds.length_window+Q('.00001')
    r2 = r*r
    small = 1/sqrt_lo(Q('.9')*M)
    assert exp_small_upper(Q(1))**bounds.log_floor < M < 1/decay(bounds.log_floor+1)
    assert scale*local*sqrt_hi(local)*r**3 < bounds.shifted_tilt
    if real_mass_bound is None:
        log_cost = small*(bounds.shifted_tilt*(4+Q('1.26')*3*(10+5*small)+Q('.5'))+3*2500)
        bad = 4*decay(Q(9)/Q('1.344'))
        real_mass_bound = (Q('1.0001')*(exp_small_upper(log_cost)+small**8)
                           /((1-bad)*(1-5*decay(44))))
    assert real_mass_bound < Q('1.39')
    # 1-b*(j/m)^(3/2) <= (1-b)_+ + 1.5*(1-j/m)_+.
    deficit = scale-1 + Q('1.5')*(local-1)
    assert Q('1.39')*Q('1.0001')*exp_small_upper(Q('1.17')*r2*deficit) < Q('1.5')
    assert Q('1.39')/sqrt_lo(Q('.9'))*Q('1.0001')*exp_small_upper(Q('1.17')*(Q('.75')+r2*deficit)) < Q('3.8')
    assert 2-local-1/(2*Q('2.35')**2) > Q('.9')
    assert Q('3.8')*Q('1.1')*2/(1-2*Q(r2,M)) < 9
    assert Q('1.5')*Q('1.27') < 2 and Q('1.5')*Q('2.31') < Q('3.5')
    assert Q('3.5')*local**2 < Q('3.51') and 2*local/2 < Q('1.01')
    assert sqrt_hi(PI_HI*(local/2+Q(1,M)))/2 < Q('.64')
    assert 1/(local/2+Q(1,M)) > Q('1.99')
    assert 3*9/(2-local) < 28
    assert Q('2.1')*Q('.26')/Q('2.35') < Q('.79')
    # Coefficients in the one-step derivative and the even second difference.
    assert 9*Q('.64')*(local+Q(1,M))/4 < 2
    assert Q('3.51')/4 < Q('.9')
    assert Q('.501')*28 < 15 and Q('.501')*Q('4.5')+Q("5.1")*9*EPS < 3
    assert ((2*sqrt_hi(Q('3.5'))+sqrt_hi(Q('1.5'))*EPS)**2*Q('1.001')**2 + 8*EPS**2)/4 < 4
    assert scale*(1+Q('1.01')) < Q('2.1') and 2*scale < Q('2.1')
    assert Q('.9')*scale+Q('3.51')*scale**2/8 < Q('1.4')
    assert (sqrt_hi(Q(1,2))+4*EPS)**2 < Q('.51')
    assert exp_small_upper(Q('.02'))*(17*2*local+12+6*EPS)/16 < 4
    assert (33*Q('3.5')+Q('1.01')*Q('1.5')/M)*exp_small_upper(bounds.placement_log+Q('.02'))/512 < bounds.variance_cost


def check_exceptions(bounds=ORIGINAL):
    M, r = bounds.min_length, bounds.max_root
    EPS = 1/sqrt_lo(M)
    local = 1+bounds.length_window+Q('.000001')
    lower_log, upper_log = bounds.log_floor, bounds.log_floor+1
    h = r**3
    b = Q('1.17')*r**2
    x = b+4*upper_log+30
    assert M*bounds.length_window**2 > b+4*upper_log+50
    assert h*(17*local**2+6*local+Q(4,M))*EPS/16 < Q('.02')
    assert h*Q('1.17')*sqrt_hi(upper_log*x/M) < bounds.placement_log
    assert Q('2.3')**2/(4*Q('1.2')*local) > 1
    assert (Q('1.99')-Q('.51')/sqrt_lo(lower_log))**2/2 > Q('1.4')+Q('1.4')/lower_log
    assert Q('1.17')*sqrt_lo(lower_log) > Q('2.3')/2*sqrt_lo(lower_log)+Q('.25')*EPS
    assert 42*sqrt_hi(M)*decay(30)*(2+530000*10*sqrt_hi(upper_log)) < Q('.79')*Q(M)**2
    assert (70*(1+r*r)+(30+5*r*r+h)*h+bounds.quadratic_cost*h*h)/M < Q('.001')
    # Check the retained-area concentration for every local skeleton length.
    geom_mean = (1+bounds.length_window)/(1-bounds.length_window)
    eu = exp_small_upper(Q('.01'))
    assert geom_mean*(1+geom_mean)*eu/(1-geom_mean*(eu-1))**2 < Q('2.4')
    assert Q('2.3')*sqrt_hi(x/M)/(Q('2.4')*(1-bounds.length_window)) < Q('.01')
    assert local*geom_mean*(1+geom_mean) < Q('2.01')
    # Collect coefficients after the sum over dyadic lengths. Each tuple
    # represents 1, r^2, q, r^2 q, r^3 q, q^2 respectively.
    for c, length, dil, rest, target in zip(
        (0, Q('13.5'), 3, 0, 0, 0),
        (0, 15, 2, 6, 3, 4),
        (0, 0, Q('2.1'), Q('2.1'), 0, Q('1.4')),
        (10, 0, 4, 0, 0, bounds.variance_cost),
        (70, 70, 30, 5, 1, bounds.quadratic_cost),
    ):
        total = Q(4,3)*(c+Q('.51')/8*length+Q(1,2)*dil+rest)
        assert total + int(target == 30) <= target


def check_tilted_height():
    # Ground approximation to the real half-meander Laplace transform.
    # The second eigenvalue exceeds 3.837 by cutting at the first node.
    b, t = Q('3.837'), Q('6.60')
    assert PI_LO**2/Q('1.5')**2 > b and Q('2.337')+Q('1.5') == b
    assert (t/8)**3 < Q('.75')**2
    # Integrate (1+x)(1+x^2/3) against t exp(-t(x-b)) from b up.
    moments = [sum(comb(j,i)*b**(j-i)*factorial(i)/t**i for i in range(j+1))
               for j in range(4)]
    mass = moments[0]+moments[1]+(moments[2]+moments[3])/3
    assert mass*decay(t*(b-Q('2.339'))) < Q('.003')
    # Linear interpolation of (1+v)^(-4/3) bounds the Taylor remainder
    # of (1+w)^(2/3), with |w| <= 1/4.
    assert Q('1.47')**3*Q('.75')**4 > 1
    exponent = Q('2.339')/18*(1+Q('.47')/3)
    variance = 2*(Q('1.003')/Q('.997')*exp_small_upper(exponent)-1)
    assert 12*variance*Q('.48')**2 < 1
    assert Q('2.339')/(3*16)+Q('2.7')/16**2 < Q(1,16)


def check_inversion(bounds=ORIGINAL):
    M, rmax = bounds.min_length, bounds.max_root
    EPS = 1/sqrt_lo(M)
    cost = bounds.quadratic_cost
    peak = Q(0)
    # Enclose the integral by nonnegative polynomials on each tilt interval.
    for i in range(235, 100*rmax):
        lo, hi = Q(i,100), Q(i+1,100)
        hlow, h = max(Q(13),lo**3), hi**3
        if h < hlow:
            continue
        height = max(sqrt_lo(6/PI_HI), lo/Q('2.34'))
        if bounds == SHORT and lo >= 4:
            height = max(height, Q('.48')*lo*lo)
        if lo < 7:
            rate, ratio = (Q('.16'), 60) if hi <= 4 else (Q('.15'), 40)
            b = min(h/2, Q('1.17')*hi*hi)
            t = max(ratio*h, sqrt_hi(((27+b)/rate)**3))
        else:
            ratio = next(Q(y) for start,y in reversed(CUTS) if lo >= Q(start))
            t = ratio*h
            height = max(height, Q('.21')*lo*lo)
        poly = (70*(1+hi**2)+(30+5*hi**2+h)*h+cost*h*h, 30+5*hi**2+h, cost)
        a = Q('1.001')/hlow
        loss = sum(c*(t**(j+1)/(j+1)+a*t**(j+2)/(j+2)) for j,c in enumerate(poly)) / (PI_LO*M*height)
        peak = max(peak,loss)
        assert t < 125000 and a*t**3/(6*PI_LO*M*sqrt_lo(M)) < Q('.001')
    assert peak < Q('.91'), float(peak)
    height = sqrt_lo(M)/rmax
    assert 2000*(1+2)/height**4 < Q('.00001') and 100*150 < height*PI_LO
    assert height > 60000 and Q(M,300*10**6) >= 2500
    assert 200*3**800*300**5*decay(Q(2500,25))**25 < Q('.0001')
    # Small-tilt tail, with both frequency signs, both laws and the centered
    # lattice normalizer. The exponential margin stays 27 at every cutoff.
    rate = Q('.15')
    umax = 27 + Q('1.17')*49
    gamma = ((umax+1)/(sqrt_lo(27)*rate*sqrt_lo(rate))
             + Q('1.001')*(umax**2+2*umax+2)/(13*rate**3))
    assert Q('1.001')*300/PI_LO*decay(27)*gamma < Q('.003')
    assert 9*343*EPS/100 + 343*EPS**3 < Q('.0001')  # T^(2/3) > 100
    for start,cut in CUTS:
        r = Q(start)
        n = Q('.49')*r*r
        tail = Q(0)
        for i,(left,_,_,rate) in enumerate(BANDS):
            if Q(left) < Q(cut):
                continue
            right = Q(BANDS[i+1][0]) if i+1 < len(BANDS) else 150
            env = min(20000*decay(Q(rate)*(n-4)), Q('1.03')*decay(Q(rate)*(n-20)))
            tail += 12*r/Q('.21')*(right-Q(left))*(1+Q('1.001')*right)*env
        assert tail < Q('.022'), (r,float(tail))
    return peak


if __name__ == '__main__':
    check_growth()
    check_tilted_height()
    for bounds in (ORIGINAL, SHORT):
        check_lengths(bounds)
        check_exceptions(bounds)
        peak = check_inversion(bounds)
        print(f'Lengths >= {bounds.min_length}, root <= {bounds.max_root}, '
              f'relative inversion error < {float(peak)+.0001:.4f}.')
