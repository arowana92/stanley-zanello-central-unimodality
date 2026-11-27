"""Excursion-center inequalities and the common all-size corank interval."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product

from verify import ballot_ranks, direct_ranks
from verify_airy_grid import sample_bounds
from verify_airy_powers import check_high_saddle, check_power_decay
from verify_rising import PI_LO, exp_small_upper, sqrt_hi, sqrt_lo


def degree_sum(n, parity):
    """Sum the n lowest degrees of the indicated slots, with multiplicity."""
    degree = total = 0
    while n:
        count = (degree+2)**2 // 4
        first = 2 + 2*parity
        if degree >= first and (degree-first) % 4 == 0:
            count += 1
        used = min(n, count)
        total += used*degree
        n -= used
        degree += 1
    return total


def planar_minimum(size):
    degrees = sorted(a+b for a in range(size) for b in range(size))
    return sum(degrees[:size])


@lru_cache(maxsize=None)
def forest_minimum(size, level):
    if level == 0:
        return planar_minimum(size)
    return min(2*level*j + planar_minimum(j) + forest_minimum(size-j,level-1)
               for j in range(size+1))


def check_centers():
    for m, ranks in ballot_ranks(40):
        n, parity = divmod(m, 2)
        center = degree_sum(n, parity)
        if n <= 12:
            assert ranks == direct_ranks(range(m-1, 0, -2))
            assert center == min(2*u*(u+parity) + forest_minimum(n-u,2*u+parity)
                                 for u in range(n+1))
        coranks = ranks[::-1]
        assert all(coranks[i] < coranks[j] for i in range((center+1)//2)
                   for j in range(i+1,center-i+1))

    # Test the excursion areas and all reachable offsets independently on words.
    for m in range(2, 15):
        offsets = set()
        for word in product((-1,1), repeat=m):
            height = area = 0
            unmatched = []
            for i,step in enumerate(word):
                if step == 1:
                    unmatched.append(i)
                elif unmatched:
                    unmatched.pop()
                else:
                    break
                height += step
                area += height//2
            else:
                offset = height**2//4
                internal = 0
                cuts = [-1] + unmatched + [m]
                for level, (left,right) in enumerate(zip(cuts,cuts[1:])):
                    part = word[left+1:right]
                    offset += level*(len(part)//2)
                    local = 0
                    for step in part:
                        if step == 1:
                            internal += local
                        local += step
                    assert local == 0
                offsets.add(offset)
                assert offset+internal == area
        assert offsets == set(range(m*m//4+1))


def check_extended_sample():
    # The imaginary segment from 1-i to 1+i.
    T, E, d = Q("1.42"), Q(3), Q(1,220)
    assert Q("2.339")**3*T**2 < E**3
    bound, f, F = sample_bounds(T,E,Q(1),d)
    c = T*d**3/4
    assert T*T/32*exp_small_upper(c) < Q(".07")
    assert T/4 < Q(".36")
    airy = (bound(f,6)/120 + bound(f,potential=3,grid=True)/48
            + bound(f,2,2,True)/16 + bound(f,4,1,True)/48
            + T*bound(f,1,1,True)/8 + T*bound(f,3)/8 + Q(".07")*bound(f,grid=True))
    correction = (bound(F,4)/6 + bound(F,potential=2,grid=True)/8
                  + bound(F,2,1,True)/4 + Q(".36")*bound(F,1)
                  + Q(".07")*d*d*bound(F,grid=True))
    F0 = bound(F,grid=True)
    b = E/2 + E**2*d**2/60
    assert b**3/6 + E**3/120 + E**4*d**2/7200 < 1
    assert b*b/2 + E**2/60 < Q("1.3")
    assert airy+correction+bound(f,grid=True)+Q("1.3")*F0 < 290
    even = (1-2*d*sqrt_hi(E))/sqrt_hi(2) - d*d*F0
    assert 2*exp_small_upper(3*d**3/4)*290 / (even*(1-Q("2.60")*d*d)) < 900
    assert Q("1.6")**3 > T**4
    assert Q("2.339")**2/30*(1+Q("1.6")) + 2000*d*d < Q(".60")
    check_power_decay(d, Q(".60")*d*d, 900*d**4)

    # Real terminal sums at the saddle and its two shifted arguments.
    d = Q(1,210)
    bound, f, F = sample_bounds(Q(1),Q("2.34"),Q(1),d)
    assert (2*Q("2.34")+2*bound(f,2))/8 < 3
    assert bound(F,grid=True) < 4
    sample_lo = 1-7*d*d
    assert Q("1.48")/2 - 600*d**4 > Q(".73")
    assert 201*sqrt_hi(2)/(sample_lo*Q(".73")) < 400
    for func, order, maximum in ((f,2,26),(F,0,12),(F,1,35)):
        assert bound(func,order) + bound(func,order,1) < maximum
    total = (Q(26,2)+(21+106*d)/4+12+70*d)*d*d
    relative = (2*total+7*d*d)/sample_lo + 3200*d**3
    assert relative < Q(".003")
    assert (1-relative)*(1-d**3/4)*(1-Q("2.60")*d*d)**2 > Q(".99")
    assert Q(220,210)**3 > Q("1.08") and Q(12*45,220) < PI_LO
    check_high_saddle(h=220, energy_bound=Q("2.339"))


def check_join():
    assert Q(".858")**3 < Q(3,8)**3*12
    for n in range(2,64):
        for parity in (0,1):
            cap = (degree_sum(n,parity)+1)//2
            # All integers k <= s/70 satisfy k+1 <= cap.
            assert (2*n+parity)**3 < (70*cap)**2
    for n, cubert_lo in ((64,4), (70000000,412)):
        assert cubert_lo**3 <= n
        assert Q(".858")*cubert_lo-Q("2.016")*sqrt_hi(Q("2.016")*n)/70 > 2+Q(1,64)
    h = 220
    slope = (2*Q("2.339")/3 + 4*Q("2.339")**2/(90*h*h)
             + Q(2000,h**4)/Q(".12"))
    assert Q(".858")*412-2 > slope*h
    assert 70**2*(2*Q("2.337")/3-Q(".016"))**2 / Q("2.001")**3 > 1450


if __name__ == "__main__":
    check_centers()
    check_extended_sample()
    check_join()
    print("Verified excursion centers, the height-220 saddle and both all-size corank intervals.")
