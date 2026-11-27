"""Exact pair-deletion, strip, and Fourier checks for thinning.md."""

from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import comb, isqrt

from verify import ballot_ranks, direct_ranks
from verify_rising import PI_HI, PI_LO, decay, exp_small_upper, sqrt_hi, sqrt_lo


def check_pair_law(max_n=12):
    """Rebuild each corank row by summing over its shorter uncolored walks."""
    for m, ranks in ballot_ranks(max_n):
        pairs = (m - 1) // 2
        extra = int(m % 2 == 0)
        row = [0] * len(ranks)
        # Packed polynomials in q, with a base larger than any coefficient.
        width = 8 * (m // 8 + 1)
        base = 1 << width
        for j in range(pairs + 1):
            w = pairs - j
            for moves in product((-1, 1), repeat=j):
                z = [0]
                for move in moves:
                    z.append(z[-1] + move)
                if min(z) < 0:
                    continue
                # Complete homogeneous polynomial of degree w in q^(2*z_i).
                holds = [1] + [0] * w
                for h in z:
                    for i in range(1, w + 1):
                        holds[i] += holds[i - 1] << (width * 2*h)
                end = z[-1]
                offset = 2*sum(z[:-1]) + (j + 3*end)//2 + extra*end
                packed = (holds[w] * (1 + base)**(w + extra)) << (width * offset)
                raw = packed.to_bytes((width // 8) * len(row), "little")
                counts = [int.from_bytes(raw[i:i + width//8], "little")
                          for i in range(0, len(raw), width//8)]
                total = sum(counts)
                assert total == comb(pairs, j) * 2**(w + extra)
                mean = Q(sum(k*b for k,b in enumerate(counts)), total)
                expected = (Q(2*(pairs + 1)*sum(z), j + 1) + Q(pairs-end, 2)
                            + extra*(end + Q(1, 2)))
                assert mean == expected
                slot_var = Q(sum(h*h for h in z), j+1) - Q(sum(z), j+1)**2
                variance = 4 * Q(w*(pairs+1), j+2) * slot_var + Q(w+extra, 4)
                assert Q(sum(k*k*b for k,b in enumerate(counts)), total) == mean**2 + variance
                row = [a + b for a,b in zip(row, counts)]
        assert row == ranks[::-1] == direct_ranks(range(m-1, 0, -2))[::-1]


def check_strips():
    # Test the stochastic reflection inequality at every trapezoid area threshold.
    for m in range(1, 14):
        groups = Counter()
        for steps in product((-1, 1), repeat=m):
            heights = [0]
            for step in steps:
                heights.append(heights[-1] + step)
            if min(heights) >= 0:
                twice_area = 2*sum(heights[:-1]) + heights[-1]
                groups[max(heights), heights[-1], twice_area] += 1
        for wall in range(m % 2, m+1, 2):
            for end in range(m % 2, wall+1, 2):
                signed = Counter()
                for (high, y, area), count in groups.items():
                    if high <= wall and y == end:
                        signed[area] += count
                        signed[2*m*wall-area] -= count
                cumulative = 0
                for key in sorted(signed):
                    cumulative += signed[key]
                    assert cumulative >= 0
                assert cumulative == 0


def check_thinning_constants():
    m = 10**8
    root = isqrt(m)
    window = Q("1.01")
    mass = Q("1.02")
    height1, height2 = Q("1.26"), Q("2.3")
    boundary = Q("2.1")
    assert (m+2)*PI_HI/(2*m) < height1**2
    assert (m+2)/(Q(".99")*m) < mass**2
    assert (1+3*window*m)*(m+2)*PI_HI/(2*m*m) < height2**2
    assert 2*mass/Q(".99") < boundary
    # Fixed-frequency length and frequency derivatives, divided by survival.
    assert max(height1/2, boundary/2) < Q("1.1")
    assert ((2*sqrt_hi(height2)+sqrt_hi(mass)/root)**2+7*mass/m)/4 < 4
    assert boundary*(Q(5,2*root)+Q(5,4)) < 8
    assert boundary*3/(2*Q(".99")) < 4
    s2 = window**2*height2/4
    assert s2 < Q(".59") and window*height2/4 < Q(".60")
    assert height1/2+3*boundary/4 < Q("2.3")
    c = Q("1.02")
    assert 1/Q(".99") < c
    assert c*(Q("2.3")+height1/2) < Q("3.1")
    assert c*Q(".60") + c*c*s2/2 < Q(".93")
    assert (sqrt_hi(Q(1,2))+Q(4,root))**2 < Q(".51")
    # Fine area conditional mean and variance in unscaled numerator units.
    assert 8/Q(".99")+(8+Q(4,m))/Q(".99")**2 < 17
    assert (8+Q(4,m))/Q(".99")-3 < 6
    assert height1*(17*window+6)+4*mass/root < 32
    assert 16*Q("1.01")*(2+Q(1,m))/Q(".99")*height2+mass*window/m < 76
    assert Q(76,512) < Q(".16")
    # Exceptional binomial lengths and the exact survival normalization.
    # m^(3/2) exp(-m/40000) decreases from m=10^8.
    assert 4*height1*root**3*decay(Q(m,40000)) < Q(".001")
    assert (1+Q(1,m))**2 > Q(4*(m+2),4*m+1)
    assert (1-Q(1,m))**2 < Q(4*m,4*m+3)
    length_remainder = Q(".51")/2
    assert Q("3.3")+length_remainder+1+Q(".001") < 5
    assert Q("3.3")+2*length_remainder+Q("3.1")/2+2 < 8
    assert length_remainder+Q(".93")/2+Q(".16") < 1
    assert 4*Q(5,3) < 7 and 4*Q(8,3)+height1/2 < 12 and Q(4,3) < Q("1.34")


def check_inversion():
    m, cutoff, rate = 2*10**13, 1200, Q(".19")
    scaled = (1000*rate)**3*cutoff**2
    z_int = next(z for z in range(100000) if z**3 >= scaled)
    lo, hi = Q(z_int-1, 1000), Q(z_int, 1000)
    for i, target in enumerate((".000016", ".015", "15.5")):
        b = Q(3*(i+1), 2)
        main = sum(Q(c*cutoff**(i+j+1), i+j+1) for j,c in enumerate((7,12,Q("1.34"))))
        tail = (300/PI_LO * sqrt_hi(1/rate)**(3*(i+1)) * decay(lo)
                * sqrt_hi(hi)**(3*(i+1)-2)/(1-(b-1)/lo))
        assert main/(m*PI_LO) + tail + Q(1,10**7) < Q(target)
    s = m*sqrt_lo(m)
    assert 8*Q(3,2)*200**5*12*decay(Q(m,2*10**8)) < Q(1,10**10)
    assert 8*Q(3,2)*100**5*12/(2*s) < Q(1,10**8)
    assert 8*Q(3,2)*100**8*2000/(12*s*s) < Q(1,10**8)
    # Strip estimate and the log-concavity slope test.
    a = Q(".18")
    exponent = PI_HI**2/(32*a*a)
    assert sqrt_lo(2*PI_LO)/(4*a*a*exp_small_upper(exponent/8)**8) > Q(".0013")
    assert Q(".0013")*exp_small_upper(Q(7,4))**4 < Q("1.78")
    assert Q(".0013")*7/Q(".47") > Q(".015")
    assert Q("1.78")/exp_small_upper(6*Q(".751")**2/2)**2 > Q(".015")
    assert 11*Q("1.78")/exp_small_upper(Q(1,12)) > Q("15.5")
    # Density error and mesh rounding localize every global maximizer.
    assert Q("1.78")*(1-decay(6*Q(".002")**2)) > 2*Q(".000016") + Q(1,10**8)
    assert 8*Q(3,2)*100**3*2/s < Q(1,10**8)


if __name__ == "__main__":
    check_pair_law()
    check_strips()
    check_thinning_constants()
    check_inversion()
    print("Both pair laws and moments match direct ranks through n=12.")
    print("All fixed-end strip comparisons pass through m=13.")
    print("Verified centered transform constants and the peak interval from n=10^13.")
