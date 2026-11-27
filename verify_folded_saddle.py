"""Rational bounds for the marked-return comparison and real-moment saddle test."""

from fractions import Fraction as Q
from itertools import combinations
from math import comb

from verify import ballot_ranks, direct_ranks
from verify_airy_grid import sample_bounds
from verify_hit_tilts import exp_bound
from verify_rising import PI_LO, decay, exp_small_upper, sqrt_hi, sqrt_lo

HEIGHT = 114
MIN_BLOCKS = 360
MESH = Q(1, HEIGHT)
ENERGY = Q("2.339")


def upper_exp(x):
    """Positive exponential bound, including block powers larger than two."""
    steps = max(1, x.__ceil__())
    return exp_small_upper(x / steps) ** steps


def check_real_moment():
    # Refine the real boundary sums at both shifted heights.
    d = Q(1, 110)
    norm, f, corr = sample_bounds(Q(1), Q("2.34"), Q(1), d)
    assert (2*Q("2.34") + 2*norm(f, 2)) / 8 < 3
    assert norm(corr, grid=True) < 4
    assert 201*sqrt_hi(2) / ((1-7*d*d)*Q(".73")) < 400
    assert Q("1.48")/2 - 600*d**4 > Q(".73")
    for fn, order, bound in ((f, 2, 26), (corr, 0, 12), (corr, 1, 35)):
        assert norm(fn, order) + norm(fn, order, 1) < bound
    quadrature = (Q(26, 2) + (21+106*d)/4 + 12 + 70*d)*d*d
    error = (2*quadrature+7*d*d)/(1-7*d*d) + 3200*d**3
    assert (1-error)*(1-d**3/4)*(1-Q("2.60")*d*d)**2 > Q(".99")
    assert 1+error < Q("1.01")
    # The mass is normalized at the saddle, not at a displaced mean.
    width = 1/sqrt_lo(MIN_BLOCKS)
    assert (Q(HEIGHT,110))**3 > 1+width
    assert (1-width)**2 > Q(".94")**3 and MIN_BLOCKS*Q(".94") > 330
    assert 20000*decay(Q("1.48")*327) < Q(".001")
    root_variance = Q(2,9)*ENERGY + 2*Q(2000,110**4)/Q(".12")**2
    assert root_variance**3 < Q(".565")**3*(1-width)**4
    moment = 2*(Q("1.001")/Q(".999")*Q("1.01")/Q(".99")*upper_exp(Q(".565")/2)-1)
    assert moment < Q(".714")
    # Peel ceil(12 H^2) pairs at either end. The real component ratios
    # individually start below 20000 after ceil(H^2) pairs.
    assert 1+(20000*decay(Q("1.48")*10))**2 < Q("1.001")
    assert Q("1.001")/Q(".999") < Q("1.003")


def power_residual(T, E, d, *, basis_norms=None):
    """Upper bound in units of d^6 for the normalized two-step residual."""
    norm, f, corr = sample_bounds(T, E, Q(1), d, basis_norms=basis_norms)
    hyper = T*T/32*upper_exp(T*d**3/4)
    airy = (norm(f,6)/120 + norm(f,potential=3,grid=True)/48
            + norm(f,2,2,True)/16 + norm(f,4,1,True)/48
            + T*norm(f,1,1,True)/8 + T*norm(f,3)/8 + hyper*norm(f,grid=True))
    correction = (norm(corr,4)/6 + norm(corr,potential=2,grid=True)/8
                  + norm(corr,2,1,True)/4 + T*norm(corr,1)/4
                  + hyper*d*d*norm(corr,grid=True))
    exponent = E/2+E**2*d*d/60
    scalar = exponent**3/6 + E**3/120 + E**4*d*d/7200
    correction_scalar = exponent**2/2+E**2/60
    residual = (airy+correction+scalar*norm(f,grid=True)
                + correction_scalar*norm(corr,grid=True))
    even = (1-2*d*sqrt_hi(E))/sqrt_hi(2)-d*d*norm(corr,grid=True)
    return 2*upper_exp(3*d**3/4)*residual/(even*(1-Q("2.6")*d*d))


def check_sample_and_powers():
    T, E, d = Q("1.74"), Q("3.4"), MESH
    assert T*T > 1+Q("1.4")**2 and E**3 > ENERGY**3*T**2
    assert power_residual(T, E, d) < 2100
    delta = 2100*d**4
    assert T**4 < Q("2.1")**3
    assert ENERGY**2/30*(1+Q("2.1"))+2000*d*d < Q(".80")
    err = Q(".80")*d*d
    assert Q("1.4")*(2*Q("1.8")+d) < Q("2.4")**2
    for low, high, B, rate in ((".08",".5","1.63",".23"),
                               (".5","1","4",".14"), ("1","1.4","20",".047")):
        lo, hi, B, rate = map(Q, (low, high, B, rate))
        loss = ENERGY*hi**2/9 + err
        dist = sqrt_hi(2*(loss+delta)/Q("1.48")) + Q("2.4")*d
        assert Q(".74")*(1-(dist+1/B)**2) > rate*hi**2
        if hi <= Q(".5"):
            lower = Q("2.337")*(Q(1,9)-Q(56,81*24)*hi**2)
        else:
            # arctan(y)/y is decreasing. Through 1 use pi/4 and through
            # 1.4 use arctan(1.4) = pi/4 + arctan(1/6).
            angle = PI_LO/4 if hi == 1 else (PI_LO/4+Q(1,6)-Q(1,6)**3/3)/hi
            lower = Q("2.337")*Q(".83")*Q(".97")*angle/9
        assert (lower-err/lo**2)*(1-loss*d*d/2)-B*delta/lo**2 > rate
    assert (1+Q("1.4")**2)*Q(".83")**6 < 1
    assert 1-Q(".34")**2/6 > Q(".97")
    # Core energy for arbitrarily small frequencies. Its complementary
    # transform has the pre-existing full-length bound exp(20-.16 N).
    assert (Q("2.337")*Q(".109")-Q(2,9)*Q(".264")*d*d
            -2000*d**4/(Q(".12")**2-Q(".08")**2)) > Q(".25")
    assert Q("1.003")/(1-Q("5.52")*Q(".08")) < Q("1.81")
    assert Q("1.003")*Q("1.63") < Q("1.64")


# Harmonics of mirrored label pairs in a block of floor(v H^2) pairs.
# Each tuple gives lower and upper |theta|/beta, power p, length v and decay.
BANDS = [
    ("1.4","1.5",30,"1.15",".013"), ("1.5","1.6",24,"1.20",".015"),
    ("1.6","1.75",24,"1.15",".017"), ("1.75","1.9",20,"1.15",".020"),
    ("1.9","2.1",16,"1.15",".023"), ("2.1","2.4",16,"1.1",".028"),
    ("2.4","3",12,"1.15",".037"), ("3","5",8,"1.10",".055"),
    ("5","12",4,".90",".12"), ("12","45",4,".40",".24"),
]


def check_harmonics():
    for left, right, p, length, rate in BANDS:
        lo, hi, v, rate = map(Q,(left,right,length,rate))
        b = Q(p,p-1)
        assert HEIGHT**3 >= b*100**3
        # Find an outward lower bound for b^(-1/3).
        root = next(Q(i,10000) for i in range(10000,0,-1) if b*i**3 <= 10000**3)
        energy = ENERGY*(1-root) + Q(2000,HEIGHT**4)*(1+b)
        min_length = v - MESH**2
        z = (4*min_length**3 - v*MESH**4)*lo**2/48
        mass = Q(comb(4*p,2*p), 2**(4*p))
        for j in range(1,2*p+1):
            rho = exp_bound(-z*j*j) if j*v*hi/HEIGHT <= PI_LO/2 else 1
            mass += Q(2*comb(4*p,2*p+j), 2**(4*p))*rho
        assert upper_exp(p*v*(energy+rate))*mass < 1, (left, rate)
        assert 2*(12+MESH**2)+v < 26


def integral_margin(N, prefactor):
    # z = sqrt(N) theta/beta. Positive mass on the core by the second moment.
    a = Q("2.1")
    slope = Q("1.001")/sqrt_lo(N)
    main = 2*a-Q(".714")*a**3/3-slope*a*a
    c = Q(".23")*(1-Q(25,N))
    # Monotone upper bound on the two Gaussian tails (integrate the linear
    # weight at its right endpoint). The tail above 10 uses a tangent line.
    tails = Q(0)
    left = a
    while left < 10:
        right = left + Q(1,100)
        tails += (right-left)*(1+slope*right)*exp_bound(-c*left*left)
        left = right
    tails += exp_bound(-100*c)*((1+10*slope)/(20*c)+slope/(20*c)**2)
    outside = 2*prefactor*tails
    for left, right, factor, rate in ((".5","1","4.02",".035"),
                                      ("1","1.4","20.1",".047")):
        length = Q(right)-Q(left)
        outside += (2*sqrt_hi(N)*length*(1+Q("1.001")*Q(right))*Q(factor)
                    *exp_bound(-Q(rate)*(N-25)))
    for left, right, _, _, rate in BANDS:
        length = Q(right)-Q(left)
        outside += (2*sqrt_hi(N)*length*(1+Q("1.001")*Q(right))*Q("1.003")
                    *exp_bound(-Q(rate)*(N-26)))
        assert 2*N*Q(rate) > 1
    # Higher lattice frequencies, including |theta| > 1/64.
    assert 2*(1-Q(25,N)) > Q("1.85")
    assert (Q(".124")*Q("1.85")-Q(1,80))**3 * 45**2 > Q("2.61")**3
    assert (Q("1.85")/75-Q(1,80))**3 * (Q(HEIGHT**3,64))**2 > Q("2.61")**3
    # Extract half the exponential, substitute t=y^(2/3), integrate the rest.
    assert 6*sqrt_hi(N)*Q(3,2)*(2+Q("1.001")*2)*exp_bound(-Q(N*12,160)) < Q(".001")
    assert Q(".17")*sqrt_hi(N)/Q(".999")*exp_bound(20-Q(".16")*N) < Q(".001")
    margin = main-outside-Q(".002")
    assert margin > Q(".05"), float(margin)
    return margin


def check_fourier():
    check_real_moment()
    check_sample_and_powers()
    check_harmonics()
    assert Q("2.1")/sqrt_hi(600) >= Q(".08")
    assert 1/(1-MESH**3/2) < Q("1.001")
    for n, factor in ((MIN_BLOCKS,Q("1.64")), (600,Q("1.81"))):
        margin = integral_margin(n, factor)
        print(f"At N >= {n} the normalized integral margin exceeds {int(1000*margin)/1000:.3f}.")


def check_curvature():
    """Weighted inversion of the shorter-walk Gaussian at the same saddle."""
    n = 2100
    d = MESH
    grid_error = 2000 * d**4
    variance_lo, variance_hi = Q(".515"), Q(".523")
    assert (2*Q("2.337")/9 - Q(4,9)*Q(".264")*d*d
            - 2*grid_error/Q(".12")**2) > variance_lo
    assert 2*ENERGY/9 + 2*grid_error/Q(".12")**2 < variance_hi
    cubic = (Q(8,27)*(ENERGY+Q(".264")*d*d)/Q(".92")**3
             + 6*grid_error/Q(".04")**3)
    assert cubic < Q("2.1") and Q(".25") / variance_hi > Q(".47")
    assert Q(HEIGHT,110)**3 > Q("1.08")
    assert Q(".68")**3*Q(".92")**4 > Q(".60")**3
    assert Q("1.001")*Q("1.06")*upper_exp(Q(".34")*201*Q(".08")**2) < Q("1.65")
    assert 2*(Q("1.65")/Q(".999")-1)/Q(".08")**2 < 205

    lo = sqrt_lo(variance_lo*(n-201))
    hi = sqrt_hi(variance_hi*n)
    u = Q(".08")*lo
    main = sqrt_lo(2*PI_LO)*Q(".999")*(1-Q(3*205,2)/lo**2)
    gaussian_tail = 2*Q("1.001")*(u+1/u)*exp_bound(-u*u/2)
    cubic_cost = 2*Q("1.001")*Q("2.1")/(6*variance_lo*lo*Q(".47")**3)
    core_norm = Q("1.001")*sqrt_hi(Q("3.14160")/Q(".47"))
    # The two complementary terms on the inner arc have one Gaussian and
    # one length-dependent bound. Cover both mass and second difference.
    core_error = (5*exp_bound(20-Q(".16")*200)
                  + (1+2*hi**3)*exp_bound(20-Q(".16")*n))
    assert core_error < Q(".001")
    assert (Q(".08")*d**3)**2 / 12 < Q(".0001")

    # Integral of x^2 outside the core. Normalize by the principal real mass.
    c = Q(".23")*(n-25)
    a = Q(".08")
    outside = (2*Q("1.64")*hi**3*exp_bound(-c*a*a)
               *(a/(2*c)+1/(4*c*c*a)))
    for left, right, factor, rate in ((".5","1","4.02",".035"),
                                      ("1","1.4","20.1",".047")):
        volume = Q(2,3)*hi**3*(Q(right)**3-Q(left)**3)
        outside += volume*Q(factor)*exp_bound(-Q(rate)*(n-25))
    for left, right, _, _, rate in BANDS:
        volume = Q(2,3)*hi**3*(Q(right)**3-Q(left)**3)
        outside += volume*Q("1.003")*exp_bound(-Q(rate)*(n-26))
        assert 2*Q(rate)*n > 3
    # Integral of y^2 exp(-N y^(2/3)/160) on y>=45 is below 36
    # by t=y^(2/3) and t^(7/2) <= t^4 on t>=1.
    assert 6*hi**3*36*exp_bound(-Q(n*12,160)) < Q(".001")
    outside += Q(".001")
    norm = core_norm + core_error + outside/u**2
    # On the core the sine multiplier differs from x^2 by <= .0001 x^2.
    assert Q("1.001")*sqrt_hi(Q("3.14160")/Q(".47"))/Q(".94") + core_error < 3
    margin = main - gaussian_tail - cubic_cost - core_error - Q(".0003") - outside
    assert margin > Q(".40") and norm < 3
    assert Q(".40")/(2*3*variance_hi)*(2*Q("2.337")/3-Q(".016"))**4 > Q(".5")
    assert 85**2*(2*Q("2.337")/3-Q(".016"))**2 / Q("2.001")**3 > n
    print(f"At N >= {n} the scaled curvature integral exceeds {int(1000*margin)/1000:.3f}.")


def folded_center(size):
    """Sum the size cheapest 4i+a+b over nonnegative triples."""
    total = degree = 0
    while size:
        count = sum(degree - 4*i + 1 for i in range(degree//4 + 1))
        used = min(size, count)
        total += used * degree
        size -= used
        degree += 1
    return total


def marked_dyck_row(m):
    """Enumerate marked ordinary Dyck paths, keeping the endpoint classes."""
    n, parity = divmod(m, 2)
    size = n + parity
    layers = [[0] * (n*(n+parity) + 1) for _ in range(n+1)]
    for downs in combinations(range(1, 2*size + 1), size):
        down = set(downs)
        height = area = 0
        shifts = []
        for position in range(1, 2*size + 1):
            height += -1 if position in down else 1
            if height < 0:
                break
            area += height//2
            if height == 0 and (position < 2*size or not parity):
                shifts.append(2*size-position+1-parity)
        else:
            weights = [(area, 0)]
            for shift in shifts:
                weights += [(v+shift, u+1) for v, u in weights]
            for v, u in weights:
                layers[u][v] += 1
    return layers


def check_folding():
    comparisons = 0
    for m, ranks in ballot_ranks(64):
        n, parity = divmod(m, 2)
        coranks = ranks[::-1]
        if n <= 9:
            layers = marked_dyck_row(m)
            assert coranks == list(map(sum, zip(*layers)))
            assert coranks == direct_ranks(range(m-1, 0, -2))[::-1]
            ell = n+parity
            for u, row in enumerate(layers):
                d = n-u
                assert sum(row) == comb(m, d) - (comb(m, d-1) if d else 0)
                center = 2*n*ell-d*(m+1)
                for k, (left, right) in enumerate(zip(row, row[1:])):
                    if left > right:
                        assert 2*k+1 > center
                        assert 9*(4*k+2+3*ell)**2*(u+1) > 32*ell**3
        if n == 1:
            continue
        center = folded_center(n+parity)
        for i in range((center+1)//2):
            for j in range(i+1, center-i+1):
                assert coranks[i] < coranks[j]
                comparisons += 1
        assert m**3 < (35*((center+1)//2))**2
    print(f"Marked Dyck paths and strict partitions agree through n=9. "
          f"{comparisons} strict folded-center comparisons through n=64.")


def check_join():
    assert Q("1.081")**3 < Q(3,8)**3*24
    join = 4_750_000
    for n, cube_root in ((64,4), (join,168)):
        assert cube_root**3 <= n
        assert (Q("1.081")*cube_root - 3
                > Q("2.016")*sqrt_hi(Q("2.016")*n)/35 + Q(1,64))
    slope = 2*ENERGY/3 + 4*ENERGY**2*MESH**2/90 + 2000*MESH**4/Q(".12")
    assert Q("1.081")*168 - 3 > slope*HEIGHT
    assert slope*HEIGHT < 178
    assert 35**2*(2*Q("2.337")/3-Q(".016"))**2 / Q("2.001")**3 > MIN_BLOCKS


if __name__ == "__main__":
    check_folding()
    check_join()
    check_fourier()
    check_curvature()
