"""Rational inverse-transform bounds for the two staircase saddle signs."""

from fractions import Fraction as Q
from math import comb

from verify import ballot_ranks, direct_ranks
from verify_folded_saddle import folded_center, power_residual, upper_exp
from verify_hit_tilts import exp_bound
from verify_rising import PI_HI, PI_LO, gaussian_moment, sqrt_hi, sqrt_lo


D = Q(1, 114)
A = Q('2.339')
CORE = Q('.4')
SIG_LO, SIG_HI = Q('.518'), Q('.520')
HARMONICS = [(3,'3.25',8,'1.10','.059'), ('3.25','3.5',7,'1.05','.068'),
             ('3.5',4,6,'1.05','.078'), (4,'4.5',5,1,'.099'),
             ('4.5',5,5,'.95','.121'), (5,6,4,'.9','.145'),
             (6,8,4,'.8','.19'), (8,12,4,'.65','.27'), (12,45,4,'.4','.24')]


def real_power_below(y, real_bound):
    """Upper bound for Re(1+iy)^(2/3) via its real cubic."""
    # 4 R^3 - 3(1+y^2)^(2/3) R = 1-y^2. The left side is
    # increasing from max(1,(1+y^2)^(1/3)/2) to infinity.
    assert (1+y*y) < 27 and real_bound >= 1
    assert 8*real_bound**3 > 1+y*y
    rhs = (4*real_bound**3 - (1-y*y))/(3*real_bound)
    return rhs > 0 and rhs**3 > (1+y*y)**2


def check_spectrum():
    assert Q('5.06')**2*D**2/30+3*D/2 < Q('2.337')
    delta = 2100*D**4
    loss = A*CORE**2/9+Q('.8')*D**2
    sine = sqrt_hi(2*(loss+delta)/Q('1.48'))
    q0 = sine+Q('2.4')*D
    assert (2*sine+Q('2.4')*D)**2 < 1-Q('.81')**2
    # Q A restricted to the oblique complementary space, and its resolvent.
    assert Q('.74')*(1-q0**2)-delta/Q('.8') > Q('.67')
    assert Q('.67')-loss-Q('1.3')*delta > Q('.60')
    assert Q(1)/Q('.8')+delta/(Q('.8')**2*Q('.60')) < Q('1.3')
    assert 2*delta/(Q('.8')*Q('.60')) < Q('4.3')*delta
    assert Q('.81')-Q('8.6')*delta > Q('.8')
    assert Q('.74')*(1-(q0+Q('8.6')*delta)**2) > Q('.67')
    assert Q('1.003')/Q('.8') < Q('1.26')
    assert Q('1.3')*2100/(1-(loss+Q('1.3')*delta)*D**2)+2000 < 4800
    assert 2000/Q('.12') < 17000
    assert 2*Q('2.337')/9-Q(4,9)*(A*A/30)*D**2 > SIG_LO
    assert 2*A/9 < SIG_HI
    assert Q(8,27)*(A+A*A*D**2/30) < Q('.7')
    assert (Q('2.337')*(Q(1,9)-Q(56,81*24)*CORE**2)
            -Q(2,9)*A*A*D**2/30) > Q('.24')
    assert Q('.24')/SIG_HI > Q('.46')
    # Use dissipation at both parity half-steps in the outer Airy band.
    t, e = Q('3.17'), Q('5.06')
    assert t*t > 10 and e**3 > A**3*t*t
    assert power_residual(t,e,D) < 25200
    delta = 25200*D**4
    assert t**4 < 5**3
    assert A*A/30*6+2000*D**2 < Q('1.26')
    assert 3*(Q('3.6')+D) < Q('3.3')**2
    shift = Q('3.3')*D
    assert real_power_below(Q(3),Q('1.451'))
    loss = A*Q('.451')+Q('1.26')*D**2
    gap = Q('1.48')*(2-Q('1.48')*D**2)
    overlap = sqrt_lo(1-2*(loss+delta)/gap)-shift
    bound = sqrt_hi(1-overlap**2)+2*shift+Q(1,35)
    assert gap*(1-bound**2)/2 > Q('.14')
    assert Q('1.003')*35 < Q('35.2')
    y0, test = Q('1.4'), Q('1.10')
    assert ((4*test**3-(1-y0*y0))/(3*test))**3 < (1+y0*y0)**2
    assert (Q('.2337')-Q('1.26')*D**2)*(1-loss*D**2/2)-35*delta > Q('.14')
    for lo,hi,factor,rate,prefactor in [('.4','.6','1.6','.235','1.61'),
                                        ('.6','1','2.5','.21','2.51'),
                                        ('1','1.4','4','.185','4.02')]:
        lo,hi,factor,rate,prefactor = map(Q,(lo,hi,factor,rate,prefactor))
        # Bisect the increasing branch of the real cubic at the far endpoint.
        lower, upper = Q(1), Q(2)
        for _ in range(24):
            mid = (lower+upper)/2
            if real_power_below(hi,mid):
                upper = mid
            else:
                lower = mid
        loss = A*(upper-1)+Q('1.26')*D**2
        lower_rate = Q('2.337')*(lower-1)/hi**2
        # Re[(1+iy)^(2/3)-1]/y^2 decreases, by the Stieltjes integral.
        assert ((lower_rate-Q('1.26')*D**2/lo**2)*(1-loss*D**2/2)
                -factor*delta/lo**2) > rate
        shift = sqrt_hi(hi*(Q('3.6')+D))*D
        overlap = sqrt_lo(1-2*(loss+delta)/gap)-shift
        bound = sqrt_hi(1-overlap**2)+2*shift+1/factor
        assert gap*(1-bound**2)/2 > rate*hi**2
        assert Q('1.003')*factor < prefactor


def check_harmonics():
    for left,right,p,v,rate in HARMONICS:
        lo,hi,v,rate = map(Q,(left,right,v,rate))
        b = Q(p,p-1)
        assert 114**3 >= b*100**3
        root = next(Q(i,10000) for i in range(10000,0,-1) if b*i**3 <= 10000**3)
        energy = A*(1-root) + 2000*D**4*(1+b)
        z = (4*(v-D**2)**3-v*D**4)*lo**2/48
        moment = Q(comb(4*p,2*p), 2**(4*p))
        for j in range(1,2*p+1):
            rho = exp_bound(-z*j*j) if j*v*hi*D <= PI_LO/2 else 1
            moment += Q(2*comb(4*p,2*p+j), 2**(4*p))*rho
        assert upper_exp(p*v*(energy+rate))*moment < 1, left
        assert 2*(12+D**2)+v < 26


def check_short_walk():
    assert Q(114,110)**3 > Q('1.1')
    assert (2*A/9+4000/Q(110**4)/Q('.12')**2)**3 < Q('.61')**3*Q('.9')**4
    bmax = 32 + D*D
    assert 32*Q('.9')-Q('2.01') > 26
    assert 20000*exp_bound(-Q('1.48')*26) < Q('.001')
    mgf = Q('1.001')/Q('.999')*Q('1.01')/Q('.99')*upper_exp(Q('.61')/2*bmax/100)
    assert 200*(mgf-1) < 26


def outer_integral(low, hi_v, order):
    # Contributions beyond |y|=.4, for the mass, derivative, or curvature.
    total = Q(0)
    for lo, hi, factor, rate in [(40,60,'1.61','.235'), (60,100,'2.51','.21'),
                                  (100,140,'4.02','.185')]:
        for i in range(lo,hi):
            y, top = Q(i,100), Q(i+1,100)
            bound = Q(factor)*exp_bound(-Q(rate)*(low-25)*y*y)
            total += Q(1,100)*top**order*bound
    total += ((Q(3)**(order+1)-Q('1.4')**(order+1))/(order+1)
              *Q('35.2')*exp_bound(-Q('.14')*(low-25)))
    for lo, hi, _, _, rate in HARMONICS:
        lo, hi = Q(lo), Q(hi)
        total += ((hi**(order+1)-lo**(order+1))/(order+1)
                  *Q('1.003')*exp_bound(-Q(rate)*(low-26)))
    return 2*hi_v**(order+1)*total + Q('.001')


def certify(low, high, curvature):
    length_lo = low-32-D**2
    length_hi = high-32
    v = sqrt_lo(SIG_LO*length_lo)
    vhi = sqrt_hi(SIG_HI*length_hi)
    cutoff = CORE*v
    exp_error = 4800*D**4*length_hi
    factor = Q('1.001')*upper_exp(exp_error)
    # All Gaussian moments below are on the full line.
    def moment(j):
        return 2*gaussian_moment(j,Q('.46'))

    j = 2 if curvature else 0
    main = (sqrt_lo(2*PI_LO)*Q('.999')
            *(1-Q(26,2)*(3 if curvature else 1)/v**2))
    assert main > 0
    gauss_tail = 2*Q('1.001')*exp_bound(-cutoff**2/2)
    gauss_tail *= cutoff+1/cutoff if curvature else 1/cutoff
    exponent_error = factor*(exp_error*moment(j)
                      + 17000*D**4*length_hi/v*moment(j+1)
                      + Q('.7')/(6*SIG_LO*v)*moment(j+3))
    rb = Q('1.26')*exp_bound(-Q('.67')*(32-25))
    rn = Q('1.26')*exp_bound(-Q('.67')*(low-25))
    remainder = (rb*upper_exp(exp_error)*moment(j)
                 + 2*rn*(CORE*vhi)**(j+1)/(j+1))
    outside = outer_integral(low,vhi,j)
    # Core absolute integrals, using the damped eigenvalue and short measure.
    def core_abs(order):
        return ((factor+rb*upper_exp(exp_error))*moment(order)
                + 2*rn*(CORE*vhi)**(order+1)/(order+1))
    if curvature:
        extra = Q('.0001')*core_abs(2)
    else:
        extra = Q('1.001')*(core_abs(1)+outer_integral(low,vhi,1))/v
    margin = main-gauss_tail-exponent_error-remainder-outside-extra
    norm = core_abs(0)+outer_integral(low,vhi,0)
    return margin, norm


def check_tails():
    # Peel only ceil(H^2) pairs at each end in the far tails. At 96
    # height-scale blocks this leaves more than 1.95 n single steps.
    assert 2*(1-2*(1+D**2)/96) > Q('1.95')
    assert (Q('.124')*Q('1.95')-Q(1,30))**3*45**2 > Q('2.61')**3
    assert (Q('1.95')/75-Q(1,80))**3*Q(114**3,64)**2 > Q('2.61')**3
    # Substitute t=y^(2/3); through order two the polynomial power is
    # <= t^4 for y>=45. Bound t^4 <= t0^4 exp(4(t-t0)/t0).
    for floor, divisor in [(12,30),(700,80)]:
        assert floor**3 < (45 if divisor == 30 else Q(114**3,64))**2
        decay_rate = Q(96,divisor)
        assert (2*60000*sqrt_hi(SIG_HI*96)**3*Q(3,2)*floor**4
                *exp_bound(-decay_rate*floor)/(decay_rate-Q(4,floor))) < Q('.0005')


def check_intermediate_range():
    # The real trial point is separated from every eigenvalue except the top.
    d = Q(1,26)
    assert power_residual(Q(1),Q('2.34'),d) < 252
    assert Q('2.65')-d > Q('2.60') and A*A*d/30 < Q('1.5')
    assert (Q('2.60')-A)*(1-Q('2.60')*d*d) > 252*d**4
    assert 252/(1-A*d*d-252*d**6) < 260
    d = Q(1,28)
    w = Q('.05')
    assert Q(28,26)**3 > 1+w
    assert (2*A/9)**3 < Q('.61')**3*(1-w)**4
    assert Q(4,9)*A**2/30*d*d/(1-w) < Q(2,9)*Q('2.337')/(1+w)**2
    for x in (Q(0),d):
        error = Q('.61')*w/2+260*(1+(1+w)**2)*x**4/w
        assert 2*A/3-Q('1.5')*x+4*A*A*x*x/90+error < Q('1.575')
    assert 2*Q('2.337')/3-Q('1.5')*d-error > Q('1.47')
    assert Q('1.0816')*Q('43.08')-Q('1.75') > 28*Q('1.575')
    assert 18**2*Q('1.47')**2/Q('2.00002')**3 > 87
    assert 114*((Q('1.575')+Q('1.75')/114)/Q('1.0816'))**3 < 365


def check_small_rows():
    for m, ranks in ballot_ranks(12):
        coranks = direct_ranks(range(m-1, 0, -2))[::-1]
        assert coranks == ranks[::-1]
        if m//2 >= 2:
            for k in range(len(coranks)-1):
                if (18*k)**2 <= m**3:
                    assert coranks[k+1] > coranks[k]
    print('Exact ballot ranks and direct partitions agree through twelve rows in both families.')


def check_coranks():
    for r in range(4):
        # Both sides are polynomials of degree at most three in h. Four
        # point comparisons of their difference prove the identity.
        const = (Q(r)+Q(7,2))**3-24*comb(r+2,2)
        assert const > 0
        for h in range(4):
            t = 4*h+r
            count = sum(comb(t-4*i+2,2) for i in range(h+1))
            assert (Q(t)+Q(7,2))**3-24*count == 19*h+const
    assert Q('1.0816')**3 < Q(3,8)**3*24
    for n in range(2,4096):
        for delta in (0,1):
            center = folded_center(n+delta)
            # If k is an integer with k <= s/18, then 2k+1 <= center.
            assert (2*n+delta)**3 < (18*((center+1)//2))**2
    for stop, divisor, root in [(80000,18,Q('43.08')), (4500000,34,Q('165.09'))]:
        for n,cube in ((4096,Q(16)),(stop,root)):
            assert cube**3 <= n
            assert (Q('1.0816')*cube-Q('1.75')-Q(1,4096)
                    > Q('2.00025')*sqrt_hi(Q('2.00025')*n)/divisor)
    assert Q('1.0816')*Q('165.09')-Q('1.75') > Q('176.3')
    assert (114*2*A/3-Q('1.5')+4*A*A*D/90+2000*D**3/Q('.12')) < Q('176.3')
    low_slope = 2*Q('2.337')/3-Q('.016')
    assert 18**2*low_slope**2/Q('2.001')**3 > 96
    assert 26**2*low_slope**2/Q('2.001')**3 > 190
    assert Q('.35')*low_slope**4/(2*Q('2.82')*SIG_HI) > Q('.5')
    assert (CORE*D**3)**2/12 < Q('.0001')


if __name__ == '__main__':
    check_small_rows()
    check_spectrum()
    check_short_walk()
    check_harmonics()
    check_tails()
    check_coranks()
    check_intermediate_range()
    for lo,hi,curvature in [(96,360,False),(190,2100,True)]:
        margins, norms = [], []
        for start in range(lo,hi,5):
            margin, norm = certify(start,min(start+5,hi),curvature)
            margins.append(margin)
            norms.append(norm)
        assert min(margins) > (Q('.35') if curvature else Q('.10'))
        assert max(norms) < (Q('2.82') if curvature else Q('2.90'))
        label = 'Curvature' if curvature else 'Growth'
        print(f'{label} on {lo} <= N <= {hi}: integral margin > {int(1000*min(margins))/1000:.3f}.')
    print('Verified the all-size and extended corank intervals for both families.')
