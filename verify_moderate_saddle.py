"""Rational bounds for the ballot Fourier inversion at moderate height scales."""

from fractions import Fraction as Q
from math import comb

from verify import ballot_ranks, direct_ranks
from verify_airy_grid import sample_bounds
from verify_folded_saddle import folded_center, power_residual, upper_exp
from verify_hit_tilts import exp_bound
from verify_rising import PI_LO, gaussian_moment, sqrt_hi, sqrt_lo
from verify_saddle_phase import HARMONICS, real_power_below


MESH = Q(1, 23)
AIRY = Q('2.339')
CORE = Q('.4')
BANDS = [('.4', '.6', '1.6', '.23'), ('.6', '1', '2.5', '.20'),
         ('1', '1.4', '4', '.18'), ('1.4', '2', '7', '.24'),
         ('2', '2.5', '12', '.24'), ('2.5', '3', '26', '.24'), ('3', '3.25', '43', '.17')]


# The shorter core covers the first old harmonic band. The rate at 5 is
# rounded down by another .001 for H >= 23.
HOLDER_BANDS = [(lo, hi, p, v, '.144' if lo == 5 else rate)
                for lo, hi, p, v, rate in HARMONICS[1:]]


def real_basis_norms():
    def moments(a):
        values = [Q(1)]
        for j in range(1,16):
            values.append((2*j*a*values[-1]+Q(j*(j-1)*(j-2),2)*values[max(0,j-3)])
                          /(2*j+1))
        return values
    hi, lo = moments(AIRY), moments(Q('2.337'))
    return ([sqrt_hi(hi[2*k]) for k in range(8)],
            [sqrt_hi(AIRY*hi[2*k]-lo[2*k+1]+k*(2*k-1)*hi[max(0,2*k-2)]) for k in range(8)])


def complex_basis_norms(real_energy, imaginary_energy):
    # Upper bounds on the raw moments of |f|^2. The current identity
    # gives a recurrence after completing a square, including the factor
    # on the left that must stay positive.
    moments = [Q(1), 2*AIRY/3]
    for j in range(2,16):
        error = imaginary_energy**2/(2*(j+1)**2*(j+2))
        denominator = 2*j+1-error*real_energy
        assert denominator > 0
        moments.append((2*j*real_energy*moments[j-1]
                        + Q(j*(j-1)*(j-2),2)*moments[max(0,j-3)]
                        + error*Q(j*(j-1),2)*moments[j-2])/denominator)
    return ([sqrt_hi(moments[2*k]) for k in range(8)],
            [sqrt_hi(real_energy*moments[2*k]+k*(2*k-1)*moments[max(0,2*k-2)]) for k in range(8)])


def real_power(y):
    """Bracket Re((1+iy)^(2/3)) by its cubic."""
    lower, upper = Q(1), Q(2)
    for _ in range(32):
        mid = (lower + upper)/2
        if real_power_below(y, mid):
            upper = mid
        else:
            lower = mid
    return lower, upper


def eigenvalue_residual(y, d=MESH):
    tilt = sqrt_hi(1+y*y)
    energy = next(Q(i,100) for i in range(233,550)
                  if Q(i,100)**3 >= AIRY**3*tilt**2)
    real_energy = AIRY*real_power(y)[1]
    return power_residual(tilt, energy, d, basis_norms=complex_basis_norms(real_energy,min(energy,2*AIRY*y/3)))


def check_real_estimates():
    d = Q(1,20)
    # Real nodal cut at 1.5 H. Lower bounds for sin(x)/d and the tail gap.
    assert (PI_LO/(Q('1.5')+d)*(1-(Q('3.142')*d/Q('1.5'))**2/6))**2 > Q('4.08')
    assert (1-Q('2.60')*d*d)*(Q('1.5')-Q('1.5')**2*d*d/2) > Q('1.48')
    residual = power_residual(Q(1), AIRY, d, basis_norms=real_basis_norms())
    assert residual < 64
    # The real trial eigenvalue exceeds lambda_2 by much more than its residual.
    assert Q('1.65')+Q('1.48')*(1-Q('2.60')*d*d) > Q('2.60')
    assert AIRY**2*d/30 < Q('1.5')
    assert (Q('2.60')-AIRY)*(1-Q('2.60')*d*d) > 64*d**4
    assert 64/(1-AIRY*d*d-64*d**6) < 65
    assert AIRY+65*d**4 < Q('2.34')
    # Real grid quadrature and the positive unit single-step eigenvector.
    d = Q(1,21)
    norm, f, corr = sample_bounds(Q(1), AIRY, Q(1), d, basis_norms=real_basis_norms())
    assert norm(corr,grid=True) < Q('.68')
    assert (2*AIRY/3 + 2*norm(f,2))/8 + Q('.68') < Q('2.5')
    for fn, order, pot, cap in [(f,2,0,12), (f,0,1,Q(28,5)), (f,1,1,5),
                                 (f,0,0,3), (corr,0,0,Q('2.1')), (corr,1,0,9)]:
        assert norm(fn,order,pot) + norm(fn,order,pot+1) < cap
    # Recover the unnormalized single-step residual from the two-step formula.
    assert 64 / (2*sqrt_lo(2)) < 23
    assert Q('.74')-64*d**4 > Q('.73')
    assert 23*sqrt_hi(2)/((1-Q('2.5')*d*d)*Q('.73')) < 46
    assert AIRY/3 < 1
    quad = (6+(Q('5.6')+2*d*8)/4+Q('2.1')+18*d)*d*d
    error = (quad+Q('2.5')*d*d)/(1-Q('2.5')*d*d)+4*46*d**3
    assert 1+error < Q('1.05')
    assert (1-error)*(1-d**3/4)*(1-Q('2.34')*d*d)**2 > Q('.94')
    # Peeling real end vectors separately.
    scale = upper_exp(Q('2.34')*(1+d*d))
    assert scale/(sqrt_lo(2)*(1-d**3/4)*(1-Q('2.34')*d*d)) < 8
    assert 10*sqrt_hi(2)*scale/Q('.94') < 158
    assert 8*158 < 1270
    shrink = exp_bound(-Q('1.48')*(Q('4.5')-d*d))
    assert (1+(8*shrink)**2)*(1+(158*shrink)**2) < Q('1.022')**2
    # Ground-state height variance after the real nodal gap.
    d = Q(1,20)
    assert 2*(1/Q('1.48')+(Q('2.34')+d/2)**2) < Q('3.6')**2


def check_core():
    d = Q(1,20)
    assert eigenvalue_residual(CORE,d) < 104
    delta = 104*d**4
    loss = AIRY*CORE**2/9 + 65*d**4 + Q('.184')*Q(2,9)*d*d*CORE**2
    shift = Q('1.8')*CORE*d*d
    sine = sqrt_hi(2*(loss+delta)/Q('1.48'))
    q0 = sine + shift
    assert (2*sine+shift)**2 < 1-Q('.81')**2
    assert Q('.74')*(1-q0**2)-delta/Q('.8') > Q('.67')
    assert Q('.67')-loss-Q('1.3')*delta > Q('.60')
    assert 1/Q('.8')+delta/(Q('.8')**2*Q('.60')) < Q('1.3')
    assert 2/(Q('.8')*Q('.60')) < Q('4.3')
    assert Q('.81')-Q('8.6')*delta > Q('.8')
    assert Q('.74')*(1-(q0+Q('8.6')*delta)**2) > Q('.67')
    assert Q('1.3')*104/(1-(loss+Q('1.3')*delta)*d*d) < 136
    assert 2*Q('2.337')/9-Q(4,9)*Q('.184')*d*d > Q('.518')
    assert 2*AIRY/9 < Q('.520') and AIRY**2/30 < Q('.184')
    assert Q(8,27)*(AIRY+Q('.184')*d*d) < Q('.70')
    assert Q('2.337')*(Q(1,9)-Q(56,81*24)*CORE**2)-Q(2,9)*Q('.184')*d*d > Q('.24')
    assert Q('1.022')/Q('.8') < Q('1.28')
    assert Q('2.337')-Q('5.5')**2*d*d/30 > 3*d/2
    # At any point of the complex disk around beta, apply the same result
    # centered at its real part. The analytic error then vanishes to order
    # two on subtracting its true value and linear term.
    radius = Q('.37')
    assert 23**3 > 20**3*(1+radius)
    assert radius**2/(1-radius**2) < CORE**2
    assert 136*(1+radius)**2 < 256
    d = MESH
    for split, cap, centered in [('.245','.024',True), ('.20','.019',False)]:
        split, cap = Q(split), Q(cap)
        assert 256*d**4/(radius*(radius-split)) < cap
        assert ((136+65)/split**2+(256/(radius*split) if centered else 0))*d**4 < cap
    assert (Q('.24')-Q('.019'))/Q('.520') > Q('.424')
    slope_error = 256*d**4/radius
    assert 2*AIRY/3 + 4*AIRY**2*d*d/90 + slope_error < Q('1.57')
    assert 2*(1/Q('1.48')+(Q('1.57')+d/2)**2) < Q('2.6')**2
    for lo, hi, factor, rate in BANDS:
        lo, hi, factor, rate = map(Q,(lo,hi,factor,rate))
        lower, upper = real_power(hi)
        delta = eigenvalue_residual(hi)*d**4
        loss = AIRY*(upper-1)+65*d**4+Q('.184')*Q(2,9)*d*d*hi**2
        gap = Q('1.48')*(2-Q('1.48')*d*d)
        shift = Q('1.3')*hi*d*d
        overlap = sqrt_lo(1-2*(loss+delta)/gap)-shift
        assert overlap > 0
        projection = sqrt_hi(1-overlap**2)+2*shift+1/factor
        per_square = Q('2.337')*(lower-1)/hi**2-Q('.184')*Q(2,9)*d*d-65*d**4/lo**2
        if lo < Q('1.4'):
            assert gap*(1-projection**2)/2 > rate*hi**2
            assert per_square*(1-loss*d*d/2)-factor*delta/lo**2 > rate
        else:
            assert gap*(1-projection**2)/2 > rate
            assert per_square*lo**2*(1-loss*d*d/2)-factor*delta > rate


def check_short_walk():
    d, w = MESH, Q('.24')
    assert Q(23,21)**3 > 1+w
    assert (1-w)**4 * (3*Q('.600')/Q('.520')-2)**3 > 1
    assert 19**3*(1-w)**2 > 15**3
    assert 1270*exp_bound(-Q('1.48')*(15-2-Q('.01'))) < Q('.001')
    loss = Q('.600')*w*w/2 + 65*d**4*(1+(1+w)**2)+256*d**4*w/Q('.37')
    mgf = Q('1.001')/Q('.999')*Q('1.05')/Q('.94')*upper_exp((19+d*d)*loss)
    assert 2*(mgf-1)/w**2 < 21


def check_harmonics():
    d = MESH
    for lo,hi,p,v,rate in HOLDER_BANDS:
        lo,hi,v,rate = map(Q,(lo,hi,v,rate))
        b = Q(p,p-1)
        assert 23**3 >= b*20**3
        root = next(Q(i,100000) for i in range(100000,0,-1) if b*i**3 <= 100000**3)
        energy = AIRY*(1-root) + 65*d**4*(1+b)
        moment = Q(comb(4*p,2*p),2**(4*p))
        for j in range(1,2*p+1):
            length = min(v,PI_LO/(2*j*hi*d))-d*d
            z = lo**2*j*j*(4*length**3-v*d**4)/48
            assert z > 0
            moment += Q(2*comb(4*p,2*p+j),2**(4*p))*exp_bound(-z)
        assert upper_exp(p*v*(energy+rate))*moment < 1, lo
        assert 2*(Q('5.5')+d*d)+v < 13


def check_far_arc():
    top = Q('.08')
    assert (PI_LO-2*top)**3 > Q('6.5')**3*top
    assert (Q('.83')/(2*Q('.12'))-Q('3.25'))**3 > top**2
    assert 2*(1-2*(1+MESH**2)/70) > Q('1.94')
    assert (Q('.12')*Q('1.94')-Q(1,25))**3*45**2 > Q('2.34')**3
    # On [.08, .5] the first harmonic of a shorter paired block suffices.
    assert Q(1,2)+2*Q('.8') < PI_LO
    assert Q('.8')**3 > Q('.5')
    assert (1+exp_bound(-Q('.5')))/2*upper_exp(Q('.21')) < 1
    assert Q('.21')/(2*(2+Q('.8')**2)) > Q('.039')
    assert (Q('1.94')*Q('.039')-Q(1,80))**3*(top*23**3)**2 > Q('2.34')**3
    assert (Q('1.94')/75-Q(1,80))**3*(Q('.5')*23**3)**2 > Q('2.34')**3
    for start, divisor in [(12,25),(95,80)]:
        assert start**3 < (45 if divisor == 25 else top*23**3)**2
        assert (2*3810*sqrt_hi(Q('.520')*70)**3*Q(3,2)*start**4
                *exp_bound(-Q(70,divisor)*start)/(Q(70,divisor)-Q(4,start))) < Q('.0005')


def outside(low, vhi, order):
    """In growth use the full modulus of the first-difference multiplier."""
    total = Q(0)
    def weighted_interval(lo, hi):
        if order == 0:
            return (hi-lo)*sqrt_hi(1+hi*hi)
        return (hi**(order+1)-lo**(order+1))/(order+1)
    for lo,hi,factor,rate in BANDS:
        lo,hi,factor,rate = map(Q,(lo,hi,factor,rate))
        if lo < Q('1.4'):
            for i in range(int(100*lo), int(100*hi)):
                y, top = Q(i,100), Q(i+1,100)
                total += factor*weighted_interval(y,top)*exp_bound(-rate*(low-Q('11.01'))*y*y)
        else:
            total += (factor*weighted_interval(lo,hi)*exp_bound(-rate*(low-Q('11.01'))))
    for lo,hi,_,_,rate in HOLDER_BANDS:
        lo,hi,rate = map(Q,(lo,hi,rate))
        total += weighted_interval(lo,hi)*exp_bound(-rate*(low-13))
    # The two far-tail bounds cover powers through two. In growth
    # sqrt(1+y^2) <= 1 + |y| gives twice this tail allowance.
    return 2*Q('1.022')*vhi**(order+1)*total+(Q('.002') if not order else Q('.001'))


def signed_bound(low, order):
    d = MESH
    v = sqrt_lo(Q('.518')*(low-19-d*d))
    vhi = sqrt_hi(Q('.520')*(low-19))
    cutoff = CORE*v
    def moment(j):
        return 2*gaussian_moment(j,Q('.424'))
    def weighted_moment(j):
        return moment(j+2)/ (2*v**2)+moment(j) if order == 0 else moment(j+2)
    if order == 0:
        main = (Q('.999')*sqrt_lo(2*PI_LO)
                *(1/upper_exp(Q(21,2)/v**2)-Q('.608')/v))
        tail_weight = 1/cutoff+(cutoff+1/cutoff)/(2*v**2)
    else:
        main = Q('.999')*sqrt_lo(2*PI_LO)*(1-Q(63,2)/v**2)
        tail_weight = cutoff+1/cutoff
    tail = Q('2.002')*exp_bound(-cutoff**2/2)*tail_weight
    exponent = Q('1.001')*(Q('.024')/Q('.518')*weighted_moment(2)
                            + Q('.70')/(6*Q('.518')*v)*weighted_moment(3))
    rb = Q('1.28')*exp_bound(-Q('.67')*(19-Q('11.01')))
    rn = Q('1.28')*exp_bound(-Q('.67')*(low-Q('11.01')))
    remainder = rb*weighted_moment(0) + 3*rn*(CORE*vhi)**(order+1)
    core_norm = (Q('1.001')+rb)*moment(0)+2*rn*CORE*vhi
    core_second = (Q('1.001')+rb)*moment(2)+2*rn*(CORE*vhi)**3/3
    extra = Q('.0001')*core_second if order else 0
    return main-tail-exponent-remainder-outside(low,vhi,order)-extra, core_norm+outside(low,vhi,0)


def check_corank_ranges():
    d = MESH
    for n in range(2,4096):
        for delta in (0,1):
            center = folded_center(n+delta)
            assert (2*n+delta)**3 < (16*((center+1)//2))**2
    for n, root in ((4096,Q(16)), (38000,Q('33.61'))):
        assert root**3 <= n
        assert (Q('1.0816')*root-Q('1.75')-Q(1,4096)
                > Q('2.00025')*sqrt_hi(Q('2.00025')*n)/16)
    slope_at_23 = 2*AIRY/(3*d)-Q('1.5')+4*AIRY**2*d/90+256*d**3/Q('.37')
    assert Q('1.0816')*Q('33.61')-Q('1.75') > slope_at_23
    assert 35 > slope_at_23
    slope = 2*Q('2.337')/3-Q('1.5')*d-256*d**4/Q('.37')
    assert 16**2*slope**2/Q('2.00025')**3 > 71
    for divisor, threshold in [(25,168), (26,185)]:
        assert 27*1000 < (35*divisor)**2
        assert divisor**2*slope**2/Q('2.001')**3 > threshold
    assert Q('.30')*slope**4/(2*Q('2.75')*Q('.520')) > Q('.5')
    assert 2*(Q('5.5')+d*d) < Q('11.01')
    assert Q('1.001')**2*exp_bound(-Q(1)) < Q('.608')**2
    assert 1/(1-d**3/2) < Q('1.001')
    assert (CORE*d**3)**2/12 < Q('.0001')
    # The slowest polynomial times exponential error in the frequency
    # bands decreases at all of the applicable block counts.
    assert Q(3,2)/(71-19) < Q('.23')*CORE**2


def check_small_rows():
    shapes = comparisons = 0
    for m, ranks in ballot_ranks(12):
        coranks = direct_ranks(range(m-1,0,-2))[::-1]
        assert ranks[::-1] == coranks
        shapes += 1
        if m//2 >= 2:
            for k in range(len(coranks)-1):
                if (16*k)**2 <= m**3:
                    assert coranks[k+1] > coranks[k]
                    comparisons += 1
    print(f'Direct partitions agree in {shapes} whole rows; {comparisons} growth checks.')


if __name__ == '__main__':
    check_small_rows()
    check_real_estimates()
    check_core()
    check_short_walk()
    check_harmonics()
    check_far_arc()
    check_corank_ranges()
    for blocks, order, lower_bound in [(71,0,'.06'), (168,2,'.03'), (185,2,'.30')]:
        margin, norm = signed_bound(blocks,order)
        assert margin > Q(lower_bound)
        if blocks == 185:
            assert norm < Q('2.75')
        print(f'Order {order} for N >= {blocks}: signed integral > {lower_bound}.')
    print('Verified strict growth through m^(3/2)/16 for every n >= 2 in both families.')
