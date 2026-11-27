"""Gaussian contour and frequency bands for the positive-tilt corank sign."""

from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial

from verify_folded_saddle import upper_exp
from verify_hit_tilts import exp_bound
from verify_return_bounds import cube_hi
from verify_rising import PI_HI, PI_LO, decay, sqrt_hi, sqrt_lo
from verify_tilted_thinning import TiltRange, check_lengths, check_exceptions

A_LO, A_HI = Q('2.337'), Q('2.339')
M = 2*10**10
RANGE = TiltRange(M, Q('12.5'), Q('.00015'), 1960, 23, Q('1.44'), Q('1.00'), Q('2.7'))


def gaussian_even(degree):
    """Moment for exp(-v^2)/sqrt(pi)."""
    half = degree//2
    return Q(factorial(degree),4**half*factorial(half))


def gaussian_factor(power, min_a):
    # Real part of E (1+iv)^p(1-i*2A*v^3/3) for Var(v)=1/(2A).
    coefficients = [Q(0)]*(power+1)
    for j in range(power+1):
        if j%2 == 0:
            coefficients[j//2] += (-1)**(j//2)*comb(power,j)*gaussian_even(j)
        else:
            coefficients[(j+1)//2] += (Q(2,3)*(-1)**(j//2)*comb(power,j)
                                       *gaussian_even(j+3))
    lower = sum(min(0,v)/min_a**i for i,v in enumerate(coefficients))+1
    # The absolute Taylor remainder is <= (2/9) A^2 v^6 (1+v^2)^ceil(p/2).
    degree = (power+1)//2
    rem = sum(Q(2,9)*comb(degree,l)*gaussian_even(6+2*l)/min_a**(l+1)
              for l in range(degree+1))
    return lower-rem


def check_density():
    b = Q('3.837')
    min_a = A_LO**3/(18*Q('.25')**2)
    assert 3*b*b/(54*Q('.25')**2)>13
    upper = sum(comb(3,j)*gaussian_even(2*j)/min_a**j for j in range(4))
    moments = [sum(comb(j,l)*b**(j-l)*factorial(l)/Q(13)**l
                   for l in range(j+1)) for j in range(10)]
    poly = moments[6]+moments[7]+(moments[8]+moments[9])/3
    tail = upper*poly/A_LO**6*exp_bound(-(b**3-A_HI**3)/(54*Q('.25')**2))
    assert tail < Q('.01')
    small = gaussian_factor(6,min_a)-tail
    assert 3*small/(2*sqrt_hi(A_HI)) > Q('.4')
    # For fixed a, r^6 exp(-a r^2/6) decreases for a r^2 > 18.
    assert A_LO*(A_LO/(3*Q('.25')))**2 > 18
    for x,order,target in [(Q('.145'),1,Q('.105')),(Q('.25'),0,Q('.30'))]:
        r = A_HI/(3*x)
        lower_exp = 1/upper_exp(A_HI*r*r/6)
        p = 3+3*order
        factor = gaussian_factor(p,A_LO**3/(18*x*x))-tail
        if order == 1:
            # The coefficient .4 is uniform for x <= .25.
            result = Q('.4')*(A_LO/(3*x))**6*lower_exp
        else:
            result = 3/(2*sqrt_hi(A_HI))*factor*(A_LO/(3*x))**3*lower_exp
        assert result > target,(x,float(result))
    assert Q('.4')*Q('7.001')**6 / upper_exp(A_HI*Q('7.001')**2/6) > Q('.0001')
    # With h=r^3 and x=a/(3r), de-tilting the derivative cancels
    # the entire leading exponential of the real Laplace transform.
    factor = gaussian_factor(6,A_LO*49/2)-tail
    assert 3*factor/(sqrt_hi(2*PI_HI*A_HI)*Q('1.003')) > Q('.701')
    assert 3*(upper+tail)/(sqrt_lo(2*PI_LO*A_LO)*Q('.997')) < 2


def check_peak():
    m = 2*10**6
    # The largest shift d/(2N)^(3/2) is <= (m+1)/m^(3/2).
    shift = (1+Q(1,m))/sqrt_lo(m)
    assert Q('.6')+shift < Q('.601') and Q('.145')+shift < Q('.147')
    assert Q('1.78')/upper_exp(6*Q('.601')**2) > Q('.20')
    loss = Q('1.78')*(1-exp_bound(-6*(Q('.25')-Q('.147'))**2))
    # Integral of t exp(-.19 t^(2/3)) on [0,infinity) is 3/.19^3.
    rounding = 300/(Q('.19')**3*PI_LO*m*sqrt_lo(m))
    assert rounding < Q('.001') and loss > Q('.10') > 2*Q('.0033')+rounding
    # On the intermediate interval, |z-z_0| <= 1/m.
    assert A_LO/(3*(A_LO/21-Q(1,M))) < Q('7.001')


def real_mass_bound():
    i = Q('.9')*M
    u = RANGE.shifted_tilt
    height = sqrt_lo(i)/cube_hi(Q(u))
    assert height > 10000 and Q('6.6')**3 < (Q('7')*sqrt_lo(Q('.9')))**3*Q('.99984')
    assert 1270*decay(Q('1.48')*(Q('.499')*Q('6.6')**2-Q('2.01'))) < Q('.001')
    exponent = Q('1.25')*u/sqrt_lo(i)+A_HI/(2*height**2)+33*u*u/i**2
    bound = Q('1.05')*Q('1.001')/Q('.997')*sqrt_hi(1+2/i)*upper_exp(exponent)
    assert bound < Q('1.11')
    assert (500000+u)/(2*M*sqrt_lo(M)) < Q(1,10**10)
    return bound


# Lower endpoint |t|/h, block length in H^2, Holder power, certified rate.
BANDS = [
    (4,'1.075',6,'.076'), (5,'.95',5,'.112'), (6,'.875',4,'.153'),
    (7,'.825',3,'.194'), (8,'.75',3,'.240'), (9,'.7',3,'.284'),
    (10,'.65',3,'.327'), (11,'.625',2,'.371'), (12,'.60',2,'.422'),
    (13,'.575',2,'.472'), (14,'.55',2,'.520'), (15,'.525',2,'.568'),
    (16,'.50',2,'.614'), (18,'.45',2,'.704'), (20,'.425',2,'.79'),
    (25,'.375',2,'.99'), (30,'.325',2,'1.18'), (35,'.30',2,'1.36'),
    (45,'.25',2,'1.70'),
]


def check_bands():
    height = sqrt_lo(M)/RANGE.max_root
    assert 2000*3/height**4 < Q('.00001')
    for left,v,p,rate in BANDS:
        v,rate=Q(v),Q(rate)
        assert 2*p*v*150/height < PI_LO and v*height**2 > 10000
        z = (Q('.999')*v)**3*left**2/16
        moment = sum(comb(4*p,2*p+j)*exp_bound(-j*j*z) for j in range(-2*p,2*p+1))/2**(4*p)
        cost = A_HI*(1-1/cube_hi(Q(p,p-1)))+Q('.00001')
        assert moment*upper_exp(p*v*(rate+cost)) < 1, left
    assert Q('2.01')/PI_LO < Q('.65')
    assert height**3/64 > 10000 and Q(2)/height**2 < Q('.001')


@lru_cache(None)
def end_factor(rate, bound):
    # Choose integer quarter-block lengths independently at the two ends.
    return min(sqrt_hi(1+(bound*bound-1)*exp_bound(-2*Q('1.48')*(Q(j,4)-Q('1.0001'))))
               *upper_exp(rate*Q(j,4)) for j in range(5,29))


def inversion_bound(lo,hi):
    h, hmin = hi**3,lo**3
    height = Q('.70')*lo**2
    blocks = Q('.4999')*lo*lo
    cost = RANGE.quadratic_cost
    poly = (70*(1+hi**2)+(30+5*hi**2+h)*h+cost*h*h,30+5*hi**2+h,cost)
    tail = Q('.003')
    choices = []
    for i in reversed(range(len(BANDS))):
        left,v,p,rate = BANDS[i]
        right = BANDS[i+1][0] if i+1<len(BANDS) else 150
        rate,v = Q(rate),Q(v)
        env = end_factor(rate,8)*end_factor(rate,158)*exp_bound(-rate*(blocks-v-Q('.001')))
        tail += Q('.65')*h/height*(right-left)*(1+Q('1.001')*right)*env
        t = left*h
        central = sum(c*(t**(j+1)/(j+1)+t**(j+2)/((j+2)*hmin))
                      for j,c in enumerate(poly))/(PI_LO*M*height)
        multiplier = t**3/(6*PI_LO*M*sqrt_lo(M)*hmin*height)
        choices.append(tail+central+multiplier)
    return min(choices)


def verify_inversion():
    assert Q('.5')*(1-Q(1,M)) > Q('.4999')
    assert Q('12.5') > 16*A_HI/3
    assert 45*RANGE.max_root**3 < 500000
    assert RANGE.max_root**3/(M*sqrt_lo(M)) < Q('.0001')
    result = max(inversion_bound(Q(i,100),Q(i+1,100)) for i in range(700,1250))
    assert result < Q('.80'), float(result)
    return result


if __name__ == '__main__':
    check_density()
    check_peak()
    check_lengths(RANGE,real_mass_bound=real_mass_bound())
    check_exceptions(RANGE)
    check_bands()
    bound = verify_inversion()
    print(f'Small-area derivative and both tilted signs checked, loss below {float(bound)+.0001:.4f}.')
