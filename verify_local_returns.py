"""Enclose the last-return residual at each rescaled time before inversion."""

from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial
from typing import NamedTuple

from verify_hit_tilts import exp_bound
from verify_return_bounds import add, cube_hi, diff, gaussian_norm, scale, times
from verify_rising import PI_HI, PI_LO, gamma_half, sqrt_hi, sqrt_lo

STEP = Q(1, 2)
EXCEPTION = Q(1, 10**16)
TINY = Q(1, 10**30)


class GammaWindow(NamedTuple):
    tau: Q
    relative: Q
    additive: Q
    tilt: Q
    final_relative: Q
    final_tilt: Q
    final_rate: Q


FINE = GammaWindow(Q(1,5000), Q('.1'), Q('.5'), Q('.06'), Q('.02'), Q('.015'), Q(1,6000))
COARSE = GammaWindow(Q('.0007'), Q('.12'), Q(1), Q('.12'), Q('.05'), Q('.04'), Q(1,1000))


@lru_cache(None)
def exp_neg(x):
    # Splitting the exponent keeps the floor of the fixed-point bound small.
    if x < 30:
        return exp_bound(-x)
    return exp_bound(-min(x, 300)/8)**8


def upper(x):
    return Q((x/TINY).__ceil__(), 10**30)


@lru_cache(None)
def peak_value(b, degree):
    return cube_hi(Q(b*degree,3)/Q('2.71'))**degree


def gauss(poly, b, lo, hi):
    """Monomial bounds on a closed interval, including interior maxima."""
    result = 0
    for j, coef in enumerate(poly):
        if not coef:
            continue
        if 3*lo**3 >= j*b:
            value = lo**j*exp_neg(lo**3/b)
        elif 3*hi**3 <= j*b:
            value = hi**j*exp_neg(hi**3/b)
        else:
            value = peak_value(b, j)
        result += abs(coef)*value
    return upper(result)


def excited_power(p):
    # Integral of (1+x) x^p (1+x^2/3) vs a shifted rate-one exponential.
    base = Q('3.837')
    moments = [sum(comb(j,l)*base**(j-l)*factorial(l) for l in range(j+1))
               for j in range(p+4)]
    return moments[p]+moments[p+1]+(moments[p+2]+moments[p+3])/3


EXCITED = [excited_power(p) for p in range(3)]


@lru_cache(None)
def airy(lo, hi):
    """Envelopes for f, f', f'' and the two correction functions."""
    root = sqrt_hi(hi)
    value, first, second = Q(1), Q('.75')*root, Q('.75')*hi
    quot = min(Q('.5'),hi*hi/8,1/lo if lo else Q('.5'))
    if lo >= 4:
        a = Q('2.339')
        sums = [(1+a)*a**p*exp_neg(Q('2.337')*lo/4)
                + EXCITED[p]*exp_neg(Q('3.837')*lo/4)
                for p in range(3)]
        invroot = 1/sqrt_lo(lo)
        value = min(value, Q('1.26')*root*sums[0])
        first = min(first, Q('.63')*(invroot*sums[0]+root*sums[1]))
        second = min(second, Q('1.26')*(invroot*sums[0]/(4*lo)
                     + invroot*sums[1]/2+root*sums[2]/4))
        quot = min(quot,Q('.63')*(invroot+root)*sums[0])
    corr = Q(8,15)*(hi*second+first/2)+Q('.35')*(first+quot)
    return tuple(map(upper,(value,first,second,corr)))


def symbol_bounds(b,c,quadratic,quintic,lo,hi,wide_lo,wide_hi,tau):
    """Bounds in units tau^2 for W_j-[g+tau D_g], and on [D_g]."""
    ell = [0,0,quadratic,0,0,quintic]
    powers = [[Q(1)]]
    for _ in range(4):
        powers.append(diff(powers[-1],b))
    corr = add(scale(ell,-1),add(scale(powers[1],-c),[0]+scale(powers[2],-Q(1,2))))
    if b == 24:
        log_rem = (13*hi/192+tau/64+(hi+tau)**4/384
                   +Q('.05')*(hi+tau)**7/1792)
    else:
        log_rem = ((7*hi**4+2*tau*hi**3)/(180*32**2)
                   +Q('.001')*(hi+tau)**7/1792)
    lattice = log_rem*exp_neg(lo**3/b)+gauss(times(ell,ell),b,lo,hi)/2
    gamma = (c*(1+c)*gauss(powers[2],b,lo,hi)/2
             +((2+3*c)*hi+6*tau)*gauss(powers[3],b,lo,hi)/6
             +(3*hi**2+26*hi*tau+24*tau**2)*gauss(powers[4],b,wide_lo,wide_hi)/24)
    first = diff(corr,b)
    second = diff(first,b)
    gamma += c*gauss(first,b,lo,hi)+(hi+2*tau)*gauss(second,b,wide_lo,wide_hi)/2
    assert max(gaussian_norm(powers[4],b),gaussian_norm(second,b),
               gaussian_norm(corr,b)) < 100
    return upper(lattice+gamma+EXCEPTION), upper(gauss(corr,b,wide_lo,wide_hi)+EXCEPTION)


def residual_grid(cutoff, window=FINE):
    free,bridge,correction,signed,V = [],[],[],[],[]
    for i in range(int(cutoff/STEP)+1):
        a,b = i*STEP,(i+1)*STEP
        lo = max(0,(1-window.relative)*a-window.additive)
        hi = (1+window.relative)*b+window.additive
        free.append(max(symbol_bounds(24,Q(1),p,Q(1,1920),a,b,lo,hi,window.tau)[0]
                        for p in [Q(1,32),Q(3,32)]))
        err,cnorm = symbol_bounds(96,Q(1,2),Q(1,192),Q(1,30720),a,b,lo,hi,window.tau)
        bridge.append(err)
        correction.append(cnorm)
        value,_,_,corr = airy(lo,hi)
        V.append(corr+EXCEPTION)
        signed.append(value+EXCEPTION+window.tau*V[-1])
    residual = []
    for i,p in enumerate(free):
        # If the input bin indices are a,b then floor(v/step)=a+b or a+b+1.
        worst = max(bridge[a]*signed[b]+correction[a]*V[b]
                    for a in range(i+1) for b in (i-a-1,i-a) if b>=0)
        residual.append(upper(p+worst))
    return residual


def return_inversion(n, cutoff, residual, window=FINE):
    errors = [Q(0)]*3
    for i in range(int(cutoff/STEP)):
        lo,hi = i*STEP,(i+1)*STEP
        _,first,second,corr = airy((1-window.final_relative)*lo,(1+window.final_relative)*hi)
        averaging = hi/n*(first/2+(1+Q(1,n))*hi*second/2+corr)+Q(1,n*n)
        # Short first returns retain at least .95 of the scaled time.
        early = max(residual[(Q('.95')*i).__floor__():i+1])
        inverse = 2*sqrt_hi(n)*(residual[i]+early)
        if i:
            # Each later return is individually rare. Sum in bins of v,
            # the time remaining after the return, in frequency units.
            for b in range((Q('.95')*(i+1)).__floor__()+1):
                frac = max(Q('.05'),1-(b+1)*STEP/lo)
                elapsed = max(Q('.05')*lo,lo-(b+1)*STEP)
                point = Q('1.01')/(frac*sqrt_lo(frac))
                osc = min(1,240*exp_neg(Q('.13')*elapsed))
                inverse += upper((STEP/lo+Q(1,n))*point*osc*residual[b])
        # At i=0 the early bound covers the full inverse.
        for order in range(3):
            errors[order] += (Q(3,2)*STEP*sqrt_hi(hi)*(hi*sqrt_hi(hi))**order
                              *(averaging+inverse*(hi/n)**2))
    return [2*v/PI_LO for v in errors]


def check_fourier_envelopes(n, cutoff, density_only=False):
    from verify_folded_saddle import upper_exp
    # The fair block has L=ceil(9 |theta|^(-2/3)), L>=900.
    assert (1-Q('.451')**2/6)**2 > Q('.93')
    assert 2*Q(91,89)*upper_exp(Q(1,91))/(PI_LO*Q('2.71')) < Q('.5')**2
    c = Q('.93')*9**3/96
    hit = exp_neg(c*Q('.9')**3)
    for i in range(10,100):
        a,b = Q(i,100),Q(i+1,100)
        hit += Q('.5')*(Q('.005')+Q(1,900))/a*exp_neg(c*(1-b)**3)
    # Linear term in the sum of squares contributes at most L theta^2/96.
    block = (hit+exp_neg(c))*upper_exp(Q('.00001'))
    assert block*upper_exp(Q('.166')*Q('9.01')) < 1
    assert 16*upper_exp(Q('.166')*Q('9.01')) < 100
    assert Q('.166')*Q(63,64)*(1-Q(1,2*n)) > Q('.162')
    # Excursion of length 2j after deleting the two exterior steps.
    j = n//20
    assert (2*j-2)/Q(16)-1 > Q('.124')*j
    assert 2/Q('.124')/sqrt_lo(Q('.124'))*upper_exp(Q('.166')*Q('9.01')) < 240
    assert Q('.166')*Q(13,16)*(1-Q(1,j)) > Q('.13')
    assert 2/(2-Q(1,j)) < Q('1.01')
    # The old full-period bound contributes only beyond theta=.001.
    assert Q(1,100)*(1-Q(1,2*n)) > Q(1,101)
    if density_only:
        # Integrate the order-zero tail from its actual lower endpoint.
        start = Q(2*n,100)
        far = 12*sqrt_hi(start)*exp_neg(start/101)/(Q(1,101)-1/(2*start))
        near = 300*sqrt_hi(cutoff)*exp_neg(Q('.162')*cutoff)/(Q('.162')-Q(1,2*cutoff))
        return [2*(far+near)/PI_LO]
    def moment(i,rate):
        p = 3*(i+1)
        return Q(3,2)*sqrt_hi((1/rate)**p)*gamma_half(p)
    far = 16*exp_neg(Q(2*n,20200))*(moment(0,Q(1,202))+moment(2,Q(1,202)))
    # Sharpen the continuum multiplier moments using the Airy sum, including
    # the entire tail u>=40, where value <= 10 sqrt(u) exp(-.58u).
    mult = []
    for order in [2,4]:
        total = 0
        for j in range(80):
            a,b = j*STEP,(j+1)*STEP
            total += Q(3,2)*STEP*sqrt_hi(b)*(b*sqrt_hi(b))**order*airy(a,b)[0]
        power = Q(3*order,2)+1
        total += 15*40**power*exp_neg(Q('.58')*40)/(Q('.58')-power/40)
        mult.append(total)
    assert (1+Q('2.339'))+EXCITED[0]*exp_neg((Q('3.837')-Q('2.337'))*10) < 7
    s = 2*n*sqrt_lo(2*n)
    reserve = [far,far+mult[0]/(2*s),far+mult[1]/(12*s*s)]
    for j in range(3):
        power = Q(3*(j+1),2)-1
        reserve[j] += (300*sqrt_hi(cutoff)**(3*(j+1)-2)*exp_neg(Q('.162')*cutoff)
                       /(Q('.162')-power/cutoff))
    return [2*v/PI_LO for v in reserve]


def check_gamma(n, cutoff, window=FINE):
    lam = window.tilt
    assert lam*window.relative-lam*lam/(2*(1-lam)) > Q('.004')
    # Cauchy--Schwarz with E|T-j|^8 <= 2^8 (j+8)^8.
    # The polynomial factor is maximized at j+8 <= 4/.002.
    assert (10**4*window.tau*(8+Q(4)/Q('.002'))**4
            * exp_neg(lam*window.additive/(2*window.tau)) < EXCEPTION)
    assert Q(cutoff,n) <= window.tau
    assert (2+Q(1,n))*cutoff*sqrt_hi(cutoff)/sqrt_lo(32*n) < Q('.8')
    assert Q(2,3)*Q(1,12)/(PI_LO/2)**2/(1-(Q('.8')/(PI_LO/2))**2) < Q('.05')
    assert Q(2,3)*Q(1,180)/PI_LO**2/(1-(Q('.8')/PI_LO)**2) < Q('.001')
    lam = window.final_tilt
    assert window.final_relative*lam-lam*lam/(2*(1-lam)) > window.final_rate
    assert window.final_rate*n/2 > 2
    assert 2*10**6*n*n*exp_neg(n*window.final_rate/2) < 1


if __name__ == '__main__':
    table = residual_grid(180)
    for n,cutoff,limits in [(750000,150,['.0045','.147','10.3']),
                             (10**6,160,['.0033','.101','6.1']),
                             (10**10,180,['.000001','.00002','.04'])]:
        check_gamma(n,cutoff)
        extra = check_fourier_envelopes(n,cutoff)
        main = return_inversion(n,cutoff,table)
        values = [v+w for v,w in zip(main,extra)]
        assert all(v < Q(bound) for v,bound in zip(values,limits)), list(map(float,values))
        print(f'N >= {n}: density and difference errors below', ', '.join(limits))
    n,cutoff = 125000,85
    check_gamma(n,cutoff,COARSE)
    main = return_inversion(n,cutoff,residual_grid(cutoff,COARSE),COARSE)[0]
    extra = check_fourier_envelopes(n,cutoff,density_only=True)[0]
    assert main+extra < Q('.069'), float(main+extra)
    print('N >= 125000: density error below .069')
