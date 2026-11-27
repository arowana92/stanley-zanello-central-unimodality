"""Rational error bounds for periodized sampled Fourier inversion of ballot areas."""

from fractions import Fraction as Q
from math import comb, factorial, isqrt

from verify_folded_saddle import upper_exp
from verify_local_returns import exp_neg
from verify_rising import PI_HI, PI_LO, sqrt_hi
from verify_size_descent import check_block, tail_integral

N_MIN = 2049
N_MAX = 300000


def all_frequency_block(theta, length):
    """Uniform killed row norm at frequencies theta through pi."""
    rho = []
    for d in range(length+1):
        l = d//2
        if not l:
            rho.append(Q(1))
            continue
        angle = min(theta, Q(3, 2*l))
        squared = Q(0)
        for j in range(l):
            v = (2*j+1)*angle/2
            squared += (v*(1-v*v/6))**2
        rho.append(exp_neg(min(Q(l, 4), squared)/4))
    norm = rho[length]
    for a in range(1, length+1):
        hit = Q(0)
        lost = Q(0)
        for j in range(a, length+1, 2):
            prob = Q(a*comb(j, (j-a)//2), j*2**j)
            hit += prob
            lost += prob*rho[length-j]
        norm = max(norm, min(1-hit, rho[length]+lost))
    return norm


def check_grid_tails():
    check_block(Q('.001'), 900, Q('9.01'), Q('.93'), Q('.5'), Q('.1895'))
    check_block(Q('.008'), 225, Q('9.04'), Q('.74'), Q('.53'), Q('.16'))
    assert Q('.16')*Q(63, 64)*(1-Q(1, 2*N_MIN)) > Q('.157')
    s = 2*N_MIN*sqrt_hi(2*N_MIN)
    step = 2*PI_HI/5
    # xi >= 2048 implies xi^(2/3) > 161.
    assert 2048**2 > 161**3
    bounds = [tail_integral(Q(161), Q('.157'), Q(3*(j+1), 2)-1, 150) for j in (1, 2)]
    for lo, hi, length, rate in [
        (Q('.008'), Q('.032'), 216, Q('.0078')),
        (Q('.032'), PI_HI, 112, Q('.0155')),
    ]:
        norm = all_frequency_block(lo, length)
        assert norm*upper_exp(rate*length) < 1, float(norm)
        # At most one endpoint spacing beyond the arc length.
        for j in (1, 2):
            assert rate*Q(63, 64)*2*N_MIN > Q(3*(j+1), 2)
            bounds[j-1] += (16*upper_exp(rate*length)
                            * exp_neg(rate*Q(63, 64)*(2*N_MIN-1))
                            * ((hi-lo)*s+step)*(hi*s)**j)
    assert all(2*b/PI_LO < limit for b, limit in zip(bounds, (Q('.00025'), Q('.949'))))
    print('Fourier tails below .00025 and .949 in the two difference orders.')
    # Aliases near the central window require K/s >= 4.3.
    shift = Q(3*N_MIN+1, 4*N_MIN*isqrt(2*N_MIN))
    assert shift < Q('.012') and 5-Q('.63')-shift-Q(1, isqrt((2*N_MIN)**3)) > Q('4.3')
    assert 6/((1+Q(1, 2*N_MIN-1))*(1+Q(1, 2*(2*N_MIN-1)))) > Q('5.99')
    large_s = 2*N_MAX*sqrt_hi(2*N_MAX)
    alias = 16*sqrt_hi(2*N_MAX+1)*large_s**3 * exp_neg(Q('5.99')*Q('4.3')**2)
    assert alias < Q('1e-12')


def check_rounding():
    # Machin's identity and the alternating arctangent series.
    def arctan_bounds(denom):
        partial = sum(Q((-1)**j, (2*j+1)*denom**(2*j+1)) for j in range(24))
        return partial, partial+Q(1, 49*denom**49)
    a, b = arctan_bounds(5)
    c, d = arctan_bounds(239)
    fixed = 0x3243F6A8885A308D313198A2E
    assert fixed < (16*a-4*d)*2**96 < (16*b-4*c)*2**96 < fixed+1
    eps = Q(1, 2**96)
    assert Q('.8')**30/factorial(30) < eps
    # Horner error with |angle/2| <= .8, then the double-angle formulas.
    assert 6/(1-Q('.64'))**2 + 3/(1-Q('.64')) + 1 < 64
    assert 4*64*(1+64*eps)+3 < 512
    assert (Q(1, 2**81)+eps+2*512*eps)/Q('.62') < Q(1, 2**79)
    last = N_MAX
    kernel = (last+1)*Q(1, 2**77)
    unit = Q(1, 2**53)
    assert (kernel*(1+Q('2.022')*sqrt_hi(last+1)) + 5*unit < Q(1, 2**47))
    # One butterfly stage, including a rounded twiddle; twenty stages at most.
    assert (1+12*unit)**20 < 1+13*20*unit
    for stages in range(1, 21):
        error = 13*stages*unit
        assert (1+error)**3*(1+4*unit)-1 < 59*stages*unit
    first_scale = isqrt((2*N_MIN)**3)
    ratio = Q('1.01')*sqrt_hi(Q('1.01'))*(1+Q(1, first_scale))
    assert ratio < Q('1.016')
    assert Q('.1366')*(1-Q(1, 2*N_MIN))**2-1/Q(first_scale) > Q('.1364')
    assert ratio*(Q('.6')+Q('.012'))+1/Q(first_scale) < Q('.623')
    print('Fixed-point constants, residual allowances and spatial endpoints verified.')


if __name__ == '__main__':
    check_grid_tails()
    check_rounding()
