"""Quantitative inversion of the signed last-return identity for both parities."""

from fractions import Fraction as Q
from math import comb, factorial

from verify_airy_grid import add, derivative
from verify_folded_saddle import upper_exp
from verify_hit_tilts import exp_bound
from verify_rising import PI_HI, PI_LO, decay, gamma_half, sqrt_hi, sqrt_lo


def times(p, q):
    result = [Q(0)] * (len(p)+len(q)-1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i+j] += a*b
    return result


def scale(p, c):
    return [v*c for v in p]


def weight(power):
    return [Q(comb(power, j)) for j in range(power+1)]


def cube_hi(x):
    """Upper endpoint of a rational bracket for a nonnegative cube root."""
    lo, hi = Q(0), max(Q(1), Q(x))
    for _ in range(60):
        mid = (lo+hi)/2
        if mid**3 < x:
            lo = mid
        else:
            hi = mid
    return hi


def gaussian_norm(poly, b):
    # Maximize each monomial times exp(-v^3/b) on the positive real line.
    return sum(abs(c)*(cube_hi(Q(j*b,3)/Q('2.71'))**j if j else 1)
               for j,c in enumerate(poly) if c)


def diff(poly, b):
    return add(derivative(poly), [0,0]+scale(poly,-Q(3,b)))


def input_error(b, c, quadratic, quintic):
    """Bound in tau^2 for the free or bridge symbol vs its corrected gamma average."""
    ell = [0,0,quadratic,0,0,quintic]
    # Lattice log error for the first three even powers, in units tau^2.
    remainder = add(weight(1), add(scale(weight(4),Q(1,384)),scale(weight(7),Q(1,256))))
    lattice = gaussian_norm(add(remainder,scale(times(ell,ell),Q(1,2))),b)

    g = [[Q(1)]]
    for _ in range(4):
        g.append(diff(g[-1],b))
    correction = add(scale(ell,-1),add(scale(g[1],-c),[0]+scale(g[2],-Q(1,2))))
    # Gamma shapes j+c, center v=j*tau. On T >= j/2 use weighted
    # derivative norms. The exceptional lower tail costs < .001 tau^2.
    gamma = (gaussian_norm(g[2],b) + gaussian_norm(times(weight(1),g[3]),b)
             + gaussian_norm(times(weight(2),g[4]),b))
    corr1 = diff(correction,b)
    corr2 = diff(corr1,b)
    gamma += gaussian_norm(corr1,b) + 2*gaussian_norm(times(weight(1),corr2),b)
    tau = Q(1, 10**6)
    exceptional = (tau**2*(4/(Q('.19')*Q('2.71')))**4*gaussian_norm(g[4],b)/24
                   + tau*(2/(Q('.19')*Q('2.71')))**2*gaussian_norm(corr2,b)/2)
    assert exceptional < Q('.001')
    return lattice+gamma+exceptional, gaussian_norm(correction,b)


def airy_bounds(lo, hi):
    """Bounds on |f'|, |f''|, and |V_delta| for lo <= v <= hi."""
    first = Q(3,4)*sqrt_hi(hi)
    second = Q(3,4)*hi
    quotient = min(Q(1,2),hi*hi/8, 1/lo if lo else Q(1,2))
    if lo >= 8:
        # Sum (1+a)^3 exp(-a v/4) at the Dirichlet Airy energies.
        envelope = 3600*exp_bound(-Q('.58')*lo)
        v = sqrt_hi(hi)
        first = min(first, Q('1.26')*(Q(1,2)+v/2)*envelope)
        second = min(second,Q('1.26')*(Q(3,4)+v/4)*envelope)
        quotient = min(quotient,Q('.63')*v*(1+1/lo)*envelope)
    corr = Q(8,15)*(hi*second+first/2) + Q('.35')*(first+quotient)
    return first,second,corr


def check_return_constants():
    # All estimates use tau <= 10^-6 and each cosine/sinc argument has modulus <= .01.
    tau = Q(1,10**6)
    assert 1+2*tau < 2
    assert ((3+26*tau+24*tau*tau)*4/24 < Q('.51')
            and (5+6*tau)/6 < 1)
    # Taylor remainders on the exceptional gamma event T<j/2.
    assert upper_exp(Q('.69')) < 2
    assert sum(comb(5,j)*factorial(j) for j in range(6)) < 327
    assert 327*upper_exp(Q('2.337')) < 3600  # evaluate at the lower energy bound
    assert Q('1.26')**2 > PI_HI/2
    assert Q('2.337')/4 > Q('.58')
    # Split v at 22. For larger v, v^(3/2) exp(-.58 v) decreases.
    assert airy_bounds(Q(0),Q(22))[2] < 205
    assert 5*3600*22*sqrt_hi(22)*exp_bound(-Q('.58')*22) < 6
    input_limits = []
    for b,c,p,q in [(24,Q(1),Q(3,32),Q(1,1920)),(24,Q(1),Q(1,32),Q(1,1920)),
                     (96,Q(1,2),Q(1,192),Q(1,30720))]:
        error, norm = input_error(b,c,p,q)
        input_limits.append((error,norm))
    free = max(value[0] for value in input_limits[:2])
    bridge, correction = input_limits[-1]
    residual = free+bridge*(1+205*tau)+205*correction
    return residual


def peak_errors(n, u_max, residual):
    """Absolute errors at lattice scales s, s^2 and s^3."""
    t = u_max*sqrt_hi(u_max)
    assert Q(u_max,n) <= Q(1,10**6) and t/sqrt_lo(n) < Q('.025')
    local = [Q(0)]*3
    for j in range(u_max):
        lo,hi = Q(j),Q(j+1)
        first, second, corr = airy_bounds(Q('.99')*lo,Q('1.01')*hi)
        # Taylor about u, including the correction on the gamma-average law.
        err = hi/n*(first/2+(1+Q(1,n))*hi*second/2+corr) + Q(1,n*n)
        for order in range(3):
            local[order] += Q(3,2)*sqrt_hi(hi)*((hi*sqrt_hi(hi))**order)*err
    results = []
    for j in range(3):
        # Wallis: 1/r_n <= 2 sqrt(n). Inverse has l1 norm <= 2.
        integral = 4*residual*Q(3,3*j+7)*t**(j+1)*u_max**2/(n*sqrt_lo(n))
        # Lattice and limit tails at .189, with both signs and the factor
        # two converting the symmetric law to the positive branch.
        power = Q(3*(j+1),2)
        rate = Q('.189')
        tail = (300*sqrt_hi(u_max)**(3*(j+1)-2)*exp_bound(-rate*u_max)
                /(rate-(power-1)/u_max))
        results.append(2*(local[j]+integral+tail)/PI_LO+Q(1,10**7))
    return results


def check_inversion():
    n, cutoff = 2 * 10**10, 120
    s = 2*n*sqrt_lo(2*n)
    assert (2+Q(1,n))*Q('.025')/sqrt_lo(32) < Q('.01')
    # The centered gamma Chernoff exponent at lambda = +/- .005.
    lam = Q('.005')
    assert lam/Q(100)-lam**2/(2*(1-lam)) > Q(1,40000)
    assert 2*10**6 * n**2 * factorial(10) < Q(n,80000)**10
    # The full-period far tail starts at u=(2N)*10^-6.
    assert Q('.19')*(1-Q(1,2*n)) > Q('.189')
    assert Q(1,100)*(1-Q(1,2*n)) > Q(1,101)
    def tail_moment(order, rate):
        b = 3*(order+1)
        return Q(3,2)*sqrt_hi((1/rate)**b)*gamma_half(b)
    far = 16*decay(Q(2*n,202*10**6))*(tail_moment(0,Q(1,202))+tail_moment(2,Q(1,202)))
    mult1 = 100*tail_moment(2,Q('.19'))/(2*s)
    mult2 = 100*tail_moment(4,Q('.19'))/(12*s*s)
    assert 2*(far+max(mult1,mult2))/PI_LO < Q(1,10**7)
    residual = check_return_constants()
    assert residual < 822
    result = peak_errors(n,cutoff,residual)
    assert all(value < Q(bound) for value,bound in zip(result,['.000010','.008','9']))
    assert 100*tail_moment(2,Q('.19'))/PI_LO < 4*10**6


if __name__ == '__main__':
    check_inversion()
    print('Both parities: density error < .000010, first difference error < .008, '
          'second difference error < 9 at N >= 20000000000.')
