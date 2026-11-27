"""Rational bounds for descent to an odd-part row below 300000."""

from fractions import Fraction as Q
from functools import lru_cache
from math import comb

from verify import ballot_ranks, direct_ranks
from verify_cubic_tilt import A_HI, A_LO, gaussian_even, gaussian_factor
from verify_folded_saddle import upper_exp
from verify_local_returns import (
    GammaWindow, airy, check_fourier_envelopes, check_gamma, continuum_multiplier_costs,
    excited_power, exp_neg, residual_grid, return_inversion,
)
from verify_rising import PI_LO, sqrt_hi, sqrt_lo
from verify_type_b_transfer import ground_integral_bounds


def split_bound(i, step, tau, bridge, signed, correction, vnorm):
    """Sum over the smaller split time using its beta-binomial point masses."""
    if i == 0:
        return bridge[0]*signed[0] + correction[0]*vnorm[0]
    total = 0
    for a in range((i+1)//2+1):
        late = max(Q(i,2), i-a-1)*step
        if a:
            mass = (step+tau)/(PI_LO*sqrt_lo(a*step*late))
        else:
            mass = 2*sqrt_hi(step+2*tau)/(PI_LO*sqrt_lo(late))
        possibilities = []
        for b in (i-a-1, i-a):
            if b >= 0:
                possibilities.append(bridge[a]*signed[b] + correction[a]*vnorm[b]
                                     + bridge[b]*signed[a] + correction[b]*vnorm[a])
        total += min(1,mass)*max(possibilities)
    return total


@lru_cache(None)
def derivative_bounds(lo, hi):
    """Suprema for f', f'', f''', Q_0, Q_0' on the given time interval."""
    _, first, second, _ = airy(lo,hi)
    quot = min(Q('.5'), hi**2/8, 1/lo if lo else 1)
    third = Q(30,32) + Q(27,8)*hi*sqrt_hi(hi)
    quot_prime = hi/4
    if lo >= 4:
        root = sqrt_hi(hi)
        inv_root = 1/sqrt_lo(lo)
        sums = [(1+A_HI)*A_HI**j*exp_neg(A_LO*lo/4)
                + excited_power(j)*exp_neg(Q('3.837')*lo/4) for j in range(4)]
        third = min(third, Q('1.26')*(
            Q(3,8)*inv_root**5*sums[0] + Q(3,8)*inv_root**3*sums[1]
            + Q(3,8)*inv_root*sums[2] + root*sums[3]/8))
        quot = min(quot, Q('.63')*(inv_root+root)*sums[0])
        excursion_first = Q('1.26')*(Q(3,2)*root*sums[0] + hi*root*sums[1]/2)/(1+A_LO)
        quot_prime = min(quot_prime, (excursion_first+first)/(2*lo) + quot/lo)
    return first, second, third, quot, quot_prime


def corrected_removal(n, lo, hi, window):
    first, second, _, quot, _ = derivative_bounds(lo, hi)
    wide = (1+window.final_relative)*hi
    _, wide_second, third, _, quot_prime = derivative_bounds((1-window.final_relative)*lo, wide)
    lead = Q(7,12)*first + hi*second/30 + Q('.35')*quot
    vprime = Q(8,15)*(wide*third+Q(3,2)*wide_second) + Q('.35')*(wide_second+quot_prime)
    tau = hi/n
    return (tau*lead + Q(3,8)*tau**2*second + hi**3*third/(3*n*sqrt_lo(n))
            + tau*Q('1.001')*hi*vprime/sqrt_lo(n) + Q(1,n*n))


def check_block(theta, min_length, length_scale, sin_factor, point, rate):
    """Cover the first-hit times on their single parity by disjoint cells."""
    min_hit = min_length//10
    assert 2*Q(min_hit+1,min_hit-1)*upper_exp(Q(1,min_hit+1))/(PI_LO*Q('2.71')) < point**2
    max_root = Q('.1') if theta == Q('.001') else Q('.2')
    assert max_root**3 == theta and Q(9)/max_root**2 == min_length
    assert length_scale >= 9+max_root**2
    assert (1-(length_scale*max_root/2)**2/6)**2 > sin_factor
    c = sin_factor*9**3/96
    start = Q('.1')-Q(2,min_length)
    width = (1-start)/400
    bound = exp_neg(c) + exp_neg(c*Q('.9')**3)
    for j in range(400):
        lo = start+j*width
        rem = max(0,1-lo-width-Q(2,min_length))
        bound += point*width/(2*lo)*exp_neg(c*rem**3)
    assert bound*upper_exp(length_scale*max_root**4/96 + rate*length_scale) < 1
    assert 16*upper_exp(rate*length_scale) < 100


def tail_integral(start, rate, power, constant):
    return (constant*sqrt_hi(start)**int(2*power)*exp_neg(rate*start)
            /(rate-power/start))


def check_lattice_bounds():
    check_block(Q('.001'), 900, Q('9.01'), Q('.93'), Q('.5'), Q('.1895'))
    check_block(Q('.008'), 225, Q('9.04'), Q('.74'), Q('.53'), Q('.16'))
    min_n = 32000
    assert Q('.1895')*Q(63,64)*(1-Q(1,2*min_n)) > Q('.186')
    assert Q('.16')*Q(63,64)*(1-Q(1,2*min_n)) > Q('.157')
    # The gamma moment bounds used in removing the last average.
    assert (1+Q(1,min_n))*(3+Q(26,min_n)+Q(24,min_n**2)) < 4
    assert 1+Q(1,min_n) < Q('1.001')**2
    from verify_return_expansion import continuum_coefficients
    meander, excursion = continuum_coefficients(2)
    for moments in (meander,excursion):
        assert -2*moments[1] < Q(1,4) and 24*moments[2] < 1
    # Inputs keep the arguments below the first cosine zero.
    profiles = [
        (32000, 62, ('.002','.20','2.2','.19','.1','.09','.004'), ['.38']),
        (47500, 69, ('.0015','.16','1.75','.15','.08','.07','.0025'), ['.12']),
        (300000, 124, ('.00042','.11','.86','.074','.035','.028','.0005'),
         ['.003','.121','13.6']),
    ]
    step = Q(1,4)
    for n, cutoff, parameters, limits in profiles:
        window = GammaWindow(*map(Q,parameters))
        check_gamma(n,cutoff,window,max_argument=Q(1))
        check_fourier_envelopes(n,cutoff,density_only=True)  # late return bound
        assert cutoff < Q(2*n,100)
        grid = residual_grid(cutoff,window,step,split_bound)
        main = return_inversion(n,cutoff,grid,window,step,corrected_removal)
        costs = continuum_multiplier_costs(n)
        for order, limit in enumerate(limits):
            power = Q(3*(order+1),2)-1
            tail = (tail_integral(cutoff,Q('.186'),power,300)
                    + tail_integral(Q(2*n,100),Q('.157'),power,150)
                    + tail_integral(Q(2*n,25),Q(1,101),power,12))
            value = main[order]+2*(tail+costs[order])/PI_LO
            assert value < Q(limit), (n,order,float(value))
        print(f'N >= {n}: certified errors below {", ".join(limits)}.', flush=True)


def check_cubic_tail():
    b, xmax = Q('3.837'), Q('.29')
    variance_scale = A_LO**3/(18*xmax**2)
    gaussian = sum(comb(3,i)*gaussian_even(2*i)/variance_scale**i for i in range(4))
    assert PI_LO**2 > b+1
    assert b*b/(18*xmax**2)-1/(1+b)-6/b > 7
    assert 1+(b+1)**2/3 < 10
    ratio = 4*exp_neg(Q(7))
    tail = (gaussian*(1+b)/Q('1.57')*(b/A_LO)**6
            *exp_neg((b**3-A_HI**3)/(54*xmax**2))*(1+10*ratio/(1-ratio)))
    assert tail < Q('.01')


def slope_bound(lo, hi):
    factor = gaussian_factor(6,A_LO**3/(18*hi*hi))-Q('.01')
    radial = min((A_LO/(3*x))**6/upper_exp(A_HI*(A_HI/(3*x))**2/6) for x in (lo,hi))
    return 3*Q('1.57')*factor*radial/(2*sqrt_hi(A_HI))


def small_density(x):
    amin = A_LO**3/(18*x*x)
    gaussian = sum(comb(3,i)*gaussian_even(2*i)/amin**i for i in range(4))
    return (3*Q('2.04')*(gaussian+Q('.01'))/(2*sqrt_lo(A_LO))
            *(A_HI/(3*x))**3*exp_neg(A_LO*(A_LO/(3*x))**2/6))


def check_reflection_and_peak():
    ground_integral_bounds()
    check_cubic_tail()
    points = list(map(Q,('.253','.26','.27','.28','.285','.29')))
    gain = sum((b-a)*slope_bound(a,b) for a,b in zip(points,points[1:]))
    assert gain > Q('.26')
    assert slope_bound(Q('.25'),Q('.253')) > 0
    assert slope_bound(Q('.1375'),Q('.145')) > Q('.121')
    assert slope_bound(Q('.145'),Q('.25')) > Q('.121')
    n = 300000
    m = 2*n
    assert Q('.6')+(1+Q(1,m))/sqrt_lo(m) < Q('.602')
    assert Q('1.78')/upper_exp(6*Q('.602')**2) > Q('.121')
    assert Q('.145')+(1+Q(1,m))/sqrt_lo(m) < Q('.147')
    assert Q('1.78')*(1-exp_neg(6*(Q('.25')-Q('.147'))**2)) > Q('.10')
    for h, total, end in [(32000,Q('.32'),Q('.326')),(47500,Q('.5'),Q('.505'))]:
        s = 2*h*sqrt_lo(2*h)
        assert total+(3*h+1)/s < end
        assert Q('1.31')/s < Q('.0001') and 300/(PI_LO*Q('.19')**3*s) < Q('.001')
    for left, right, error in [('.163','.326','.38'),('.215','.35','.12'),('.155','.505','.12')]:
        lost = 6*(Q(right)**2-Q('.29')**2+Q('.0001'))
        assert Q('1.78')/upper_exp(lost) > small_density(Q(left))+2*Q(error)
    needed = 2*Q('.1375')*(2+Q(1,n))*sqrt_hi(2+Q(1,n)) + Q(1,n)/sqrt_lo(n)
    cost = 2*sqrt_lo(2)/3
    assert cost*Q('.89')*sqrt_lo(Q('.89')) - 2/sqrt_lo(n) > needed
    y = Q('.16')
    assert (cost*(1-y)*sqrt_lo(1-y) + Q('.32')*(2*y)*sqrt_lo(2*y)
            - 2/sqrt_lo(n) > needed)
    assert sqrt_lo(Q(8,13))-2/sqrt_lo(n) > needed
    print('Peak, reflected-comparison margins and the three size splits verified.')


def check_small_recurrences():
    # Only use the two published path recurrences on the comparison side.
    # A radix larger than the total walk count makes equality digitwise.
    base = 1 << 32
    dyck, odd = [1], [1]
    for m, ranks in ballot_ranks(12):
        n, parity = divmod(m,2)
        counts = direct_ranks(range(m-1,0,-2))[::-1]
        assert counts == ranks[::-1]
        if parity:
            row = sum(base**h*odd[h]*dyck[n-h] for h in range(n+1))
        else:
            dyck.append(sum(base**h*dyck[h]*dyck[n-h-1] for h in range(n)))
            row = dyck[n] + sum(base**(2*h+1)*odd[h]*dyck[n-h] for h in range(n))
            odd.append(row)
        for count in counts:
            row, digit = divmod(row,base)
            assert digit == count
        assert row == 0
    print('Both descent recurrences match direct strict partitions in all 24 small rows.')


if __name__ == '__main__':
    check_small_recurrences()
    check_reflection_and_peak()
    check_lattice_bounds()
