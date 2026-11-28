"""Certify the peak signs for both parities at every half-length N >= 150000.

Use the direct corrected binomial split, local derivative bounds for the
polynomial trial, and the Fourier decay of pinned first returns. No tables other
than the Lean Chebyshev coefficient rows are needed.
"""

from fractions import Fraction as Q
from math import comb, factorial, floor

from verify_gamma_polynomials import monomial_coefficients, read_rows
from verify_local_returns import exp_neg, gauss, upper
from verify_polynomial_integral import compact_signs
from verify_return_bounds import diff, times
from verify_rising import PI_LO, sqrt_hi, sqrt_lo
from verify_split_correction import check_first_correction

MIN_SIZE = 150000
RETURN_CUTOFF = 114
MAX_STEP = Q(1, 1250)
CUTOFF = 144
STEP = Q(1, 2)
WINDOWS = ((1, 1359, 3390, 1, Q(1, 5)),
           (2, 3330, 4040, -1, Q(160)),
           (1, 3980, 6310, -1, Q(2)))


def bin_derivatives(power, index, orders):
    """Horner shift to z=(2*index+1+t)/1024, -1<=t<=1, v=256z."""
    degree = len(power)-1
    coeffs = [power[-1]]
    for j in range(degree-1, -1, -1):
        following = [(2*index+1)*a for a in coeffs]+[0]
        for k, a in enumerate(coeffs):
            following[k+1] += a
        following[0] += power[j] << (10*(degree-j))
        coeffs = following
    bounds = []
    for r in range(orders):
        bounds.append(upper(Q(4**r*sum(map(abs, coeffs)), 2**(10*degree+120))))
        coeffs = [k*a for k, a in enumerate(coeffs) if k]
    return bounds


def trial_bounds():
    rows = read_rows()
    bins = range(2*CUTOFF)
    def jets(name, orders):
        poly = [int(c) for c in monomial_coefficients(rows[name], 1)]
        return [bin_derivatives(poly, i, orders) for i in bins]

    trial = jets("trial", 5)
    even = jets("evenCorrection", 3)
    odd = jets("oddCorrection", 3)
    # G=M+(F'+vF'')/2, so G^(r) contains (r+1)F^(r+1)/2.
    signed = [[max(even[i][r], odd[i][r]) + (r+1)*trial[i][r+1]/2
               + ((i+1)*STEP)*trial[i][r+2]/2 for r in range(3)] for i in bins]
    return trial, signed


def input_bounds(tau):
    angle = (2+Q(1, MIN_SIZE))*RETURN_CUTOFF*sqrt_hi(RETURN_CUTOFF)/sqrt_lo(32*MIN_SIZE)
    assert angle <= Q(9, 8)
    assert Q(RETURN_CUTOFF, MIN_SIZE) <= tau
    # Euler-product majorants for all terms past the quartic in both logs.
    assert Q(2, 3*12)/((PI_LO/2)**2-angle**2) < Q(".05")
    assert Q(2, 3*180)/(PI_LO**2-angle**2) < Q(".001")
    bridge_log = [0, 0, Q(1,192), 0, 0, Q(1,30720)]
    free_log = [0, 0, Q(3,32), 0, 0, Q(1,1920)]
    def derivatives(poly, count):
        result = [poly]
        for _ in range(count-1):
            result.append(diff(result[-1], 96))
        return result

    rho, rho1 = derivatives([Q(1)], 5), derivatives(bridge_log, 3)
    bridge, first, free_noise, bridge_noise = [], [], [], []
    for i in range(2*RETURN_CUTOFF):
        lo, hi = i*STEP, (i+1)*STEP
        bridge.append([gauss(p, 96, lo, hi) for p in rho])
        first.append([gauss(p, 96, lo, hi) for p in rho1])
        rb = (7*hi**4+2*tau*hi**3)/(180*32**2)+Q(".001")*(hi+tau)**7/1792
        rp = 13*hi/192+tau/64+(hi+tau)**4/384+Q(".05")*(hi+tau)**7/1792
        bridge_noise.append(upper(rb*exp_neg(lo**3/96)+gauss(times(bridge_log, bridge_log), 96, lo, hi)/2))
        free_noise.append(upper(rp*exp_neg(lo**3/24)+gauss(times(free_log, free_log), 24, lo, hi)/2))
    return bridge, first, free_noise, bridge_noise


def split_costs(tau, trial, signed):
    bridge, first, free_noise, bridge_noise = input_bounds(tau)

    def product_jet(left, right, r):
        return sum(comb(r, t)*left[t]*right[r-t] for t in range(r+1))

    costs = []
    for i in range(2*RETURN_CUTOFF):
        v = (i+1)*STEP
        maxima = [Q(0)]*4
        for a in range(i+1):
            for b in (i-a, i-a-1):
                if b < 0:
                    continue
                # Taylor remainders may reach their suprema at distinct splits.
                lattice = bridge_noise[a]*(trial[b][0]+tau*signed[b][0])+first[a][0]*signed[b][0]
                mixed = v*(product_jet(first[a], trial[b], 2)+product_jet(bridge[a], signed[b], 2))/8
                third = v*product_jet(bridge[a], trial[b], 3)/24
                fourth = v*v*product_jet(bridge[a], trial[b], 4)/128
                maxima = list(map(max, maxima, (lattice, mixed, third, fourth)))
        costs.append(upper(free_noise[i]+sum(maxima)))
    return costs


def frequency_costs(correction):
    n = MIN_SIZE
    trial, signed = trial_bounds()
    costs = split_costs(MAX_STEP, trial, signed)
    assert CUTOFF*sqrt_hi(CUTOFF) <= Q('.001')*2*n*sqrt_lo(2*n)
    total = [Q(0)]*3
    for i in range(2*CUTOFF):
        lo, hi = i*STEP, (i+1)*STEP
        if lo >= RETURN_CUTOFF:
            # The conditioned meander bound applies to the true signed amplitude.
            # The independent polynomial enclosure supplies the trial term.
            error = 100*exp_neg(Q(".186")*lo) + trial[i][0]
        else:
            early = max(costs[floor(Q(".95")*i):i+1])
            inverse = 2*sqrt_hi(n)*(costs[i]+early)
            if i:
                for k in range(floor(Q(".95")*(i+1))+1):
                    p = max(Q(".05"), 1-Q(k+1, i))
                    # sqrt(j)*r_j increases, and r_j/((2j-1) r_N)
                    # is the normalized first-return mass. Each bin contains
                    # at most N*STEP/lo+1 possible return times.
                    # The elapsed rescaled time is at least (i-k-1)/2.
                    # Every ten full bin widths contribute a factor exp(-.75) < 1/2.
                    blocks = max(0, i-k-1)//10
                    discount = min(Q(1), Q(125, 2**blocks))
                    inverse += upper((STEP/lo+Q(1,n))*Q(".501")/(p*sqrt_lo(p))*costs[k]*discount)
            smooth = (1+hi*sqrt_hi(hi)/2)*Q(15,10**16)+hi*Q(36,10**14)
            error = (smooth+4*sqrt_hi(n)*hi/n*correction
                     +(hi/n)**2*inverse+hi/n*signed[i][0])
        for r in (1, 2):
            total[r] += Q(3,2)*STEP*sqrt_hi(hi)*(hi*sqrt_hi(hi))**r*error
    return total


def lattice_tail(r):
    n, u = MIN_SIZE, Q(CUTOFF)
    # The outer arc starts after the retained interval and contributes at
    # most 144*(16*N^2)^3 / exp(N/200), decreasing by the 22nd power bound.
    assert u*sqrt_hi(u) <= Q(".008")*2*n*sqrt_lo(2*n)
    assert 144*16**3*n**6*factorial(22)*Q(200,n)**22 <= Q(1,1000)
    # Differentiate -1200*t^(3r+1)*exp(-.157*t^2) for t=xi^(1/3)>=12.
    assert 300 <= 1200*(Q(".314")-Q(3*r+1, 144))
    return 1200*12**(3*r+1)*exp_neg(Q(".157")*u) + Q(1,1000)


def main():
    assert MIN_SIZE//20 >= 501
    correction = check_first_correction(CUTOFF)
    total = frequency_costs(correction)
    for r, lo, hi, margin, trial_error in compact_signs(WINDOWS, 12**3):
        remaining = margin-total[r]-lattice_tail(r)-trial_error
        if remaining <= 0:
            raise ArithmeticError(f"sign not certified at {lo}..{hi}")
        lower = floor(10**6*remaining)/10**6
        print(f"order {r}, {lo}/10000..{hi}/10000: retained error bound {float(total[r]):.8g}, "
              f"full-period margin > {lower:.6f}", flush=True)


if __name__ == "__main__":
    main()
