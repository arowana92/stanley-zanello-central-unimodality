"""Check both staircase peak comparisons for every half-length N >= 10000.

The central frequency cells retain the signed quadratic residual. All cell
arithmetic uses rational bounds or upward-rounded nonnegative integers.
"""

from argparse import ArgumentParser
from fractions import Fraction as Q
from math import ceil, comb, floor, lcm

from verify_direct_peak import CUTOFF, RETURN_CUTOFF, STEP, WINDOWS, bin_derivatives
from verify_gamma_polynomials import chebyshev_coefficients, monomial_coefficients, read_rows
from verify_local_returns import exp_neg, gauss, upper
from verify_polynomial_integral import compact_signs
from verify_return_bounds import diff, times
from verify_rising import PI_LO, sqrt_hi, sqrt_lo
from verify_second_split import (
    WIDTH, check_log_terms, check_monomials, log_terms, plus, product_jet,
    residuals, second_input_error, symbol_coefficients,
)
from verify_split_correction import check_first_correction, drift


MIN_SIZE = 10000
MAX_STEP = Q(RETURN_CUTOFF,MIN_SIZE)
GRID = 10**30
CELLS = 2*RETURN_CUTOFF


def cell_jets(poly, orders, start=0, stop=CELLS):
    denominator = lcm(*(c.denominator for c in poly))
    numerators = [int(c*denominator) for c in poly]
    # bin_derivatives interprets its integer input at the shared dyadic scale.
    return [[ceil(GRID*c*2**120/denominator) for c in bin_derivatives(numerators,i,orders)]
            for i in range(start,stop)]


def trial_cells():
    rows = read_rows()
    def poly(name):
        return monomial_coefficients(rows[name],2**120)
    trial = poly("trial")
    assert all(entry[0]*10**14 <= GRID for entry in cell_jets(trial,1,CELLS,2*CUTOFF))
    signed = [cell_jets(plus(poly(name),drift(trial,Q(1,2),WIDTH)),5)
              for name in ("evenCorrection","oddCorrection")]
    both = [[max(a,b) for a,b in zip(left,right)] for left,right in zip(*signed)]
    return cell_jets(trial,7), both


def symmetric_dyadic_row(coeffs, den):
    scale = 2**120
    result = []
    for k, c in enumerate(coeffs):
        multiplicity = 1 if k == 0 else 2
        d = multiplicity*den
        result.append(multiplicity*((2*c*scale+d)//(2*d)))
    return result


def residual_cells(gaussian_error, truncated=False):
    result = [Q(0)]*CELLS
    for poly in residuals():
        coeffs,den = chebyshev_coefficients(poly)
        scale = 2**120
        if truncated:
            row = symmetric_dyadic_row(coeffs, den)
            tail = sum(map(abs, row[256:]))
            assert len(row) <= 1031 and Q(tail,scale) < Q(2,10**9)
            omitted = Q(2*1031+1+tail,scale)
            row = row[:256]
        else:
            row = [round(Q(c*scale,den)) for c in coeffs]
            omitted = Q(len(row),2*scale)
        while row and row[-1]==0:
            row.pop()
        jets = cell_jets(monomial_coefficients(row,scale),1)
        result = [max(old,upper(Q(cell[0],GRID)+omitted+gaussian_error))
                  for old,cell in zip(result,jets)]
    return result


def scale(poly, c):
    return [c*p for p in poly]


def shifted_power(k):
    return [comb(k,j)*MAX_STEP**(k-j) for j in range(k+1)]


def monomials(terms):
    result = [Q(0)]*(max(j for j,_ in terms)+1)
    for j,c in terms:
        result[j] += c
    return result


def curve_inputs(parity):
    # C majorizes the logarithmic remainder divided by tau^3. The real
    # exponential adds A^3/6 + A*B + tau*B^2/2 for log coefficients A,B.
    first,second = log_terms(parity)
    A,B = monomials(first),monomials(second)
    if parity is None:
        divisor = 96
        C = plus(monomials(((3,Q(2,180*32**2)),)),
                 scale(shifted_power(6),Q(1,512*2835)),
                 scale(shifted_power(9),Q(1,18432*32000)))
    else:
        divisor = 24
        C = plus([Q(1,64)], scale([MAX_STEP**3,8*MAX_STEP**2,24*MAX_STEP,Q(104,3)],Q(1,12288)),
                 scale(shifted_power(6),Q(1,11520)),
                 scale(shifted_power(9),Q(1,18432*70)))
    noise = plus(C,scale(times(times(A,A),A),Q(1,6)),times(A,B),
                 scale(times(B,B),MAX_STEP/2))
    first_curve, second_curve = symbol_coefficients([Q(1)],first,second,width=1)
    def jets(poly, order):
        values = [poly]
        for _ in range(order):
            values.append(diff(values[-1],divisor))
        return [[ceil(GRID*gauss(p,divisor,i*STEP,(i+1)*STEP)) for p in values]
                for i in range(CELLS)]
    remainder = [ceil(GRID*(gauss(noise,divisor,i*STEP,(i+1)*STEP)+Q(1,10**18)))
                 for i in range(CELLS)]
    if parity is None:
        return jets([Q(1)],6),jets(first_curve,4),jets(second_curve,2),remainder
    return remainder


def check_symbol_bounds():
    # Euler-product zeros bound the positive logarithmic terms after degree six.
    assert Q(3,4*45)/((PI_LO/2)**2-Q(9,8)**2) <= Q(1,70)
    assert Q(3,4*2835)/(PI_LO**2-Q(9,8)**2) <= Q(1,32000)
    # If (2v+tau)*sqrt(tau/32)>9/8 then v>28, tau>1/2000 and N<228000.
    assert (56+MAX_STEP)**2*MAX_STEP/32 <= Q(9,8)**2
    assert (2*RETURN_CUTOFF+MAX_STEP)**2*Q(1,2000*32) <= Q(9,8)**2
    assert 2*sqrt_hi(2000*RETURN_CUTOFF) < 1000
    # At l=floor(25/tau), the prefix of 2l steps is in the first quadrant.
    assert 25-MAX_STEP >= 24 and (50+MAX_STEP)**2*MAX_STEP/32 < (PI_LO/2)**2
    assert Q(24**3,96)-25*MAX_STEP**2/384 >= 140
    A,B = (monomials(p) for p in log_terms(1))
    amplitude = plus([Q(1)],scale(A,MAX_STEP),
                     scale(plus(scale(times(A,A),Q(1,2)),B),MAX_STEP**2))
    # The slow bridge Gaussian and larger odd free-log coefficients dominate both parities.
    assert (1000*exp_neg(Q(140))+gauss(amplitude,96,Q(28),Q(RETURN_CUTOFF)))*2000**3 <= Q(1,10**18)


def cubic_costs(trial, signed):
    bridge, first, second, bridge_noise = curve_inputs(None)
    free_noise = curve_inputs(1)
    costs = []
    for i in range(CELLS):
        v = (i+1)*STEP
        maxima = [Q(0)]*5
        for a in range(i+1):
            for b in (i-a,i-a-1):
                if b<0:
                    continue
                F,G = trial[b],signed[b]
                A,B,C = bridge[a],first[a],second[a]
                terms = (bridge_noise[a]*(F[0]+MAX_STEP*G[0])+C[0]*G[0],
                         v/8*(product_jet(C,F,2)+product_jet(B,G,2)),
                         v/24*(product_jet(B,F,3)+product_jet(A,G,3)),
                         v**2/128*(product_jet(B,F,4)+product_jet(A,G,4)),
                         v/96*product_jet(A,F,4)+v**2/192*product_jet(A,F,5)
                         +v**3/1440*product_jet(A,F,6))
                maxima = list(map(max,maxima,terms))
        costs.append(upper(Q(free_noise[i],GRID)+sum(maxima)/GRID**2))
    return costs


def return_cost(i, costs):
    early = max(costs[19*i//20:i+1])
    inverse = 2*sqrt_hi(MIN_SIZE)*(costs[i]+early)
    if i:
        for k in range(19*(i+1)//20+1):
            p = max(Q(1,20),1-Q(k+1,i))
            discount = min(Q(1),Q(125,2**(max(i-k-1,0)//10)))
            inverse += upper((Q(1,i)+Q(1,MIN_SIZE))*Q(".501")/(p*sqrt_lo(p))*costs[k]*discount)
    return inverse


def retained_errors(use_lean_gaussian_bound=False, truncated=False):
    check_symbol_bounds()
    assert MAX_STEP <= Q(".02") and MIN_SIZE//20+1 >= 501
    assert CUTOFF*sqrt_hi(CUTOFF) <= Q(".001")*2*MIN_SIZE*sqrt_lo(2*MIN_SIZE)
    check_monomials()
    check_log_terms()
    first_error = check_first_correction(CUTOFF)
    replacement = second_input_error()
    assert replacement <= Q(18,10**14)
    if use_lean_gaussian_bound or truncated:
        replacement = Q(3,10**7)  # second_residual_transfer on [0,144].
    second = residual_cells(replacement, truncated)
    trial,signed = trial_cells()
    cubic = cubic_costs(trial,signed)
    total = [Q(0)]*3
    for i in range(2*CUTOFF):
        hi = (i+1)*STEP
        if i<CELLS:
            t = hi/MIN_SIZE
            smooth = (1+hi*sqrt_hi(hi)/2)*Q(15,10**16)+hi*Q(36,10**14)
            error = (smooth+4*sqrt_hi(MIN_SIZE)*t*first_error
                     +t**2*return_cost(i,second)+t**3*return_cost(i,cubic)
                     +t*Q(signed[i][0],GRID))
        else:
            error = 100*exp_neg(Q(".186")*i*STEP)+Q(1,10**14)
        for r in (1,2):
            total[r] += Q(3,2)*STEP*sqrt_hi(hi)*(hi*sqrt_hi(hi))**r*error
    return total


def tail_error(r):
    n = MIN_SIZE
    # On the outer arc the block exponent is at most 2-N/67 in both parities.
    # N^(9/2)*exp(-N/67) is decreasing for N>=n>9*67/2.
    assert Q('.0078')*Q(63,64)*2 >= Q(1,67)
    assert Q('.0078')*(216+Q(63,64)) <= 2
    assert 2*n>9*67
    assert 144*(4*2*n*sqrt_hi(2*n))**3*exp_neg(Q(n,67)) < Q(1,1000)
    assert 1728 <= Q(".008")*2*n*sqrt_lo(2*n)
    assert 300 <= 1200*(Q(".314")-Q(3*r+1,144))
    return 1200*12**(3*r+1)*exp_neg(Q(".157")*144)+Q(1,1000)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--lean-gaussian-bound', action='store_true',
                        help='use the uniform Gaussian replacement error proved in Lean')
    parser.add_argument('--lean-cheb-prefix', action='store_true',
                        help='use the Lean Gaussian allowance and the first 256 symmetric dyadic modes')
    options = parser.parse_args()
    total = retained_errors(options.lean_gaussian_bound, options.lean_cheb_prefix)
    for r,lo,hi,margin,trial_error in compact_signs(WINDOWS,1728):
        remaining = margin-total[r]-tail_error(r)-trial_error
        assert remaining > 0
        lower = floor(10**6*remaining)/10**6
        print(f"order {r}, {lo}/10000..{hi}/10000: retained error <= {float(total[r]):.9g}, "
              f"full-period margin > {lower:.6f}",flush=True)


if __name__ == "__main__":
    main()
