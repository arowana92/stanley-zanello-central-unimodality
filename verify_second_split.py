"""Compute the signed quadratic residual of the last-return polynomial trial."""

from fractions import Fraction as Q
from math import comb, lcm

from verify_gamma_polynomials import (
    chebyshev_coefficients, derivative_coefficients, gaussian_defect, monomial_coefficients,
    read_rows, split_product, subtract, uniform_bounds,
)
from verify_local_returns import gauss
from verify_return_bounds import diff, times
from verify_split_correction import drift


WIDTH = 256


def plus(*polys):
    result = [Q(0)] * max(map(len, polys))
    for poly in polys:
        for i, value in enumerate(poly):
            result[i] += value
    return result


def times_power(poly, degree, coefficient, width=WIDTH):
    """Multiply a polynomial in z=v/WIDTH by coefficient*v**degree."""
    return [Q(0)]*degree + [coefficient*width**degree*c for c in poly]


def derivative(poly, order):
    for _ in range(order):
        poly = [j*c/WIDTH for j, c in enumerate(poly) if j] or [Q(0)]
    return poly


def weighted_jet(left, right, order, a, b):
    """Arcsine average of x**a (1-x)**b times the signed split derivative."""
    terms = []
    for h in range(order+1):
        # Shifting input degrees changes the beta moment at each coefficient.
        # Remove the extra output powers once the weighted integral is computed.
        lhs = [Q(0)]*a + derivative(left, h)
        rhs = [Q(0)]*b + derivative(right, order-h)
        row = split_product(lhs, rhs)[a+b:]
        multiplier = (-1)**(order-h)*comb(order, h)
        terms.append([multiplier*c for c in row])
    return plus(*terms)


def first_split(left, right):
    return times_power(weighted_jet(left, right, 2, 1, 1), 1, Q(1, 2))


def second_split(left, right):
    third = subtract(weighted_jet(left, right, 3, 1, 2),
                     weighted_jet(left, right, 3, 2, 1))
    fourth = weighted_jet(left, right, 4, 2, 2)
    return plus(times_power(third, 1, Q(1, 6)), times_power(fourth, 2, Q(1, 8)))


def log_terms(parity):
    if parity is None:
        return ((2, Q(1,192)), (5, Q(1,30720))), ((4, Q(7,184320)), (7, Q(1,5160960)))
    return (((2, Q(2*parity+1,32)), (5, Q(1,1920))),
            ((1, Q(12*parity+1,192)), (4, Q(2*parity+1,1536)), (7, Q(1,80640))))


def symbol_coefficients(poly, first_log, second_log, width=WIDTH):
    """First two coefficients of exp(-tau*L1-tau**2*L2) times poly."""
    def multiply_log(row, coefficients):
        return plus(*(times_power(row, degree, c, width) for degree, c in coefficients))
    linear = multiply_log(poly, first_log)
    quadratic = subtract([c/2 for c in multiply_log(linear, first_log)],
                         multiply_log(poly, second_log))
    return [-c for c in linear], quadratic


def residuals():
    rows = read_rows()
    def poly(name):
        return monomial_coefficients(rows[name], 2**120)
    free, bridge, trial = map(poly, ("free", "bridge", "trial"))
    b1, b2 = symbol_coefficients(bridge, *log_terms(None))
    common = plus(split_product(b2, trial), first_split(b1, trial), second_split(bridge, trial))
    for parity, name in enumerate(("evenCorrection", "oddCorrection")):
        signed = plus(poly(name), drift(trial, Q(1,2), WIDTH))
        _, p2 = symbol_coefficients(free, *log_terms(parity))
        yield subtract(p2, common, split_product(b1, signed), first_split(bridge, signed))


def restrict_to_interval(poly, lo, hi):
    """Change z=v/256 to the unit variable (v-lo)/(hi-lo)."""
    denominator = lcm(*(c.denominator for c in poly))
    integers = [int(c*denominator) for c in poly]
    degree = len(poly)-1
    row = [integers[-1]]
    for j in range(degree-1,-1,-1):
        following = [lo*c for c in row]+[0]
        for k,c in enumerate(row):
            following[k+1] += (hi-lo)*c
        following[0] += integers[j]*WIDTH**(degree-j)
        row = following
    return [Q(c,denominator*WIDTH**degree) for c in row]


def chebyshev_jets(poly, width, order):
    row, denominator = chebyshev_coefficients(poly)
    bounds = []
    for r in range(order+1):
        bounds.append(Q(sum(map(abs,row)),denominator)*Q(2,width)**r)
        row = derivative_coefficients(row)
    return bounds


def gaussian_jet_errors(poly, divisor, order):
    """Bound derivatives of exp(-v^3/divisor)-poly on [0,20] and [20,144]."""
    cut, end = 20, 144
    defect = chebyshev_jets(gaussian_defect(poly, WIDTH, divisor), WIDTH, order)
    low = [abs(1-poly[0])+cut*defect[0]/WIDTH]
    rates = [Q(3*cut**2,divisor), Q(6*cut,divisor), Q(6,divisor)]
    for r in range(1,order+1):
        low.append(defect[r-1]/WIDTH + sum(comb(r-1,k)*rates[k]*low[r-1-k]
                                          for k in range(min(2,r-1)+1)))
    high = chebyshev_jets(restrict_to_interval(poly,cut,end), end-cut, order)
    factor = [Q(1)]
    for r in range(order+1):
        high[r] += gauss(factor,divisor,Q(cut),Q(end))
        factor = diff(factor,divisor)
    return low, high


def product_jet(a, b, r):
    return sum(comb(r,h)*a[h]*b[r-h] for h in range(r+1))


def multiplier_error(poly, errors, r):
    bounds = []
    for limit, row in zip((20,144),errors):
        factors = [sum(abs(c)*Q(limit,WIDTH)**j for j,c in enumerate(derivative(poly,k)))
                   for k in range(r+1)]
        bounds.append(product_jet(factors,row,r))
    return max(bounds)


def second_input_error():
    """Transfer the polynomial quadratic residual to the actual Gaussian curves."""
    rows = read_rows()
    def poly(name):
        return monomial_coefficients(rows[name],2**120)
    trial = poly("trial")
    fj = chebyshev_jets(trial,WIDTH,4)
    pe = gaussian_jet_errors(poly("free"),24,0)
    be = gaussian_jet_errors(poly("bridge"),96,4)
    b1,b2 = symbol_coefficients([Q(1)],*log_terms(None))
    eb = list(map(max,*be))
    e1 = [multiplier_error(b1,be,r) for r in range(3)]
    e2 = multiplier_error(b2,be,0)
    allowance = Q(0)
    for parity,name in enumerate(("evenCorrection","oddCorrection")):
        signed = plus(poly(name),drift(trial,Q(1,2),WIDTH))
        gj = chebyshev_jets(signed,WIDTH,2)
        _,p2 = symbol_coefficients([Q(1)],*log_terms(parity))
        v = 144
        error = (multiplier_error(p2,pe,0)+e2*fj[0]+e1[0]*gj[0]
                 +Q(v,8)*(product_jet(e1,fj,2)+product_jet(eb,gj,2))
                 +Q(v,24)*product_jet(eb,fj,3)+Q(v*v,128)*product_jet(eb,fj,4))
        allowance = max(allowance,error)
    return allowance


def interpolate(values):
    """Return power coefficients from exact evaluations at consecutive integers starting at zero."""
    coeffs = [Q(0)]*len(values)
    basis = [Q(1)]
    for k in range(len(values)):
        for i,c in enumerate(basis):
            coeffs[i] += c*values[0]
        values = [v-u for u,v in zip(values,values[1:])]
        basis = [c/(k+1) for c in times(basis,[-k,1])]
    return coeffs


def check_log_terms():
    # The coefficients of tau and tau^2 in the log after j=v/tau.
    for parity in (None,0,1):
        expected = [{},{}]
        denominators = (6,180,2835) if parity is None else (2,12,45)
        for a, divisor in enumerate(denominators,1):
            costs = []
            for j in range(2*a+2):
                total = sum(h**(2*a) for h in range(1,2*j+(parity or 0)+1))
                if parity is None:
                    total -= 2*sum(h**(2*a) for h in range(1,j+1))
                costs.append(Q(total,32**a*divisor))
            powers = interpolate(costs)
            for s in (1,2):
                index = 3*a-s
                if index < len(powers) and powers[index]:
                    expected[s-1][index] = powers[index]
        assert expected == [dict(terms) for terms in log_terms(parity)]


def check_monomials():
    """Compare the coefficient with exact discrete arcsine expectations at 0..a+b."""
    for a in range(7):
        for b in range(7):
            order = a+b
            if order < 2:
                continue
            row = []
            for j in range(order+1):
                count = sum(comb(2*k,k)*comb(2*(j-k),j-k)*k**a*(j-k)**b for k in range(j+1))
                row.append(Q(count, 4**j))
            coeff = interpolate(row)[order-2]
            left = [Q(0)]*a+[Q(WIDTH**a)]
            right = [Q(0)]*b+[Q(WIDTH**b)]
            computed = second_split(left, right)
            assert all(c==(coeff*WIDTH**(order-2) if k==order-2 else 0)
                       for k,c in enumerate(computed))


def main():
    check_monomials()
    check_log_terms()
    replacement = second_input_error()
    assert replacement < Q(18,10**14)
    print(f"Gaussian replacement error <= {float(replacement):.9g}", flush=True)
    for parity, poly in enumerate(residuals()):
        # Restrict to 0 <= v <= 144 before converting to a Chebyshev series.
        value, slope = uniform_bounds([c*Q(144, WIDTH)**j for j,c in enumerate(poly)], 144)
        assert value < (Q(".008") if parity==0 else Q(".093"))
        assert slope < (Q(".012") if parity==0 else Q(".126"))
        print(f"parity {parity}: polynomial norm <= {float(value):.9g}, "
              f"derivative <= {float(slope):.9g}")


if __name__ == "__main__":
    main()
