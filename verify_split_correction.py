"""Bound the first correction for the direct discrete last-return trial.

All polynomials use z=v/256. The exact beta product and Gaussian defect
checks use the dyadic coefficients shared with the Lean development.
"""

from fractions import Fraction as Q

from verify_gamma_polynomials import (
    correction, derivative_coefficients, gaussian_defect,
    monomial_coefficients, read_rows, split_product, subtract, uniform_bounds,
)


def drift(poly, c, width):
    """Coefficients of c f'(v) + v f''(v)/2 in the common variable z."""
    return [j*(c+Q(j-1, 2))*a/width for j, a in enumerate(poly) if j]


def gaussian_errors(poly, width, divisor, cutoff):
    """Uniform errors in the value and first two v derivatives."""
    defect = gaussian_defect(poly, width, divisor)
    norm, slope = uniform_bounds(defect, width)
    # D(z)/width = P'(v)+a(v)P(v), where a=3v^2/divisor.
    # The integrating factor ratio from an earlier time is at most one.
    value = abs(poly[0]-1) + Q(cutoff, width)*norm
    rate = Q(3*cutoff**2, divisor)
    first = norm/width + rate*value
    second = slope/width + Q(6*cutoff, divisor)*value + rate*first
    return value, first, second


def cheb_jet(row, width, order):
    scale = 2**120
    bounds = []
    for k in range(order+1):
        bounds.append(Q(2**k*sum(map(abs, row)), width**k*scale))
        row = derivative_coefficients(row)
    return bounds


def check_first_correction(cutoff=144):
    width = 256
    rows = read_rows()
    P, B, F = [monomial_coefficients(rows[name], 2**120) for name in ("free", "bridge", "trial")]
    # H=B⋆F. The term B⋆halfDrift(F) cancels the corresponding part
    # of the corrected signed trial G=M+halfDrift(F).
    H = split_product(B, F)
    B1 = correction(B, width, -Q(1,192), -Q(1,30720))
    corrected_bridge = split_product(subtract(B1, drift(B, Q(1,2), width)), F)
    dP = gaussian_errors(P, width, 24, cutoff)[0]
    dB, dB1, dB2 = gaussian_errors(B, width, 96, cutoff)
    f0, f1, f2 = cheb_jet(rows["trial"], width, 2)
    U = Q(cutoff)
    log_bridge = U**2/192 + U**5/30720
    result = []
    for parity, name in enumerate(("evenCorrection", "oddCorrection")):
        M = monomial_coefficients(rows[name], 2**120)
        log_free = (2*parity+1)*U**2/32 + U**5/1920
        P1 = correction(P, width, -Q(2*parity+1,32), -Q(1,1920))
        residual = subtract(P1, drift(H, Q(1), width), corrected_bridge, split_product(B, M))
        bound = uniform_bounds(residual, width)[0]
        g0 = cheb_jet(rows[name], width, 0)[0] + (f1+U*f2)/2
        # Replace P, B by p, rho in the original split formula
        # and use x(1-x)<=1/4 for the quadrature correction.
        transfer = (log_free*dP + log_bridge*dB*f0 + dB*g0
                    + U*(dB2*f0+2*dB1*f1+dB*f2)/8)
        if bound + transfer >= Q(3, 10**12):
            raise ArithmeticError(f"first correction exceeds target in parity {parity}")
        print(f"parity {parity}: polynomial {float(bound):.6g}, "
              f"input allowance {float(transfer):.6g}", flush=True)
        result.append(bound + transfer)
    return max(result)


if __name__ == "__main__":
    check_first_correction()
