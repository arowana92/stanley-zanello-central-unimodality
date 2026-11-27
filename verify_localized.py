"""Rational endpoint checks for the local comparisons in localized-mode.md."""

from fractions import Fraction as Q

from verify_rising import PI_LO, PI_HI, decay, sqrt_hi, sqrt_lo


def tent_integral(j):
    """Integral of |t|**j times the trapezoidal Fourier cutoff."""
    return Q(2*(2**(j+2)-1), (j+1)*(j+2))


def check_kernels():
    for j, bound in enumerate((2, 2, 5, 11)):
        # Twice differentiating |frequency|^j is only used for its magnitude
        # away from the breakpoints. The actual multiplier uses (i*t)^j.
        variation = 2*(1 + 2**j)
        if j:
            variation += 4*(2**j-1)
        if j >= 2:
            variation += j*(j-1)*tent_integral(j-2)
        assert (tent_integral(j)+variation)/(2*PI_LO) < bound


def inversion_constants(n, order):
    epsilon = 1 / sqrt_lo(2*n)
    kernel = (2, 5, 11)[order]
    prefactor = 6*PI_HI*kernel*epsilon

    # Negative tilts have |h| <= 1250 and R^2/|h| <= 2500 at |h| >= 1.
    cutoff = 10**9
    neg = prefactor*600*1250**2*(1+1250+2*cutoff)*cutoff**order
    if order == 1:
        neg = prefactor*600*2500*(1+1250+2*cutoff)*cutoff

    # For r < 50 the cutoff is 4*10^5 max(10,r)^3. At r >= 1,
    # T/|h| <= 4*10^8 and T^2/|h| <= 1.6*10^17 at both endpoints.
    cutoff = 5*10**10
    small = prefactor*600*50**2*(1+50**3+2*cutoff)*cutoff**order
    if order == 1:
        small = prefactor*600*50**2*(4*10**8+cutoff+2*16*10**16)

    results = [neg, small]
    for r, factor in ((200_000, 10**4), (270_000, 60)):
        cutoff = factor*r**2
        value = prefactor*60*r**2*(1+r**3+2*cutoff)*cutoff**order
        results.append(value/r**3 if order == 1 else value)
    return results


def check_clock():
    # Express the deterministic area error in units V^2 / m^(3/2).
    # Here V/m < .001, V >= 10^6 and V^2/m >= 25*50^2.
    error = (3+Q(4,25*50**2)+Q(5,10**6))/2
    error += Q("1.51")*Q("1.001")*(1+Q(1,10**6))/2
    assert error*16**2 < 600 and error*5**2 < 60
    # Since epsilon >= exp(-R^2/2), a loss of 4.5 R^2 absorbs
    # the normalization by epsilon and the additive epsilon^8 error.
    radius_min = 50
    assert (Q("6.25")-Q("1.31")-Q("4.5"))*radius_min**2 > 3
    assert (32-16-Q(".25")-1/Q(radius_min)-Q("4.5"))*radius_min**2 > 3
    assert (Q(radius_min**2,100)-16-4)*radius_min**2 > 2
    for scale, weight, radius, tilt, cutoff in (
        (16, 600, 1250, 1250, 10**9),
        (16, 600, 50, 50**3, 5*10**10),
        (5, 60, 200_000, 200_000**3, 10**4*200_000**2),
        (5, 60, 270_000, 270_000**3, 60*270_000**2),
    ):
        eps = 1/sqrt_lo(2*10**61)
        assert scale*eps*radius < Q(".001")
        eta = weight*eps*radius**2
        assert eta*(Q(".1")+Q("2.002")*tilt+Q("3.003")*cutoff) < Q(".05")


def check_thresholds():
    assert max(inversion_constants(10**61, 0)) < Q(".74")
    assert max(inversion_constants(10**61, 1)) < Q(".024")
    assert max(inversion_constants(10**118, 2)) < 5
    assert 4*(Q(".024")+Q(".011")) < 1-Q(".74")-Q(".011")
    # Uniform tail from the high-frequency bands is < .01. Leave .001
    # for lattice multipliers and the discarded tests.
    max_frequency = 2*4*10**14
    min_scale = 10**91
    small_errors = (Q(max_frequency**3,min_scale)
                    + Q(max_frequency**5,min_scale**2)
                    + Q(36*11*max_frequency**3,10**(61*4)))
    assert small_errors < Q(".001")
    # At the join k/s >= 4/r_* the concentration lemma bounds r.
    assert (Q("2.60")/3+Q(7,250))*1_200_000/4 < 270_000
    assert 16*Q("2.001")**3 < (1_200_000*Q(".00000944"))**2


def check_fair_peak():
    cutoff = 9000
    rate = Q(".059")
    assert 3*Q(".67")/(8*Q("4.25")) > rate
    # Rational enclosures for z = rate * cutoff**(2/3).
    z_low, z_high = Q("25.52"), Q("25.54")
    assert z_low**3 < rate**3*cutoff**2 < z_high**3
    for j, target in enumerate((Q(".0000002"), Q(".0012"), Q("8.1"))):
        b = Q(3*(j+1), 2)
        low = (Q(262*cutoff**(j+1),j+1)+Q(11*cutoff**(j+2),j+2))/(PI_LO*10**15)
        tail = (24/PI_LO * sqrt_hi(1/rate)**(3*(j+1)) * decay(z_low)
                * sqrt_hi(z_high)**(3*(j+1)-2)/(1-(b-1)/z_low))
        assert low+tail+Q(1,10**12) < target


if __name__ == "__main__":
    check_kernels()
    check_clock()
    check_thresholds()
    check_fair_peak()
    print("Localized kernel, clock, tilted inversion and high-rank-mass bounds verified.")
