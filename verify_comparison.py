"""Rational endpoint checks for the transfer and tilted-mode estimates."""

from fractions import Fraction
from math import factorial


def exponential_sum(x, terms):
    return sum(x ** j / factorial(j) for j in range(terms + 1))


def check_saddle_constants():
    # Propagated error bounds on the two smaller complex disks.
    boundary_error = Fraction(11, 10**20)
    inner_error = Fraction(2, 10**13)
    outer_error = Fraction(3, 10**8)
    assert boundary_error**17 < inner_error**25
    assert boundary_error**2 < outer_error**5
    assert 2 * outer_error < Fraction(".01") * Fraction(".004")**2
    assert Fraction(2, 3) * Fraction("1.65") - 100 * inner_error > 1
    curvature_error = 2 * 10**4 * inner_error
    assert Fraction(2, 9) * Fraction("1.65") - curvature_error > Fraction(".35")
    assert Fraction(2, 9) * Fraction("2.60") + curvature_error < Fraction(".60")
    third_error = 6 * inner_error / Fraction(".006")**3
    assert Fraction(8, 27) * Fraction("2.60") / Fraction(".996")**3 + third_error < 1

    # Upper-bound exp(.42) by the series and a geometric remainder.
    energy = Fraction(".42")
    exp_upper = exponential_sum(energy, 6) + energy**7 / factorial(7) / (1 - energy / 8)
    block_loss = Fraction(".0999")**3 * 200**2 / 16
    row_bound = (1 + 1 / exponential_sum(block_loss, 8)) / 2
    assert exp_upper * row_bound < Fraction(".85")
    assert 9 * Fraction(".15") / 201**2 > Fraction(".00003")
    assert 9 * Fraction(".15") / 400**2 > Fraction(".000008")

    pairs_on_height_scale = 10**10
    lower_width = 59100
    assert lower_width**2 < Fraction(".35") * pairs_on_height_scale
    assert Fraction(2500 * 6, lower_width) < Fraction(".254")
    assert 6**3 / (6 * Fraction(".35") * lower_width) < Fraction(".002")
    assert 1 - Fraction(".254") - Fraction("1.254") * Fraction(".002") / Fraction(".998") > Fraction(".74")
    exponent = Fraction(".00003") * Fraction(".02")**2 * pairs_on_height_scale
    assert exponent == 120
    # exp(20) < 3**20 and exp(-120) < (3/8)**120.
    volume = 2 * 3**20 * (1 + 10**4 * 10**5)**3
    assert volume * 2 * Fraction(3, 8)**120 < Fraction(".01")


def inversion_error(epsilon, radius, cutoff, order):
    return 10**7 * epsilon * radius**2 * (radius**3 + cutoff) * cutoff**(order + 1)


def check_mode_constants():
    max_r = 1_200_000
    epsilon = Fraction(1, 10**50)
    assert 2 * 10**5 * epsilon * max_r**5 < Fraction(1, 10**13)

    assert inversion_error(epsilon, 2000, 10**9, 1) < Fraction(1, 10**7)
    assert inversion_error(epsilon, 2000, 10**12, 0) < Fraction(1, 10**10)
    # For the small positive tilts, T**2/h <= 10**18.
    assert 10**7 * epsilon * 2000**2 * (2000**3 + 10**12) * 10**18 < Fraction(1, 10**6)
    assert inversion_error(epsilon, 2000, 4 * 10**10, 1) < Fraction(1, 10**4)

    # At r >= 2000 the normalized errors are polynomials increasing in r.
    cutoff = 10**4 * max_r**2
    assert inversion_error(epsilon, max_r, cutoff, 0) / max_r < Fraction(".0031")
    assert inversion_error(epsilon, max_r, cutoff, 1) / max_r**4 < Fraction(".000026")
    second_epsilon = Fraction(1, 10**82)
    assert inversion_error(second_epsilon, 2000, 10**12, 2) < Fraction(".001")
    assert inversion_error(second_epsilon, max_r, cutoff, 2) / max_r < Fraction(".0063")
    assert 16 * Fraction("2.001")**3 < (max_r * Fraction(".00000944"))**2

    # For the large positive tilt, remove half the first Fourier tail exponent.
    assert Fraction(".0000039") * (10**4)**2 / 2 == 195
    assert 4 * 3**20 * Fraction(3, 8)**195 * 10**10 * max_r**6 < Fraction(".001")


if __name__ == "__main__":
    check_saddle_constants()
    check_mode_constants()
    print("Saddle, tilted-mode and interval-overlap endpoint bounds verified.")
