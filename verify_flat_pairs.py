"""Check the flat-pair identities and numerical endpoints in the concentration proof."""

from fractions import Fraction
from itertools import product
from math import factorial

from verify_comparison import exponential_sum, inversion_error


def check_flat_pairs():
    # Each edge has weight (radius * phase)**j. Gaussian integers give exact phases
    # even when the symmetric edge action of a single step is half-integral.
    for a, b, c in ((3, 4, 5), (0, 1, 1)):
        powers = [(1, 0)]
        for _ in range(27):
            x, y = powers[-1]
            powers.append((a * x - b * y, b * x + a * y))
        cosine = Fraction(a * a - b * b, c * c)
        for radius in (Fraction(1, 2), Fraction(199, 200)):
            q = radius**2
            diagonal_ratio = 1 - 2 * q * (1 - cosine) / (1 + q)**2
            for start in range(1, 12, 2):
                rows = {}
                for first, second in product((-1, 1), repeat=2):
                    middle = start + first
                    end = middle + second
                    if end < 0:
                        continue
                    index = min(start, middle) + min(middle, end)
                    x, y = powers[index]
                    row = rows.setdefault(end, [0, 0, 0])
                    row[0] += radius**index * Fraction(x, c**index)
                    row[1] += radius**index * Fraction(y, c**index)
                    row[2] += radius**index
                for end, (real, imag, positive) in rows.items():
                    ratio = diagonal_ratio if end == start else 1
                    assert real**2 + imag**2 == ratio * positive**2


def check_uniform_saddle():
    f = Fraction
    lambda_lower = (1 - f("1.30") / 16)**2
    assert lambda_lower > f(".844")
    assert lambda_lower * (f(".75") - f(".75")**2 / 32) > f(".60")
    assert 2 * (1 / f("10.4") - f(1, 32))**2 > f(".0084")
    assert 6 * f(".37") / f(".079")**3 < 4600
    assert f("2.60") * (1 + f("1.30") / (2 * (16 - f("1.30")))) < f("2.72")
    trial = (1 - f(10, 2 * 13**2)) * (1 - f(5, 128))
    assert trial * exponential_sum(f(9, 128), 2) > 1

    # Norm loss when the frequency multiple first exceeds 200.
    block_loss = f(".0975")**3 * 200**2 / 16
    t = f(".272")
    exp_upper = exponential_sum(t, 6) + t**7 / factorial(7) / (1 - t / 8)
    assert exp_upper * (1 + 1 / exponential_sum(block_loss, 6)) / 2 < f(".8")
    assert f(".023") / 20**4 > f(".00000014")
    assert f(".023") * 200**2 / 400**4 > f(".00000003")

    n_blocks = 10**21
    lower_width = 2_890_000_000
    assert lower_width**2 < f(".0084") * n_blocks
    assert 4600 * 6**3 / (6 * f(".0084") * lower_width) < f(".007")
    assert f(16 * 10**6 * 6, lower_width) < f(".034")
    assert f(".5") - 4600 * f(".0000015") / (6 * f(".0084")) > f(".36")
    assert f(".00000014") * f(".0000015")**2 * n_blocks == 315
    assert 4 * 3**20 * (1 + 10**4 * 4 * 10**11)**3 * f(3, 8)**315 < f(".01")


def check_concentration_bounds():
    f = Fraction
    epsilon = f(1, 10**39)
    assert (f("2.60") / 3 + f(7, 250)) * 1_200_000 / 4 < 270_000
    assert 2 * 10**5 * epsilon * 270_000**5 < f(".000005")
    assert inversion_error(epsilon, 1250, 10**9, 0) < f(".001")
    assert 10**7 * epsilon * 2500 * 3 * 10**9 * 10**18 <= f(".075")
    assert inversion_error(epsilon, 50, 5 * 10**10, 0) < f(".001")
    assert 10**7 * epsilon * 50**2 * (50**3 + 5 * 10**10) * 16 * 10**16 < f(".201")
    assert inversion_error(epsilon, 250, 625_000_000, 1) < f(".2")
    assert inversion_error(f(1, 10**67), 1250, 4 * 10**11, 2) < f(".001")

    for c, r in ((10**4, 200_000), (60, 270_000)):
        cutoff = c * r**2
        assert inversion_error(epsilon, r, cutoff, 0) / r**2 < f(".034")
        assert inversion_error(epsilon, r, cutoff, 1) / r**5 < f(".0017")
        assert inversion_error(f(1, 10**67), r, cutoff, 2) / r**2 < f(".54")

    # Bound both transforms and both tails with a rational upper bound on e**(-1).
    max_r = 1_200_000
    assert f(".0735") * 60**2 / 2 > 132
    assert 16 * 10**6 * 200 * max_r**6 * f(3, 8)**132 < f(".001")
    assert f(588, 10**11) * 200_000**2 > 235
    assert 16 * 3**20 * (1 + 10**4 * max_r**3)**3 * f(3, 8)**235 < f(".001")
    assert f(1, 10**24) * (1 + 78 * f("2.303"))**6 < f(35, 10**12)


if __name__ == "__main__":
    check_flat_pairs()
    check_uniform_saddle()
    check_concentration_bounds()
    print("Two-step phases, uniform saddle bounds and concentration endpoints verified.")
