"""Reconstruct the rank-shift witnesses for the Lean right-flank bin checks."""

import argparse
from fractions import Fraction as Q
from functools import lru_cache
from math import ceil, factorial, isqrt

SCALE = 10**6
EPS = Q(1, 4096)
H = Q(15, 16)
ENERGY = (1+EPS)*(2+EPS)/6
SHIFTS = (0, 1, 2, 4, 6, 9, 12, 16, 20, 24, 28, 32)
FOURIER = (19, 810, 98000)


def root_lo(x):
    return Q(isqrt(x.numerator*SCALE**2//x.denominator), SCALE)


def charge(x):
    return Q(ceil(x*SCALE), SCALE)


@lru_cache(maxsize=None)
def decay_index(i):
    y = Q(i, 1024)
    return charge(1/sum(y**j/factorial(j) for j in range(15)))**8


def exp_cost(exponent):
    if exponent > 0:
        return None
    return decay_index((-128*exponent).__floor__())


def signed_costs(mass, diff, curve, delta, zhi):
    du = Q("1.001")*delta*zhi
    return (mass, Q("1.001")*diff + du*mass, curve + 2*du*diff)


def early_candidates(g, top, v, w, denom, zhi):
    e = w+EPS
    chunk = v/3 - 2*EPS
    count = (w-v)/2+EPS
    assert chunk/EPS >= 80
    for idx, delta in enumerate(SHIFTS):
        lam = top+delta
        beta = lam*e/4
        front = 2*beta + Q(".8")/root_lo(chunk)
        z = root_lo((1-(lam*(1-v)/128)**2)*(1-e)**3/12)
        norm = exp_cost(delta**2*ENERGY/8 -
                        v*(1-e/2)**2*(g+delta)*(g*(1-g*g*EPS/6)+delta)/8)
        if norm is None:
            continue
        prob = count*(Q(1,2)+beta/128)*front**2*norm/(root_lo(chunk)*denom)
        ratio = zhi/z
        costs = signed_costs(Q(".46")*ratio, Q(".46")*ratio**2, Q(".56")*ratio**3, delta, zhi)
        yield idx, tuple(charge(prob*x) for x in costs)


def late_candidates(g, top, fraction, denom, zhi):
    for idx, delta in enumerate(SHIFTS):
        a = (g/2*(1-g*g*EPS/12)+Q(delta, 2))*H*(1-H/2)
        cap = (top+delta)/2-a
        if min(a, cap) < 0 or max(a, cap) > Q(".24")*64:
            continue
        norm = exp_cost(delta**2*ENERGY/8-a*a/2)
        if norm is None:
            continue
        prob = norm*(2*cap+Q(".8")/root_lo(fraction))/denom
        costs = signed_costs(*FOURIER, delta, zhi)
        yield idx, tuple(charge(prob*x) for x in costs)


def pick(candidates):
    pairs = list(candidates)
    assert pairs
    return [min((costs[r], idx) for idx, costs in pairs) for r in range(3)]


def saddle(curve, index):
    fraction = Q(1, 14 if curve else 10)
    g = Q("11.99")*(Q(15,16) if curve else Q(3,4)) + 2*index
    top = min(Q(25), g+2)
    assert g < top
    f = fraction+EPS
    zlo = root_lo((1-(top/128)**2)*(1-f)**3/12)
    zhi = root_lo((1-fraction+EPS)**3/12) + Q(1,SCALE)
    kappa = g/2*(1-g*g*EPS/12)
    denom = 2*kappa*(1-f)/(1+top/128)
    variance = (f+(1+top/128)/(1-f)*(f*f+1/(2*kappa**2)))/(4*zlo**2)
    x = variance/2
    gauss = 1-x+x**2/2-x**3/6
    totals = [Q(0)]*3
    digits = [0]*3
    for i in range(42):
        v = min(H, fraction+Q(i,48))
        w = min(H, fraction+Q(i+1,48))
        if v == w:
            continue
        for r, (value, shift) in enumerate(pick(early_candidates(g,top,v,w,denom,zhi))):
            totals[r] += value
            digits[r] += shift*16**i
    late = pick(late_candidates(g,top,fraction,denom,zhi))
    late_code = sum(shift*16**r for r, (_, shift) in enumerate(late))
    loss = [totals[r]+late[r][0] for r in range(3)]
    mass = Q(".3989")*gauss-Q(".005")-loss[0]
    central = variance/(1+variance/2)-gauss
    assert mass > 0 and central < 0
    growth = Q(".999")*zlo*g*mass-Q(".25")-loss[1]
    curvature = -(Q(".3989")*central+Q(".010")+loss[2])
    margin = curvature if curve else growth
    assert margin > 0, (curve,index,margin)
    return (*digits, late_code), margin


def upper_half_first_hits():
    base = Q(119, 5)
    drift = Q(19, 50)
    cuts = [min(H, Q(1, 10) + Q(i, 8)) for i in range(8)]
    assert cuts[0] == Q(1, 10) and cuts[-1] == H
    result = Q(0)
    for v, w in zip(cuts, cuts[1:]):
        e = w + EPS
        chunk = v/3 - 2*EPS
        root = root_lo(chunk)
        a = v*(1-e/2)**2/8
        assert v < w and e < 1 and chunk/EPS >= 80 and a >= Q(1, 160)
        width = e/2 + Q(4, 5)/(root*base)
        decay = exp_cost(-a*Q(19, 20)*base**2)
        per_time = base/drift*width**2/root*decay/(1-e)**3
        result += charge(((w-v)/2 + EPS)*per_time)
    assert result <= Q(1, 40)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-witnesses", action="store_true", help="print the four packed shift-index columns")
    args = parser.parse_args()
    for curve, count in ((False,9), (True,7)):
        rows = [saddle(curve,i) for i in range(count)]
        if args.lean_witnesses:
            print("#[" + ",\n  ".join("⟨" + ", ".join(hex(x) for x in digits) + "⟩"
                                      for digits, _ in rows) + "]")
        else:
            margin = min(value for _, value in rows)
            print(f"{'Curvature' if curve else 'Growth'}: {count} saddle bins, margin > {int(margin*10000)/10000:.4f}")


    if not args.lean_witnesses:
        print(f"Upper-half first-hit loss in seven time bins: {upper_half_first_hits()} <= 1/40")


if __name__ == "__main__":
    main()
