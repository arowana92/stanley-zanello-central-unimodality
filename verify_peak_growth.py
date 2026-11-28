"""Check the signed growth budget for saddle parameters between 7.194 and 8.9925.

All comparisons and shifts are exact. The output bounds the arithmetic
expressions in this file. Their application to the integer ranks also needs
the analytic inequalities over each bin and the saddle coverage theorem.
"""

import argparse
from fractions import Fraction as Q

from verify_rank_bins import EPS, ENERGY, SCALE, charge, exp_cost, root_lo

L = Q(3, 40)
H = Q(37, 40)
MAX_SHIFT = 32
START = Q(1199, 100)*Q(3, 5)
STOP = Q(1199, 100)*Q(3, 4)
CUTS = (START, START+Q(1, 16), START+Q(1, 4), START+Q(1, 2), START+Q(3, 4), START+1, START+Q(3, 2), STOP)


def down(x):
    return Q((x*SCALE).__floor__(), SCALE)


def negexp_lower(x):
    assert 0 <= x <= 256
    return down((1-x/256)**256)


def root_hi(x):
    return root_lo(x) + Q(1, SCALE)


def prefix(g, G):
    """Lower prefix margin, including the occupation-time variance estimate."""
    f = L + EPS
    zlo = root_lo((1-(G/128)**2)*(1-f)**3/12)
    zhi = root_hi((1-L+EPS)**3/12)
    drift = g/2 * (1-g*g*EPS/12)
    U = g*(1-f)/2
    K = down(Q(".79")/root_hi(f))
    den = down(2*U*(1-U/64) + K*negexp_lower(U/64 + U/K + f*U*U/2))
    V = charge((f*G+1/drift)/(4*zlo*zlo*den))
    mass = Q(".3989")*negexp_lower(V/2) - Q(".005")
    slope = Q(".399")*(Q(".406")+Q(".293")*V) + Q(".007")
    return zlo, zhi, drift, den, down(Q(".999")*g*zlo*mass - slope)


def late(g, G, zhi, drift, den):
    """Minimize the reflected, two-harmonic cost over the allowed shifts."""
    costs = []
    for shift in range(MAX_SHIFT+1):
        a = (drift+Q(shift, 2))*H*(1-H/2)
        cap = (G+shift)/2-a
        if min(a, cap) <= 0 or max(a, cap) > Q(".24")*64:
            continue
        ex = exp_cost(shift*shift*ENERGY/8-a*a/2)
        if ex is None:
            continue
        reflect = min(1, Q(".84") / (a*root_lo(1-H-EPS)))
        surv = 2*cap+Q(".8")*exp_cost(-Q(".48")*cap*cap*L)/root_lo(L)
        cost = Q("1.001")*ex*reflect*surv/den*(Q("54.5")+(G+shift)*zhi*Q("3.6"))
        costs.append((charge(cost), shift))
    return min(costs)


def early(g, G, zhi, den, left, edge):
    """Even witness codes use the fifths split. Odd codes use the area bound."""
    v = left-EPS
    e = edge+EPS
    outer, inner = v/5-2*EPS, 3*v/5-EPS
    assert outer/EPS >= 40 and inner/EPS >= 80 and e < 1
    yroot = root_hi((e+EPS)/2)
    vroot = root_lo(v-EPS)
    prt = root_hi(Q(22, 7))
    candidates = []
    for shift in range(MAX_SHIFT+1):
        lam = G+shift
        beta = lam*e/4
        z = root_lo((1-(lam*(1-v)/128)**2)*(1-e)**3/12)
        base = shift*shift*ENERGY/8 - v*(1-e/2)**2*(g+shift)*(g*(1-g*g*EPS/6)+shift)/8
        cost = Q("1.001")*(zhi/z)**2*(Q(".36")+lam*z*Q(".43"))*(edge-left)/(2*den)
        norm = exp_cost(base)
        if norm is not None:
            surv = 2*beta+Q(".8")*exp_cost(-Q(".48")*beta*beta*outer)/root_lo(outer)
            pin = (Q(1,2)+beta/128)*surv*surv*Q(".86")/root_lo(inner)
            candidates.append((charge(cost*pin*norm), 2*shift))
        y = lam*e*yroot/2
        save = (g+shift)**2*v*(v*v-EPS**2)/96*(1-(lam*e/256)**2/6)
        norm = exp_cost(base+lam*e/256-save+y*y/4)
        if norm is not None:
            mark = Q(".8")*(1+y*(prt+min(prt,y))/2)/vroot**3
            candidates.append((charge(cost*mark*norm), 2*shift+1))
    return min(candidates)


def calculate(g, G, step):
    zlo, zhi, drift, den, pre = prefix(g, G)
    last, shift = late(g, G, zhi, drift, den)
    witnesses = []
    total = Q(0)
    left = L
    while left < H+2*EPS:
        endpoint = min(H+2*EPS, left+step)
        cost, witness = early(g, G, zhi, den, left, endpoint)
        total += cost
        witnesses.append(witness)
        left = endpoint
    return pre, total, last, pre-total-last, witnesses, shift


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-witnesses", action="store_true", help="print packed base-128 shift codes and the late shift")
    args = parser.parse_args()
    for i, (g, G) in enumerate(zip(CUTS, CUTS[1:])):
        step = Q(1, 512 if i == 0 else 256 if i < 4 else 128)
        pre, e, l, gap, codes, shift = calculate(g, G, step)
        assert gap > Q(22, 1000), (i, gap)
        if args.lean_witnesses:
            packed = sum(code << (7*j) for j, code in enumerate(codes))
            print(f"⟨{hex(packed)}, {shift}⟩,", flush=True)
        else:
            print(f"g in [{g}, {G}], {len(codes)} time bins, prefix {pre}, "
                  f"early {e}, late {l}, margin {gap}", flush=True)


if __name__ == "__main__":
    main()
