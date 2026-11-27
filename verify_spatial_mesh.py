"""Check one Fourier length group's three spatial signs with integer dot products."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as Q
from functools import partial
from math import ceil, comb, isqrt
from pathlib import Path

from verify_packed_residual import check_frequency, cosine_offset
from verify_rising import PI_HI, PI_LO


MESH = 32768
AMPLITUDE_DEN = 1 << 80
PHASE_DEN = 1 << 112
WINDOWS = ((1, Q(".1359"), Q(".339"), 1),
           (2, Q(".333"), Q(".404"), -1),
           (1, Q(".398"), Q(".631"), -1))


def phase_table():
    """Round the mesh cosines to integers, bounding every rounding error."""
    half = MESH//2
    table = []
    radius = 0
    for i in range(half+1):
        lo, hi = cosine_offset(PHASE_DEN, half.bit_length()-1, i)
        center = (lo+hi)//2
        table.append(center-PHASE_DEN)
        radius = max(radius, hi-center)
    return table + table[-2:0:-1], Q(radius, PHASE_DEN)


def endpoint_values(t, program, first, last, period, inv_survival, lean_path=None):
    _, bounds, (s, candidates) = check_frequency(program, last, period, t, lean_path=lean_path,
                                                  prove_inputs=True)
    span = max(1, last-first)
    values = []
    for row in candidates:
        # Floor exactly to an absolute error below 1/AMPLITUDE_DEN.
        a = [(row[n]*AMPLITUDE_DEN*inv.numerator)//(s*inv.denominator)
             for n, inv in zip(range(first, last+1), inv_survival)]
        deviation = max(abs(span*v - (span-i)*a[0] - i*a[-1]) for i, v in enumerate(a))
        values.append((a[0], a[-1], deviation))
    if lean_path is not None:
        write_chord_proof(lean_path, first, last, period, t, s, bounds[2], values)
    return [(left, right, bounds[2]+Q(span+deviation, span*AMPLITUDE_DEN))
            for left, right, deviation in values]


def write_chord_proof(path, first, last, period, mode, scale, amplitude_error, endpoints):
    """Extend the generated amplitude proof by the length check for both parities."""
    left, right, deviations = zip(*endpoints)
    span = max(1, last-first)
    deviation = max(deviations)
    amp_units = ceil(amplitude_error*10**15)
    lines = ["namespace FourierSample", "open CentralUnimodality CentralUnimodality.Residual",
             f"def leftEnd (σ : ℕ) : ℤ := if σ=0 then {left[0]} else {left[1]}",
             f"def rightEnd (σ : ℕ) : ℤ := if σ=0 then {right[0]} else {right[1]}",
             "theorem lengthChecked (σ : ℕ) (hσ : σ ≤ 1) :",
             f"    MeshLength.check {first} {last} (2^80) {scale} (candidates σ)",
             f"      (leftEnd σ) (rightEnd σ) {deviation} = true := by",
             "  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hσ with rfl|rfl <;> decide +kernel",
             f"theorem interpolatedAmplitude (n δ : ℕ) (hδ : δ ≤ 1) (hl : {first} ≤ n+δ) (hr : n+δ ≤ {last}) :",
             "    let d : ℕ := 2^80",
             f"    |signedAmplitude n δ (gridFrequency {period} {mode}) -",
             f"      chord (((n+δ-{first}:ℕ):ℝ)/{span}) ((leftEnd (1-δ):ℝ)/d)",
             f"        ((rightEnd (1-δ):ℝ)/d)| ≤ ({amp_units}:ℝ)/10^15 +",
             f"          (({span}:ℝ)+{deviation})/({span}*d) := by",
             f"  exact MeshLength.checked_chord (n := n) (δ := δ) (θ := gridFrequency {period} {mode})",
             f"    (first := {first}) (last := {last}) (d := 2^80) (E := {deviation})",
             f"    (by decide) hl hr (s := {scale}) (by decide) (candidates (1-δ)) (leftEnd (1-δ)) (rightEnd (1-δ))",
             "    (lengthChecked (1-δ) (by omega)) (sampledAmplitude n δ hδ (by omega) hr)",
             "#print axioms interpolatedAmplitude", "end FourierSample"]
    path.write_text("import CentralUnimodality.MeshLength\n" + path.read_text() + "\n".join(lines) + "\n")
    error = Q(amp_units, 10**15) + Q(span+deviation, span*AMPLITUDE_DEN)
    print(f"Wrote {path} for mode {mode}, {first}..{last}. "
          f"Both parities have chord error at most {ceil(error*10**15)}/10^15.")


def collect(program, first, last, period, stop, jobs):
    inv_survival = [Q(4**n, comb(2*n, n)) for n in range(first, last+1)]
    one_mode = partial(endpoint_values, program=program, first=first, last=last,
                       period=period, inv_survival=inv_survival)
    modes = range(1, stop+1)
    if jobs == 1:
        values = map(one_mode, modes)
    else:
        with ProcessPoolExecutor(max_workers=jobs) as pool:
            values = list(pool.map(one_mode, modes, chunksize=4))
    rows = [[[], []], [[], []]]
    # sum t^r e_t in each parity, including both amplitude and length errors.
    costs = [[Q(0), Q(0)], [Q(0), Q(0)]]
    for t, pair in enumerate(values, 1):
        for parity, (left, right, e) in enumerate(pair):
            rows[parity][0].append(left)
            rows[parity][1].append(right)
            for r in (1, 2):
                costs[parity][r-1] += t**r*e
    return rows, costs


def window_margin(amplitudes, cost, table, phase_error, period, scale, window):
    r, left, right, sign = window
    h = Q(period, MESH*scale)
    lo, hi = left//h, ceil(right/h)
    # The r-th derivative has phase r*pi/2. All mesh indices are exact.
    offset = r*(MESH//4)
    weights = [sign*t**r*v for t, v in enumerate(amplitudes, 1)]
    node = min(sum(w*table[(i*t+offset) % MESH] for t, w in enumerate(weights, 1))
               for i in range(lo, hi+1))
    factor = Q(4*scale, period)
    unit_lo, unit_hi = 2*PI_LO*scale/period, 2*PI_HI*scale/period
    value = Q(node, AMPLITUDE_DEN*PHASE_DEN)
    value -= phase_error*Q(sum(map(abs, weights)), AMPLITUDE_DEN)
    mesh_bound = factor*(unit_lo if value >= 0 else unit_hi)**r*value
    norms = sum(t**(r+2)*abs(v) for t, v in enumerate(amplitudes, 1))
    curvature = factor*unit_hi**(r+2)*Q(norms, AMPLITUDE_DEN)
    reserve = Q(".00026") if r == 1 else Q(".95")
    return mesh_bound - h*h*curvature/8 - factor*unit_hi**r*cost - reserve


def verify(program, first, last, jobs, sample=None):
    if not 2049 <= first <= last <= min(300000, first+first//100):
        raise ValueError("expected one length group within 2049..300000")
    scale = isqrt((2*first)**3)
    period = 1 << (5*(scale+1)-1).bit_length()
    if 5*(isqrt((2*last)**3)+1) > period:
        raise ValueError("the group crosses a grid period boundary")
    stop = ceil(Q(204800*period, 628*scale))
    if stop >= MESH//2:
        raise ValueError("mesh Nyquist cutoff exceeded")
    if sample is not None:
        mode, path = sample
        mode = int(mode)
        if not 1 <= mode <= stop:
            raise ValueError(f"sample mode must be in 1..{stop}")
        inv_survival = [Q(4**n, comb(2*n, n)) for n in range(first, last+1)]
        endpoint_values(mode, program, first, last, period, inv_survival, Path(path))
        return
    rows, costs = collect(program, first, last, period, stop, jobs)
    table, phase_error = phase_table()
    for window in WINDOWS:
        r = window[0]
        margin = min(window_margin(row, costs[parity][r-1], table, phase_error, period, scale, window)
                     for parity, endpoints in enumerate(rows) for row in endpoints)
        if margin <= 0:
            raise ArithmeticError(f"failed sign on {window[1:3]}, margin {float(margin):.8g}")
        # Positive, rounded down, including every error reserve.
        print(f"Order {r}, x in [{window[1]}, {window[2]}], lower margin {margin*10**6//1}/1000000")
    print(f"Verified {first}..{last}, both parities, all {stop} retained modes, Q={period}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("program", help="compiled verify_fourier_window executable")
    parser.add_argument("first", type=int)
    parser.add_argument("last", type=int)
    parser.add_argument("--jobs", type=int, default=1, help="number of concurrent frequency checks")
    parser.add_argument("--lean-sample", nargs=2, metavar=("MODE", "FILE"),
                        help="export one frequency with a Lean proof of the length interpolation bound")
    opts = parser.parse_args()
    if opts.jobs < 1:
        parser.error("--jobs must be positive")
    verify(opts.program, opts.first, opts.last, opts.jobs, opts.lean_sample)
