"""Audit length convolutions by exact integer arithmetic on the exported dyadics."""

import argparse
import subprocess
from fractions import Fraction
from math import isqrt
from pathlib import Path


def pack_signed(values, width):
    """Evaluate the signed coefficient polynomial at B = 256**width."""
    base = 1 << (8 * width)
    low = bytearray()
    correction = bytearray()
    for value in values:
        low.extend((value % base).to_bytes(width, "little"))
        correction.extend(int(value < 0).to_bytes(width, "little"))
    return int.from_bytes(low, "little") - base * int.from_bytes(correction, "little")


def check_convolution(scale, bridge, free, candidate, direct=False):
    length = len(bridge)
    free_max, bridge_max, candidate_max = (max(map(abs, row)) for row in (free, bridge, candidate))
    bound = scale * free_max + length * bridge_max * candidate_max
    largest = max(2 * bound, free_max, bridge_max, candidate_max)
    width = max(1, (largest.bit_length() + 7) // 8)
    base = 1 << (8 * width)
    modulus = 1 << (8 * width * length)
    difference = scale * pack_signed(free, width) - pack_signed(bridge, width) * pack_signed(candidate, width)
    bias = int.from_bytes((base // 2).to_bytes(width, "little") * length, "little")
    encoded = ((difference + bias) % modulus).to_bytes(length * width, "little")
    errors = [int.from_bytes(encoded[i:i+width], "little") - base // 2
              for i in range(0, len(encoded), width)]
    worst = max(range(length), key=lambda i: abs(errors[i]))
    magnitude = abs(errors[worst])
    # These are the coefficient bound and congruence in packed_residual_coefficients.
    if magnitude > bound or bound + magnitude >= base:
        raise ArithmeticError("insufficient room for signed digits")
    if (difference - pack_signed(errors, width)) % modulus:
        raise ArithmeticError("residual congruence failed")
    indices = range(length) if direct else {0, 1, length // 2, length - 1, worst}
    for i in indices:
        actual = scale * free[i] - sum(bridge[k] * candidate[i-k] for k in range(i+1))
        if errors[i] != actual:
            raise ArithmeticError(f"direct convolution disagrees at {i}")
    return Fraction(magnitude, scale * scale), worst, base, errors


def lean_row(name, values):
    # Avoid repeated elaboration of overloaded unary minus on long signed rows.
    literals = [f"Int.negSucc {-value-1}" if value < 0 else str(value) for value in values]
    blocks = [", ".join(literals[i:i+32]) for i in range(0, len(literals), 32)]
    return f"def {name} : List ℤ := List.flatten [\n" + ",\n".join(f"  [{b}]" for b in blocks) + "]\n"


def half_roots(d, interval):
    return min(d, isqrt(d*interval[0]//2)), min(d, isqrt(d*interval[1]//2)+1)


def cosine_offset(d, depth, tick):
    """Enclose d*(1+cos(tick*pi/2**depth)) for 0 <= tick <= 2**depth."""
    if depth == 0:
        return (2*d, 2*d) if tick == 0 else (0, 0)
    half = 1 << (depth-1)
    low, high = half_roots(d, cosine_offset(d, depth-1, min(tick, 2*half-tick)))
    return (d+low, d+high) if tick <= half else (d-high, d-low)


def small_grid_errors(period, frequency, scale, columns, bits=112):
    """Outward integer bounds for both true free inputs and the true bridge."""
    d = 1 << bits
    k = period.bit_length() - 2
    bridge, free_even, free_odd = columns[:3]
    cut = min(len(bridge)-1, (period//(2*frequency)-1)//2)
    if cut < len(bridge)-1 and cut < 200:
        raise ValueError("the paired prefix before the quadrant boundary must have at least 200 pairs")

    cosine = half_roots(d, cosine_offset(d, k, frequency))
    sine = half_roots(d, cosine_offset(d, k, (1 << k)-frequency))

    def mul(a, b):
        return a[0]*b[0]//d, a[1]*b[1]//d+1

    def advance(phase):
        c, s = phase
        cc, ss = mul(c, cosine), mul(s, sine)
        sc, cs = mul(s, cosine), mul(c, sine)
        return ((max(0, cc[0]-ss[1]), max(0, cc[1]-ss[0])),
                (sc[0]+cs[0], sc[1]+cs[1]))

    def error(interval, stored):
        return (max(abs(endpoint*scale-stored*d) for endpoint in interval)+d-1)//d

    one = d, d
    half, odd = (one, (0, 0)), (cosine, sine)
    r, even_free, odd_free = one, one, cosine
    er = ef = 0
    for j, (rv, ev, ov) in enumerate(zip(bridge, free_even, free_odd)):
        if j > cut:
            # quadrant_input_tail bounds each true transform by 2^-57.
            tail = (scale+(1 << 57)-1) >> 57
            er = max(er, abs(rv)+tail)
            ef = max(ef, abs(ev)+tail, abs(ov)+tail)
            continue
        if j:
            half = advance(half)
            numerator = mul(mul(r, half[0]), odd[1])
            lo, hi = half[1]
            if lo == 0:
                raise ArithmeticError("bridge denominator enclosure touches zero")
            r = d*numerator[0]//(2*hi), d*numerator[1]//(2*lo)+1
            even_phase = advance(odd)
            odd = advance(even_phase)
            even_free = mul(odd_free, even_phase[0])
            odd_free = mul(even_free, odd[0])
        er = max(er, error(r, rv))
        ef = max(ef, error(even_free, ev), error(odd_free, ov))
    return d, k, er, ef, cut


def amplitude_proof(last, period, frequency, scale, columns, checks, input_bounds):
    d, k, er, ef, cut = input_bounds
    bases = [item[2] for item in checks]
    e = max(abs(x) for item in checks for x in item[3])
    v = max(abs(x) for col in columns[3:] for x in col)
    root_bound = isqrt(last-1) + 1
    residual = Fraction(ef, scale) + Fraction(e+(last+1)*er*v, scale*scale)
    scaled = 4*root_bound*residual*10**15
    upper = -(-scaled.numerator//scaled.denominator)
    if cut == last:
        input_test = f"SmallGrid.check {d} {k} {frequency} {scale} {er} {ef} (start {d} {k} {frequency})"
        theorem = "input_amplitude"
        angle_checks = "(by omega)"
    else:
        input_test = f"cutCheck {d} {k} {frequency} {cut} {scale} {er} {ef}"
        theorem = f"cut_amplitude (l := {cut})"
        angle_checks = "(by decide) (by decide) (by decide)"
    return [
        "open CentralUnimodality CentralUnimodality.SmallGrid",
        f"theorem inputsChecked : {input_test} bridge freeEven freeOdd = true := by decide +kernel",
        "def candidates := parityRow candidateEven candidateOdd",
        "def errors := parityRow errorEven errorOdd",
        f"def bases (σ : ℕ) : ℤ := if σ=0 then {bases[0]} else {bases[1]}",
        f"theorem sampledAmplitude (n δ : ℕ) (hδ : δ ≤ 1) (h₁ : 1 ≤ n+δ) (hN : n+δ ≤ {last}) :",
        f"    |signedAmplitude n δ (gridFrequency {period} {frequency}) -",
        f"      (PowerSeries.coeff (n+δ) (scaledSeries {scale} (rowPolynomial (candidates (1-δ))))).re /",
        f"        survival (n+δ)| ≤ ({upper}:ℝ)/10^15 := by",
        f"  have h := {theorem} (d := {d}) (k := {k}) (f := {frequency}) (L := {last+1})",
        f"    (n := n) (v := {v}) (e := {e}) (by decide) hδ (by omega) {angle_checks} (by decide)",
        "    bridge freeEven freeOdd candidates errors bases (by decide +kernel) inputsChecked",
        "    (by intro σ hσ; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hσ with rfl|rfl",
        "        · exact residualEven", "        · exact residualOdd)",
        "    (by intro σ hσ; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hσ with rfl|rfl <;> decide +kernel)",
        "    (by intro σ hσ; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hσ with rfl|rfl <;> decide +kernel)",
        f"  apply (uniform_error (M := {root_bound}) h₁ (by omega) (by positivity) h).trans",
        "  norm_num", "#print axioms sampledAmplitude"]


def emit_lean(path, last, period, frequency, scale, columns, checks, input_bounds):
    module = "QuadrantCheck" if input_bounds else "CheckResidual"
    lines = [f"import CentralUnimodality.{module}",
             f"/- Exact binary64 arrays for N ≤ {last}, Q = {period}, mode {frequency}. -/",
             "set_option maxRecDepth 30000", "set_option maxHeartbeats 0",
             "open CentralUnimodality.Residual", "namespace FourierSample"]
    for name, values in zip(("bridge", "freeEven", "freeOdd", "candidateEven", "candidateOdd"), columns):
        lines.append(lean_row(name, values))
    for label, (_, _, base, residual) in zip(("Even", "Odd"), checks):
        lines.append(lean_row(f"error{label}", residual))
        bound = max(map(abs, residual))
        lines.extend([
            f"theorem residual{label} : check {base} {scale} {last+1} free{label} bridge",
            f"    candidate{label} error{label} = true := by decide +kernel",
            f"theorem bound{label} : ∀ i < {last+1},",
            f"    |({scale}:ℤ)*(rowPolynomial free{label}).coeff i -",
            f"      (rowPolynomial bridge * rowPolynomial candidate{label}).coeff i| ≤ {bound} := by",
            f"  apply checked_bound (B := {base}) (E := error{label}) (e := {bound})",
            f"  · exact residual{label}", "  · decide +kernel", f"#print axioms bound{label}"])
    if input_bounds:
        lines.extend(amplitude_proof(last, period, frequency, scale, columns, checks, input_bounds))
    lines.append("end FourierSample")
    path.write_text("\n".join(lines) + "\n")


def check_frequency(program, last, period, frequency, direct=False, lean_path=None, prove_inputs=False):
    data = subprocess.check_output([program, "--residual-inputs", str(last), str(period), str(frequency)])
    rows = [[float.fromhex(token.decode()).as_integer_ratio() for token in line.split()]
            for line in data.splitlines()]
    if len(rows) != last + 1 or any(len(row) != 5 for row in rows):
        raise ValueError("incomplete dyadic sample")
    scale = max(denominator for row in rows for _, denominator in row)
    columns = [[num * (scale // den) for num, den in column] for column in zip(*rows)]
    bridge, free_even, free_odd, candidate_even, candidate_odd = columns
    checks = [check_convolution(scale, bridge, f, v, direct)
              for f, v in [(free_even, candidate_even), (free_odd, candidate_odd)]]
    input_bounds = small_grid_errors(period, frequency, scale, columns) if prove_inputs else None
    if lean_path is not None:
        emit_lean(lean_path, last, period, frequency, scale, columns, checks, input_bounds)
    errors = [(error, index) for error, index, _, _ in checks]
    if input_bounds is None:
        return errors, None, (scale, columns[3:])
    er, ef = input_bounds[2:4]
    v = max(abs(x) for col in columns[3:] for x in col)
    u = Fraction(ef, scale) + max(error for error, _ in errors) + Fraction((last+1)*er*v, scale**2)
    return errors, (Fraction(er, scale), Fraction(ef, scale), 4*(isqrt(last-1)+1)*u), (scale, columns[3:])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("program", help="compiled verify_fourier_window executable")
    parser.add_argument("last", type=int, help="last strict half-length")
    parser.add_argument("period", type=int, help="spatial Fourier period")
    parser.add_argument("first_mode", type=int)
    parser.add_argument("last_mode", type=int)
    parser.add_argument("--direct", action="store_true", help="also sum every convolution coefficient term by term")
    parser.add_argument("--emit-lean", type=Path, metavar="FILE", help="write a kernel-replayable certificate for one mode")
    parser.add_argument("--prove-inputs", action="store_true", help="also enclose true walk inputs and conditional amplitudes, and include the proof when emitting Lean")
    args = parser.parse_args()
    if args.emit_lean is not None and args.first_mode != args.last_mode:
        parser.error("--emit-lean requires a single mode")
    if not 1 <= args.first_mode <= args.last_mode:
        parser.error("expected a nonempty interval of positive modes")
    worst = (Fraction(-1), 0, 0, 0)
    input_worst = [(Fraction(-1), 0)] * 3
    for mode in range(args.first_mode, args.last_mode + 1):
        errors, input_errors, _ = check_frequency(args.program, args.last, args.period, mode,
                                                 args.direct, args.emit_lean, args.prove_inputs)
        for parity, (error, index) in enumerate(errors):
            worst = max(worst, (error, mode, parity, index))
        if input_errors:
            input_worst = [max(old, (new, mode)) for old, new in zip(input_worst, input_errors)]
    error, mode, parity, index = worst
    print(f"Exact dyadic residual maximum {error} ({float(error):.6g})")
    print(f"Modes {args.first_mode}..{args.last_mode}, lengths 0..{args.last}, both parities")
    print(f"Maximum at mode {mode}, parity {parity}, half-length {index}")
    if args.prove_inputs:
        for label, (bound, mode) in zip(("bridge input", "free input", "conditional amplitude"), input_worst):
            print(f"Maximum {label} error bound {bound} ({float(bound):.6g}) at mode {mode}")


if __name__ == "__main__":
    main()
