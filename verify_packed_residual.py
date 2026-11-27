"""Audit length convolutions by exact integer arithmetic on the exported dyadics."""

import argparse
import subprocess
from fractions import Fraction
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
    blocks = [", ".join(map(str, values[i:i+32])) for i in range(0, len(values), 32)]
    return f"def {name} : List ℤ := List.flatten [\n" + ",\n".join(f"  [{b}]" for b in blocks) + "]\n"


def emit_lean(path, last, period, frequency, scale, columns, checks):
    lines = ["import CentralUnimodality.CheckResidual",
             f"/- Exact binary64 arrays for N ≤ {last}, Q = {period}, mode {frequency}. -/",
             "set_option maxRecDepth 30000", "set_option maxHeartbeats 0",
             "open CentralUnimodality.Residual", "namespace FourierSample"]
    for name, values in zip(("bridge", "freeEven", "freeOdd", "candidateEven", "candidateOdd"), columns):
        lines.append(lean_row(name, values))
    for label, (_, _, base, residual) in zip(("Even", "Odd"), checks):
        lines.append(lean_row(f"error{label}", residual))
        bound = max(map(abs, residual))
        lines.extend([
            f"theorem bound{label} : ∀ i < {last+1},",
            f"    |({scale}:ℤ)*(rowPolynomial free{label}).coeff i -",
            f"      (rowPolynomial bridge * rowPolynomial candidate{label}).coeff i| ≤ {bound} := by",
            f"  apply checked_bound (B := {base}) (E := error{label}) (e := {bound})",
            "  · decide +kernel", "  · decide +kernel", f"#print axioms bound{label}"])
    lines.append("end FourierSample")
    path.write_text("\n".join(lines) + "\n")


def check_frequency(program, last, period, frequency, direct=False, lean_path=None):
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
    if lean_path is not None:
        emit_lean(lean_path, last, period, frequency, scale, columns, checks)
    return [(error, index) for error, index, _, _ in checks]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("program", help="compiled verify_fourier_window executable")
    parser.add_argument("last", type=int, help="last strict half-length")
    parser.add_argument("period", type=int, help="spatial Fourier period")
    parser.add_argument("first_mode", type=int)
    parser.add_argument("last_mode", type=int)
    parser.add_argument("--direct", action="store_true", help="also sum every convolution coefficient term by term")
    parser.add_argument("--emit-lean", type=Path, metavar="FILE", help="write a kernel-replayable certificate for one mode")
    args = parser.parse_args()
    if args.emit_lean is not None and args.first_mode != args.last_mode:
        parser.error("--emit-lean requires a single mode")
    if not 1 <= args.first_mode <= args.last_mode:
        parser.error("expected a nonempty interval of positive modes")
    worst = (Fraction(-1), 0, 0, 0)
    for mode in range(args.first_mode, args.last_mode + 1):
        for parity, (error, index) in enumerate(check_frequency(
                args.program, args.last, args.period, mode, args.direct, args.emit_lean)):
            worst = max(worst, (error, mode, parity, index))
    error, mode, parity, index = worst
    print(f"Exact dyadic residual maximum {error} ({float(error):.6g})")
    print(f"Modes {args.first_mode}..{args.last_mode}, lengths 0..{args.last}, both parities")
    print(f"Maximum at mode {mode}, parity {parity}, half-length {index}")


if __name__ == "__main__":
    main()
