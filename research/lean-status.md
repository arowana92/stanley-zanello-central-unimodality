# Lean verification status

**Partial formalization.** Lean proves weak unimodality for both central staircase families for every row count through 63. The full conjecture is stated as `CentralUnimodality.Conjecture34`. Its universal proof is still in progress. The [computer-assisted research proof](../proof.md) gives the intended argument for the remaining sizes.

## What the kernel checks

| Theorem | Scope |
| --- | --- |
| `mem_containedPartitions`, `conjecture34_iff_staircase` | The counted objects are exactly the lists of distinct decreasing positive parts that satisfy the row bounds of the two given staircases. The empty list is included. The rank is the sum of the parts. [Statement](../CentralUnimodality/Statement.lean) |
| `rankCountLength_step`, `rankCountLength_succ` | The ballot recurrence counts these partitions at every length, number of parts and rank. The two predecessor classes are disjoint because exactly one class has smallest part one. [Rank counts](../CentralUnimodality/Ranks.lean) |
| `packedRow_digit` | Evaluating the rank polynomial at a power of two places each coefficient in its own digit when the bit width exceeds the ballot length. The cardinality bound rules out carries. [Digit proof](../CentralUnimodality/Packing.lean) · [Packed recurrence](../CentralUnimodality/PackedRows.lean) |
| `central_through_63` | All ranks in all 126 positive-size shapes through 63 rows satisfy weak unimodality. Lean's kernel evaluates the integer verifier. [Finite check and its soundness](../CentralUnimodality/Finite.lean) · [Base theorem](../CentralUnimodality/BaseCases.lean) |
| `unimodalOn_of_curvature`, `UnimodalOn.extend`, `unimodalOn_reverse_iff` | First-difference signs on the flanks and second-difference signs across the peak imply unimodality. Monotone adjacent intervals can be attached, and reversing the row preserves the conclusion. [Order lemmas](../CentralUnimodality/Unimodality.lean) |

The kernel-checked base theorem uses only arithmetic on natural numbers. In the formal proof every positive row with ballot length at most 127 is evaluated at base $2^{128}$. Reading its digits from low to high tests every adjacent pair through the degree of the shape. No externally computed coefficients or proposed peak ranks enter the theorem.

## Remaining proof obligations

The induction beyond 63 rows requires the moment inequalities on smaller odd-part rows and the ordinary Dyck interval bound. Its finite central and flank estimates cover sizes through 299,999. Its uniform analytic estimate applies at every larger size. These estimates still need Lean proofs linked to the rank counts. The Python and C++ verifiers and the bounds justifying them are documented in the [research proof](../proof.md).

## Reproduction

Use the pinned Lean 4.36.0 toolchain and mathlib revision in the Lake manifest. From the repository root run

~~~sh
lake build
lake env lean research/CheckLean.lean
LEAN_NUM_THREADS=1 lake env leanchecker --verbose --fresh CentralUnimodality
~~~

The audit checks the types of the finite theorem and the strict-partition characterization. It checks the transitive dependencies of every project declaration against the same axiom allowlist used in the 321-avoiding superpatterns repository, consisting of `propext`, `Classical.choice` and `Quot.sound`. The fresh replay checks the imported declarations and the project modules from an empty kernel environment.
