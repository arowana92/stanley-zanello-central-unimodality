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
| `ballotEquiv`, `signed_ranks` | Nonnegative ballot words correspond bijectively to the literal partitions. For any test function of the integer signed area, the no-return sum is exactly its two reflected values summed against the rank counts. [Ballot bijection](../CentralUnimodality/Ballot.lean) · [Area identity](../CentralUnimodality/WalkArea.lean) · [Signed rank formula](../CentralUnimodality/SignedRanks.lean) |
| `lastReturn_convolution` | Splitting the unrestricted walk at its last zero gives the exact product convolution for every additive area character and every length. [Last-return decomposition](../CentralUnimodality/LastReturn.lean) |
| `firstReturn_renewal`, `firstReturn_kraft` | Positive-length bridge transforms split at their first return. The exact first-return probabilities through any horizon sum to at most one, by counting disjoint extensions of first-return words. [First-return proof](../CentralUnimodality/FirstReturn.lean) |
| `reflected_of_negative_sum` | In every unimodal row, a negative weighted moment and the specified inequalities on its primitive force a reflected coefficient comparison. The proof sums over all integer superlevels. [Moment test](../CentralUnimodality/MomentTest.lean) |
| `fourier_signed_ranks`, `fourier_free_product` | At any real frequency, the fair signed-area transform is the exact shifted cosine sum against the staircase rank counts. The unrestricted transform is a product of cosines. [Fourier inputs](../CentralUnimodality/FourierInputs.lean) |
| `walkSeries_bridge_inverse`, `fairSeries_residual_bound` | The first-return series gives the exact bridge inverse. For any proposed no-return series and any length, a complex residual bounded by $e$ through that length implies error at most $2e$. [Formal inverse](../CentralUnimodality/ReturnInverse.lean) · [Error estimate](../CentralUnimodality/FourierResidual.lean) |
| `sum_rankCount`, `survival_even`, `survival_odd`, `firstReturn_probability` | The total staircase count is the middle binomial coefficient. Survival at lengths $2n$ and $2n+1$ is $r_n=4^{-n}\binom{2n}{n}$. The first-return mass at $2n$ is $r_n/(2n-1)$ for positive $n$. Lean also checks $1/(4n)\le r_n^2\le 1/(n+1)$. [Ballot count](../CentralUnimodality/Survival.lean) · [First returns](../CentralUnimodality/FirstReturnMass.lean) · [Probability bounds](../CentralUnimodality/SurvivalBounds.lean) |
| `ballot_rank_polynomial`, `odd_ballot_convolution`, `dyck_convolution`, `stump_convolution` | The corank generating polynomial of either staircase is the ballot area polynomial. Cutting at the last zero gives the odd-length recurrence. Removing the final down-step gives Carlitz–Riordan, and eliminating the odd-length series yields Stump’s type B area recurrence for the odd-part staircase. [Coranks](../CentralUnimodality/Corank.lean) · [Last zero](../CentralUnimodality/BallotCut.lean) · [Ordinary Dyck recurrence](../CentralUnimodality/DyckRecurrence.lean) · [Stump recurrence](../CentralUnimodality/Stump.lean) |

The kernel-checked base theorem uses only arithmetic on natural numbers. In the formal proof every positive row with ballot length at most 127 is evaluated at base $2^{128}$. Reading its digits from low to high tests every adjacent pair through the degree of the shape. No externally computed coefficients or proposed peak ranks enter the theorem.

## Remaining proof obligations

The two concrete polynomial witnesses still require formal bounds on their antiderivatives and expectations. The induction beyond 63 rows also uses the ordinary Dyck interval bound. Its finite central and flank estimates cover sizes through 299,999. Its uniform analytic estimate applies at every larger size. These estimates still need Lean proofs linked to the rank counts. The Python and C++ verifiers and the bounds justifying them are documented in the [research proof](../proof.md).

## Reproduction

Use the pinned Lean 4.36.0 toolchain and mathlib revision in the Lake manifest. From the repository root run

~~~sh
lake build
lake env lean research/CheckLean.lean
LEAN_NUM_THREADS=1 lake env leanchecker --verbose --fresh CentralUnimodality
~~~

The audit checks the types of the finite theorem and the strict-partition characterization. It checks the transitive dependencies of every project declaration against the same axiom allowlist used in the 321-avoiding superpatterns repository, consisting of `propext`, `Classical.choice` and `Quot.sound`. The fresh replay checks the imported declarations and the project modules from an empty kernel environment.
