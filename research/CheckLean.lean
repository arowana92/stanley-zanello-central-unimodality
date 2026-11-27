import CentralUnimodality
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let permitted : List Name := [``propext, ``Quot.sound, ``Classical.choice]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    if (`CentralUnimodality).isPrefixOf env.header.moduleNames[idx]! then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a => !(permitted.contains a)
      unless extra.isEmpty do
        throwError "{name} depends on unapproved axioms {extra}"
      checked := checked + 1
  if checked == 0 then throwError "no CentralUnimodality declarations found"
  logInfo m!"Audited {checked} project declarations."


open CentralUnimodality

example {n : ℕ} (hn : n ≤ 63) :
    UnimodalOn (rankCount (2*n)) 0 (n*n) ∧
    UnimodalOn (rankCount (2*n+1)) 0 (n*(n+1)) := central_through_63 hn

example (n δ : ℕ) (hδ : δ ≤ 1) (μ : List ℕ) :
    μ ∈ containedPartitions n δ ↔ InsideStaircase n δ μ :=
  mem_containedPartitions hδ μ

#check Conjecture34
#print axioms central_through_63
#print axioms conjecture34_iff_staircase
#print axioms packedRow_digit
#print axioms unimodalOn_of_curvature

example (n δ : ℕ) (hδ : δ ≤ 1) (F : ℤ → ℤ) :
    (∑ w ∈ strictWords (2*n+δ+1), F (walkArea w)) =
      ∑ j ∈ Finset.range (n*(n+δ)+1), rankCount (2*n+δ) j •
        (F (signedAreaAtRank n δ j) + F (-signedAreaAtRank n δ j)) := signed_ranks F n δ hδ

#print axioms lastReturn_convolution
#print axioms reflected_of_negative_sum
#print axioms firstReturn_renewal
#print axioms firstReturn_kraft

example (ω : ℝ) (V : PowerSeries ℂ) (n : ℕ) (e : ℝ)
    (h : ∀ j ≤ n, ‖PowerSeries.coeff j (fairSeries (areaCharacter ω) words -
        fairSeries (areaCharacter ω) bridges * V)‖ ≤ e) :
    ‖PowerSeries.coeff n (fairSeries (areaCharacter ω) strictWords - V)‖ ≤ 2*e :=
  fairSeries_residual_bound _ (areaCharacter_zero ω) (areaCharacter_add ω)
    (fun x => (norm_areaCharacter ω x).le) V n e h

#print axioms fourier_signed_ranks
#print axioms fourier_free_product
#print axioms fairSeries_residual_bound
#print axioms firstReturn_probability
#print axioms survival_sq_lower
#print axioms survival_sq_upper

#print axioms ballot_rank_polynomial
#print axioms dyck_convolution
#print axioms odd_ballot_convolution
#print axioms stump_convolution

example {n : ℕ} (hn : n ≤ 95) :
    UnimodalOn (rankCount (2*n)) 0 (n*n) ∧
    UnimodalOn (rankCount (2*n+1)) 0 (n*(n+1)) := central_through_95 hn

#print axioms reflected_through_191
#print axioms Witness.reflected_from_two_witnesses
#print axioms oddPart_prefix_step
#print axioms evenPart_prefix_step
#print axioms even_momentColumn
#print axioms odd_momentColumn
#print axioms momentColumn_rescale
#print axioms catalanRoot_mul_ballotBase
#print axioms sizeEuler_dyckBase

#print axioms rootPower_coeff
#print axioms MomentBase.eval_divided
#print axioms certify_moment_series
