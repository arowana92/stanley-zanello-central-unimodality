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
