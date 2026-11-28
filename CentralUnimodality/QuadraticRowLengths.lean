module

public import CentralUnimodality.SecondResidualRows

/-! Calculate the sizes in the quadratic evaluator from list lengths alone.
The bound for dyadic rounding counts the sixteen zero slots above degree 1014. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

private theorem linear_length (s t : ℤ) (a b : List ℤ) :
    (linearRows s t a b).length=max a.length b.length := by
  induction a generalizing b with
  | nil => simp [linearRows]
  | cons c a ih =>
    cases b with
    | nil => simp [linearRows]
    | cons d b => simp [linearRows,ih,Nat.succ_max_succ]

private theorem degree_length (j : ℕ) (a : List ℤ) : (degreeWeight j a).length=a.length := by
  induction a generalizing j with
  | nil => rfl
  | cons c a ih => simp [degreeWeight,ih]

private theorem diff_length (r : ℕ) (a : List ℤ) : (powerDerivative^[r] a).length=a.length-r := by
  induction r with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply',powerDerivative,degree_length,ih,Nat.sub_sub]

private theorem weight_length (f : ℕ → ℕ) (a : List ℤ) (j t : ℕ) : (weightList f a j t).length=a.length := by
  induction a generalizing j t with
  | nil => rfl
  | cons c a ih => simp [weightList,ih]

private theorem divided_length (d : ℕ) (a : List ℤ) (j t : ℕ) : (divideWeights d a j t).length=a.length := by
  induction a generalizing j t with
  | nil => rfl
  | cons c a ih => simp [divideWeights,ih]

private theorem beta_length (a b : List ℤ) : (betaDense a b).2.length=a.length+b.length-1 := by
  simp only [betaDense,divided_length,packedDenseProduct_length,halfWeighted,weight_length]

namespace RationalPolyRow

private theorem physical_length (a : List ℤ) : (physicalNumer a).length=a.length := by
  induction a with
  | nil => rfl
  | cons c a ih => simp [physicalNumer,ih]

private theorem operation_lengths (a b : RationalPolyRow) (j : ℕ) (s t : ℤ) (q : ℕ+) :
    (mul a b).numer.length=a.numer.length+b.numer.length-1 ∧
    (beta a b).numer.length=a.numer.length+b.numer.length-1 ∧
    (diff j a).numer.length=a.numer.length-j ∧
    (linear s t a b).numer.length=max a.numer.length b.numer.length ∧
    (shift j a).numer.length=j+a.numer.length ∧
    (scale s q a).numer.length=a.numer.length ∧ (drop j a).numer.length=a.numer.length-j := by
  simp only [mul,packedDenseProduct_length,beta,beta_length,diff,diff_length,linear,linear_length,
    shift,List.length_append,List.length_replicate,scale,List.length_nil,Nat.max_zero,drop,List.length_drop]
  trivial

end RationalPolyRow
open RationalPolyRow

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
theorem quadratic_residual_length {σ : ℕ} (hs : σ≤1) : (quadraticResidualRow σ).numer.length=1031 := by
  have m (a b : RationalPolyRow) := (operation_lengths a b 0 0 0 1).1
  have be (a b : RationalPolyRow) := (operation_lengths a b 0 0 0 1).2.1
  have d (r : ℕ) (a : RationalPolyRow) := (operation_lengths a a r 0 0 1).2.2.1
  have lin (s t : ℤ) (a b : RationalPolyRow) := (operation_lengths a b 0 s t 1).2.2.2.1
  have sh (r : ℕ) (a : RationalPolyRow) := (operation_lengths a a r 0 0 1).2.2.2.2.1
  have sc (s : ℤ) (q : ℕ+) (a : RationalPolyRow) := (operation_lengths a a 0 s 0 q).2.2.2.2.2.1
  have dr (r : ℕ) (a : RationalPolyRow) := (operation_lengths a a r 0 0 1).2.2.2.2.2.2
  rcases (show σ=0 ∨ σ=1 by omega) with rfl|rfl <;>
    simp only [quadraticResidualRow,fromTrials,RationalPolyRow.residual,secondMultiplierRow,bridgeLogSecondRow,freeLogSecondRow,
      bridgeLogRow,freeLogRow,halfDriftRow,splitFirst,splitSecond,weightedJetRow,sumRows,weighted,
      m,be,d,lin,sh,sc,dr,physicalRow,physical_length,term,zero,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil] <;> decide +kernel

end CentralUnimodality.PolynomialTrial
