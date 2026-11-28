module

public import CentralUnimodality.DirectLatticeResidual
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Derivatives of the split at fixed time and their local product
bounds. At order two the signed combination supplies the correction. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Set

noncomputable def splitPair (A B : ℝ → ℝ) (v x : ℝ) := A (v*x)*B (v*(1-x))

noncomputable def splitJet (r : ℕ) (A B : ℝ → ℝ) (v x : ℝ) :=
  ∑ i ∈ Finset.range (r+1), (r.choose i:ℝ)*(-1)^(r-i)*iteratedDeriv i A (v*x)*iteratedDeriv (r-i) B (v*(1-x))

noncomputable def splitJetBound (r : ℕ) (A B : ℝ → ℝ) (v x : ℝ) :=
  ∑ i ∈ Finset.range (r+1), (r.choose i:ℝ)*|iteratedDeriv i A (v*x)| *|iteratedDeriv (r-i) B (v*(1-x))|

theorem splitPair_smooth {r : ℕ} {A B : ℝ → ℝ} (ha : ContDiff ℝ r A) (hb : ContDiff ℝ r B)
    (v : ℝ) : ContDiff ℝ r (splitPair A B v) :=
  (ha.comp (contDiff_const.mul contDiff_id)).mul (hb.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))

theorem splitPair_derivative {r : ℕ} {A B : ℝ → ℝ} (ha : ContDiff ℝ r A) (hb : ContDiff ℝ r B)
    (v x : ℝ) : iteratedDeriv r (splitPair A B v) x=v^r*splitJet r A B v x := by
  let L := fun x => A (v*x)
  let T := fun x => B (v*x)
  let R := fun x => T (1-x)
  have hl : ContDiff ℝ r L := ha.comp (contDiff_const.mul contDiff_id)
  have ht : ContDiff ℝ r T := hb.comp (contDiff_const.mul contDiff_id)
  have hr : ContDiff ℝ r R := ht.comp (contDiff_const.sub contDiff_id)
  change iteratedDeriv r (L*R) x=_
  rw [iteratedDeriv_mul hl.contDiffAt hr.contDiffAt,splitJet,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have il : i≤r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have left := congrFun (iteratedDeriv_comp_const_mul (ha.of_le (by exact_mod_cast il)) v) x
  have right := congrFun (iteratedDeriv_comp_const_mul (hb.of_le (by exact_mod_cast Nat.sub_le r i)) v) (1-x)
  dsimp only [L,R]
  simp only [left,iteratedDeriv_comp_const_sub,show iteratedDeriv (r-i) T (1-x)=_ from right,smul_eq_mul]
  rw [show v^r=v^i*v^(r-i) by rw [← pow_add,Nat.add_sub_of_le il]]; ring

theorem splitJet_abs (r : ℕ) (A B : ℝ → ℝ) (v x : ℝ) :
    |splitJet r A B v x|≤splitJetBound r A B v x := by
  unfold splitJet splitJetBound
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro i _
  simp only [abs_mul,abs_pow,Nat.abs_cast,abs_neg,abs_one,one_pow,mul_one,le_refl]

theorem splitPair_derivative_bound {r : ℕ} {A B : ℝ → ℝ} (ha : ContDiff ℝ r A) (hb : ContDiff ℝ r B)
    {v : ℝ} (hv : 0≤v) (x : ℝ) :
    |iteratedDeriv r (splitPair A B v) x|≤v^r*splitJetBound r A B v x := by
  rw [splitPair_derivative ha hb,abs_mul,abs_of_nonneg (pow_nonneg hv r)]
  exact mul_le_mul_of_nonneg_left (splitJet_abs ..) (pow_nonneg hv r)

theorem splitJet_two (A B : ℝ → ℝ) (v x : ℝ) :
    splitJet 2 A B v x=iteratedDeriv 2 A (v*x)*B (v*(1-x))-
      2*deriv A (v*x)*deriv B (v*(1-x))+A (v*x)*iteratedDeriv 2 B (v*(1-x)) := by
  norm_num [splitJet,Finset.sum_range_succ,Nat.choose]; ring

end CentralUnimodality.ReturnSplit
