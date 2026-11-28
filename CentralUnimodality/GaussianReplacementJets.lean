module

public import CentralUnimodality.BridgeCurvatureError
public import CentralUnimodality.PhysicalCorrectionTrial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! Global derivative errors between the bridge Gaussian and its dyadic trial
from the differentiated polynomial ODE, without subdividing the time interval. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit Real Set Finset

def valueJetRow (a : List ℤ) (r : ℕ) := (derivativeRow 0)^[r] a

theorem iterated_value_row (a : List ℤ) (r : ℕ) :
    iteratedDeriv r (value a)=fun t => (-1/128:ℝ)^r*value (valueJetRow a r) t := by
  induction r with
  | zero => simp [valueJetRow]
  | succ r ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    rw [(((value_hasDerivAt (valueJetRow a r) t).const_mul ((-1/128:ℝ)^r))).deriv]
    simp only [valueJetRow,Function.iterate_succ_apply',pow_succ]
    ring

theorem iterated_value_row_bound (a : List ℤ) (r : ℕ) {v : ℝ} (hv : v∈Icc (0:ℝ) 256) :
    |iteratedDeriv r (value a) v|≤(rowBudget (valueJetRow a r):ℝ)/(2*2^120*128^r) := by
  rw [iterated_value_row,abs_mul,abs_pow]
  norm_num only [abs_div,abs_neg,abs_one,abs_of_pos (by norm_num : (0:ℝ)<128)]
  exact (mul_le_mul_of_nonneg_left (value_bound _ hv) (by positivity : 0≤(1/128:ℝ)^r)).trans_eq (by
    rw [div_pow,one_pow]; ring)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem defect_jet_budgets : ∀ r ∈ Finset.range 4,
    rowBudget (valueJetRow bridgeDefectRow r)*10^18≤2*2^120*128^r := by decide +kernel

private theorem defect_jet_bound {r : ℕ} (hr : r≤3) {v : ℝ} (hv : v∈Icc (0:ℝ) 256) :
    |iteratedDeriv r (value bridgeDefectRow) v|≤1/10^18 := by
  have budget : (rowBudget (valueJetRow bridgeDefectRow r):ℝ)*10^18≤2*2^120*128^r := by
    exact_mod_cast defect_jet_budgets r (mem_range.mpr (by omega))
  apply (iterated_value_row_bound _ _ hv).trans
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [budget]

set_option maxRecDepth 4000 in
theorem bridge_replacement_jets {v : ℝ} (hv : v∈Icc (0:ℝ) 144) (r : ℕ) (hr : r≤4) :
    |iteratedDeriv r (value bridgeCandidate) v-iteratedDeriv r bridgeCurve v|≤
      2/10^22*(1000:ℝ)^r := by
  let B := value bridgeCandidate
  let E := B-bridgeCurve
  let a := fun t : ℝ => t^2/32
  have wide : v∈Icc (0:ℝ) 256 := ⟨hv.1,by linarith only [hv.2]⟩
  have smooth (p : List ℤ) (k : ℕ) : ContDiff ℝ k (value p) := by
    rw [← physical_evaluation]; simpa using (physicalPoly p).contDiff_aeval (𝕜:=ℝ) k
  have hb (k : ℕ) : ContDiff ℝ k bridgeCurve := by unfold bridgeCurve; fun_prop
  have he (k : ℕ) : ContDiff ℝ k E := (smooth _ k).sub (hb k)
  have ha (k : ℕ) : ContDiff ℝ k a := by unfold a; fun_prop
  have ode : deriv E=(fun t => value bridgeDefectRow t/256)-a*E := by
    funext t
    rw [show E=B-bridgeCurve from rfl,deriv_sub (value_hasDerivAt _ t).differentiableAt (bridge_hasDeriv t).differentiableAt]
    simp only [Pi.sub_apply,Pi.mul_apply,bridge_defect_identity,B,(bridge_hasDeriv t).deriv,a]
    ring
  have rate (k : ℕ) (hk : k≤3) : |iteratedDeriv k a v|≤648 := by
    have v0 := hv.1
    unfold a
    rw [iteratedDeriv_div_const,iteratedDeriv_pow,abs_div,abs_of_pos (by norm_num : (0:ℝ)<32),
      abs_of_nonneg (by positivity : 0≤(Nat.descFactorial 2 k:ℝ)*v^(2-k))]
    have hsq := pow_le_pow_left₀ hv.1 hv.2 2
    interval_cases k <;> norm_num [Nat.descFactorial] <;> linarith only [hsq,hv.2]
  have all (k : ℕ) (hk : k≤4) : |iteratedDeriv k E v|≤2/10^22*(1000:ℝ)^k := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      cases k with
      | zero => simpa [E,B] using (gaussian_inputs wide).2.2.1
      | succ k =>
        have kl : k≤3 := by omega
        have hd := (smooth bridgeDefectRow k).div_const (256:ℝ)
        have hp : ContDiff ℝ k (a*E) := (ha k).mul (he k)
        rw [iteratedDeriv_succ',ode,iteratedDeriv_sub (f:=fun t => value bridgeDefectRow t/256) (g:=a*E) hd.contDiffAt hp.contDiffAt,
          iteratedDeriv_div_const,iteratedDeriv_mul (ha k).contDiffAt (he k).contDiffAt]
        apply (abs_sub ..).trans
        rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<256)]
        apply (add_le_add (div_le_div_of_nonneg_right (defect_jet_bound kl wide) (by norm_num)) (Finset.abs_sum_le_sum_abs ..)).trans
        have term (i : ℕ) (hi : i∈range (k+1)) :
            |(k.choose i:ℝ)*iteratedDeriv i a v*iteratedDeriv (k-i) E v|≤
              (k.choose i:ℝ)*648*(2/10^22*1000^(k-i)) := by
          have il : i≤k := by simpa using hi
          rw [abs_mul,abs_mul,Nat.abs_cast]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (rate i (il.trans kl)) (by positivity))
            (ih _ (by omega) (by omega)) (abs_nonneg _) (by positivity)
        apply (add_le_add le_rfl (sum_le_sum term)).trans
        interval_cases k <;> norm_num [sum_range_succ,Nat.choose]
  have H := all r hr
  simpa only [E,B,iteratedDeriv_sub (smooth bridgeCandidate r).contDiffAt (hb r).contDiffAt] using H

end CentralUnimodality.PolynomialTrial
