module

public import CentralUnimodality.GaussianReplacementJets
public import CentralUnimodality.QuadraticLatticeResidual
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! Uniform errors in the three Gaussian multipliers that enter the signed
quadratic residual, using positive polynomial majorants up to time 144. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Set ReturnSplit Finset

private theorem second_abs {a b c d : ℝ} (lo : 0≤a) (lb : 0≤b) (ha : a≤c) (hb : b≤d) :
    |a^2/2-b|≤c^2/2+d := by
  apply (abs_sub ..).trans
  rw [abs_of_nonneg (by positivity : 0≤a^2/2),abs_of_nonneg lb]
  linarith only [pow_le_pow_left₀ lo ha 2,hb]

theorem free_second_replacement {σ : ℕ} (hs : σ≤1) {v : ℝ} (hv : v∈Icc (0:ℝ) 144) :
    |value freeCandidate v*(freeLogCorrection σ v^2/2-freeSecondLog σ v)-freeSecond σ v|≤12/10^8 := by
  have wide : v∈Icc (0:ℝ) 256 := ⟨hv.1,by linarith only [hv.2]⟩
  have v0 := hv.1
  have c (k : ℕ) := pow_le_pow_left₀ v0 hv.2 k
  have A : freeLogCorrection σ v≤33000000 := by
    interval_cases σ <;> norm_num [freeLogCorrection] <;> linarith only [c 2,c 5]
  have B : freeSecondLog σ v≤10^12 := by
    interval_cases σ <;> norm_num [freeSecondLog] <;> linarith only [hv.2,c 4,c 7]
  have h := second_abs (by unfold freeLogCorrection; positivity) (by unfold freeSecondLog; positivity) A B
  rw [freeSecond,← sub_mul,abs_mul]
  exact (mul_le_mul (gaussian_inputs wide).1 h (abs_nonneg _) (by norm_num)).trans (by norm_num)

theorem bridge_second_replacement {v : ℝ} (hv : v∈Icc (0:ℝ) 144) :
    |value bridgeCandidate v*(bridgeLogCorrection v^2/2-bridgeSecondLog v)-bridgeSecond v|≤6/10^10 := by
  have wide : v∈Icc (0:ℝ) 256 := ⟨hv.1,by linarith only [hv.2]⟩
  have v0 := hv.1
  have c (k : ℕ) := pow_le_pow_left₀ v0 hv.2 k
  have A : bridgeLogCorrection v≤2100000 := by unfold bridgeLogCorrection; linarith only [c 2,c 5]
  have B : bridgeSecondLog v≤10^9 := by unfold bridgeSecondLog; linarith only [c 4,c 7]
  have h := second_abs (by unfold bridgeLogCorrection; positivity) (by unfold bridgeSecondLog; positivity) A B
  rw [bridgeSecond,← sub_mul,abs_mul]
  exact (mul_le_mul (gaussian_inputs wide).2.2.1 h (abs_nonneg _) (by norm_num)).trans (by norm_num)

private theorem log_jet_cap {v : ℝ} (hv : v∈Icc (0:ℝ) 144) {r : ℕ} (hr : r≤2) :
    |iteratedDeriv r bridgeLogCorrection v|≤2100000 := by
  have v0 := hv.1
  have c (k : ℕ) := pow_le_pow_left₀ v0 hv.2 k
  let f := fun t : ℝ => t^2/192
  let g := fun t : ℝ => t^5/30720
  have hf : ContDiff ℝ r f := by unfold f; fun_prop
  have hg : ContDiff ℝ r g := by unfold g; fun_prop
  change |iteratedDeriv r (f+g) v|≤_
  rw [iteratedDeriv_add hf.contDiffAt hg.contDiffAt]
  dsimp only [f,g]
  rw [iteratedDeriv_div_const,iteratedDeriv_div_const,iteratedDeriv_pow,iteratedDeriv_pow,
    abs_of_nonneg (by positivity)]
  interval_cases r <;> norm_num [Nat.descFactorial] <;> linarith only [c 2,c 5,c 1,c 4,c 3]

theorem bridge_first_replacement_jets {v : ℝ} (hv : v∈Icc (0:ℝ) 144) (r : ℕ) (hr : r≤2) :
    |iteratedDeriv r ((fun t => -value bridgeCandidate t*bridgeLogCorrection t)-bridgeFirst) v|≤
      5/10^16*(1000:ℝ)^r := by
  let E := value bridgeCandidate-bridgeCurve
  have pb : ContDiff ℝ r (value bridgeCandidate) := by
    rw [← physical_evaluation]; simpa using (physicalPoly bridgeCandidate).contDiff_aeval (𝕜:=ℝ) r
  have bb : ContDiff ℝ r bridgeCurve := by unfold bridgeCurve; fun_prop
  have a : ContDiff ℝ r bridgeLogCorrection := by unfold bridgeLogCorrection; fun_prop
  have e : ContDiff ℝ r E := pb.sub bb
  have f : ((fun t => -value bridgeCandidate t*bridgeLogCorrection t)-bridgeFirst)= -(bridgeLogCorrection*E) := by
    funext t; simp [E,bridgeFirst]; ring
  rw [f,iteratedDeriv_neg,abs_neg,iteratedDeriv_mul a.contDiffAt e.contDiffAt]
  apply (abs_sum_le_sum_abs ..).trans
  have term (i : ℕ) (hi : i∈range (r+1)) :
      |(r.choose i:ℝ)*iteratedDeriv i bridgeLogCorrection v*iteratedDeriv (r-i) E v|≤
        (r.choose i:ℝ)*2100000*(2/10^22*1000^(r-i)) := by
    have il : i≤r := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have lo := Nat.sub_le r i
    have be := bridge_replacement_jets hv (r-i) (by omega)
    have ee : |iteratedDeriv (r-i) E v|≤2/10^22*1000^(r-i) := by
      dsimp only [E]
      rw [iteratedDeriv_sub (pb.of_le (by exact_mod_cast lo)).contDiffAt (bb.of_le (by exact_mod_cast lo)).contDiffAt]
      exact be
    rw [abs_mul,abs_mul,Nat.abs_cast]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (log_jet_cap hv (il.trans hr)) (by positivity))
      ee (abs_nonneg _) (by positivity)
  apply (sum_le_sum term).trans
  interval_cases r <;> norm_num [sum_range_succ,Nat.choose]

end CentralUnimodality.PolynomialTrial
