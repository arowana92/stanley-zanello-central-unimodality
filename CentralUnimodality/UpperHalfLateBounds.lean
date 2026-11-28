module

public import CentralUnimodality.UpperHalfPrefixScales
public import CentralUnimodality.LateUniformBudget
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The final cut under an unshifted upper-half tilt. Above a fixed
one-step drift the total event probability suffices even at a single rank. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real BinArithmetic

@[simp] theorem rankChange_zero (c j : ℝ) (m : ℕ) : rankChange c 0 j m=1 := by
  simp [rankChange,(rankNormalizer_pos c m).ne']

theorem eventSiteMass_bounds (c : ℝ) (m : ℕ) (A : Finset (List Bool)) (k : ℤ) :
    0 ≤ eventSiteMass c m A k ∧ eventSiteMass c m A k ≤ ∑ w ∈ A, signMass c (c*m) w := by
  unfold eventSiteMass
  exact ⟨Finset.sum_nonneg fun w _ => by split_ifs <;> first | exact (signMass_pos ..).le | rfl,
    Finset.sum_le_sum fun w _ => by split_ifs <;> first | rfl | exact (signMass_pos ..).le⟩

theorem far_late_height {m T : ℕ} {u : ℝ} (hm : 0<(m:ℝ)) (hT : T≤m)
    (hcut : 15/16*(m:ℝ) ≤ T) (hd : 0 ≤ tanh u) :
    (15/32*tanh u)*m ≤ (tanh u/m)*prefixLabels m T := by
  have ht : (T:ℝ) ≤ m := by exact_mod_cast hT
  have H : (15/32)*(m:ℝ)^2 ≤ prefixLabels m T := by
    unfold prefixLabels
    have h₁ := mul_le_mul_of_nonneg_right (sub_nonneg.mpr ht) (Nat.cast_nonneg (α:=ℝ) T)
    nlinarith only [h₁,mul_le_mul_of_nonneg_right hcut hm.le,Nat.cast_nonneg (α:=ℝ) T]
  have HH := mul_le_mul_of_nonneg_left H hd
  rw [show tanh u/m*prefixLabels m T=tanh u*prefixLabels m T/m by ring,le_div_iff₀ hm]
  linarith only [HH]

private theorem high_decay {M : ℝ} (hM : 4096 ≤ M) : M^3*exp (-(M/100)) ≤ 1/1000 := by
  have hp : 0 ≤ M/4000 := by linarith
  have H := mul_le_mul (by linarith only [exp_one_gt_d9] : (8/3:ℝ) ≤ exp 1)
    (show M/4000 ≤ exp (M/4000-1) by linarith only [add_one_le_exp (M/4000-1)]) hp (exp_pos _).le
  rw [← exp_add,show 1+(M/4000-1)=M/4000 by ring] at H
  have hh := pow_le_pow_left₀ (by linarith only [hp] : 0 ≤ M/1500) (by linarith only [H] : M/1500 ≤ exp (M/4000)) 40
  rw [← exp_nat_mul] at hh
  have hlarge := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4096) hM 37)
    (pow_nonneg (by linarith only [hM] : 0≤M) 3)
  have hpoly : M^3 ≤ 1/1000*(M/1500)^40 := by
    norm_num at hlarge; nlinarith only [hlarge,pow_nonneg (by linarith only [hM] : 0 ≤ M) 3]
  rw [exp_neg,← div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
  apply hpoly.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact hh.trans_eq (by norm_num; ring_nf)

theorem late_loss_large_tilt {m T : ℕ} (hm : 4096 ≤ m) (hT : T≤m) (hcut : 15/16*(m:ℝ) ≤ T)
    {c σ P : ℝ} (hc : 0 ≤ c) (hlo : 2/5 ≤ c*m) (hhi : c*m ≤ 1)
    (hσ : 0 ≤ σ) (hu : σ ≤ (3/10)*sizeScale m) (hP : tanh (c*m) ≤ P) (k : ℤ) :
    σ/P*signedRank 0 k (eventSiteMass c m (lateHitEvent m T)) ≤ 1/1000 ∧
    σ^2/P*signedRank 1 k (eventSiteMass c m (lateHitEvent m T)) ≤ 1/1000 := by
  let d := tanh (c*m)
  let b := 15/32*d
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0<(m:ℝ) := by linarith
  have hd := upper_half_drift (mul_nonneg hc hp.le) hhi
  have hd' : 3/10 ≤ d := by dsimp [d]; linarith only [hd,hlo]
  have hd₀ : 0≤d := by linarith only [hd']
  have hb : 57/400 ≤ b := by dsimp only [b,d]; linarith only [hd,hlo]
  have hPp : 0<P := by change d ≤ P at hP; linarith only [hd',hP]
  have HE := late_hit_change_bound (by omega : 0<m) hT hc (by norm_num : (0:ℝ)≤0)
    (by linarith only [hb] : 0 ≤ b) (by simpa only [add_zero] using far_late_height hp hT hcut hd₀)
  simp [rankChange_zero] at HE
  have hb2 : 1/50 ≤ b^2 := by linarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤57/400) hb 2]
  have hdec : lateHitMass c m T ≤ exp (-((m:ℝ)/100)) :=
    HE.trans (exp_le_exp.mpr (by linarith only [mul_le_mul_of_nonneg_left hb2 hp.le]))
  let A := eventSiteMass c m (lateHitEvent m T)
  have bound (j : ℤ) : A j ≤ exp (-((m:ℝ)/100)) := by
    have H := (eventSiteMass_bounds c m (lateHitEvent m T) j).2
    rw [late_event_probability] at H; exact H.trans hdec
  have mass : signedRank 0 k A ≤ exp (-((m:ℝ)/100)) := bound k
  have diff : signedRank 1 k A ≤ exp (-((m:ℝ)/100)) := by
    change A (k+1)-A k ≤ _; linarith only [bound (k+1),(eventSiteMass_bounds c m (lateHitEvent m T) k).1]
  have hs2 : (sizeScale m)^2=(m:ℝ)^3 := by dsimp [sizeScale]; rw [mul_pow,sq_sqrt hp.le]; ring
  have hσsq := pow_le_pow_left₀ hσ hu 2
  rw [mul_pow,hs2] at hσsq
  have hP' : 3/10 ≤ P := hd'.trans hP
  have hs₀ : 1 ≤ sizeScale m := by
    have hr : 1 ≤ √(m:ℝ) := (le_sqrt (by norm_num) hp.le).mpr (by linarith only [hM])
    dsimp only [sizeScale]; nlinarith only [mul_le_mul_of_nonneg_left hr hp.le,hM]
  have hr : sizeScale m ≤ (m:ℝ)^3 := by nlinarith only [hs2,mul_nonneg (sub_nonneg.mpr hs₀) (hs₀.trans' zero_le_one)]
  have divbound {x : ℝ} (hx : x ≤ (3/10)*(m:ℝ)^3) : x/P ≤ (m:ℝ)^3 := by
    apply (div_le_iff₀ hPp).mpr; linarith only [hx,mul_le_mul_of_nonneg_right hP' (pow_nonneg hp.le 3)]
  have bound₀ := divbound (by linarith only [hu,hr] : σ ≤ (3/10)*(m:ℝ)^3)
  have bound₁ := divbound (by linarith only [hσsq,pow_nonneg hp.le 3] : σ^2 ≤ (3/10)*(m:ℝ)^3)
  exact ⟨((mul_le_mul_of_nonneg_left mass (div_nonneg hσ hPp.le)).trans
      (mul_le_mul_of_nonneg_right bound₀ (exp_pos _).le)).trans (high_decay hM),
    ((mul_le_mul_of_nonneg_left diff (by positivity : 0 ≤ σ^2/P)).trans
      (mul_le_mul_of_nonneg_right bound₁ (exp_pos _).le)).trans (high_decay hM)⟩

end CentralUnimodality.MarkedExcursion
