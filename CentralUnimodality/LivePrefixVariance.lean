module

public import CentralUnimodality.ConditionalRankVariance
public import CentralUnimodality.RankBinSetup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Keep the finite survival probability in the stopped second-moment
estimate. This lets the corrected survival denominator improve the
conditional variance used on the central side of the signed test. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real BinArithmetic

private theorem live_telescope (f : ℕ→ℝ) (L : ℕ) :
    f L*L+∑ t∈Finset.range L, ((t:ℝ)+1)*(f t-f (t+1))=∑ t∈Finset.range L,f t := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,← ih,Nat.cast_succ]; ring

theorem prefix_occupation_bound (c u : ℝ) {m L : ℕ} (hL : L≤m) :
    (∑ w∈ballots L, signMass c u w*(centeredRank c u m w)^2) ≤
      (m:ℝ)^2/4*∑ t∈Finset.range L, live c u t 1 := by
  let A := (m:ℝ)^2/4
  let H (t : ℕ) := ∑ w∈hitWords 1 (t+1), signMass c u w
  have h₁ := mul_le_mul_of_nonneg_left (prefixVariance_le hL c u) (live_nonneg c u L 1)
  have h₂ (t) (ht : t∈Finset.range L) : prefixVariance c u m (t+1)*H t ≤ A*(((t:ℝ)+1)*H t) := by
    have K := mul_le_mul_of_nonneg_right (prefixVariance_le ((Finset.mem_range.mp ht).trans_le hL) c u)
      (show 0≤H t from Finset.sum_nonneg (fun _ _ => (signMass_pos ..).le))
    push_cast at K; dsimp only [A]; linarith only [K]
  have S := Finset.sum_le_sum h₂
  rw [← Finset.mul_sum] at S
  have E := stopped_variance_bound c u m L
  change _≤live c u L 1*prefixVariance c u m L+∑ t∈Finset.range L,prefixVariance c u m (t+1)*H t at E
  have hhit (t) : H t=live c u t 1-live c u (t+1) 1 := (prefix_first_hit c u t).symm
  have K := live_telescope (fun t => live c u t 1) L
  simp_rw [← hhit] at K
  rw [← K,mul_add]
  dsimp only [A] at S
  linarith only [E,S,h₁]

theorem prefix_occupation_drift {m L : ℕ} (hL : L≤m) {c u : ℝ} (hc : 0≤c) (hu : 0<u) :
    (∑ w∈ballots L, signMass c u w*(centeredRank c u m w)^2) ≤
      (m:ℝ)^2/4*(2*u*L+1/tanh u) := by
  have hd : 0<tanh u := by rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr hu) (cosh_pos _)
  have q₁ : exp (-2*u)≤1 := exp_le_one_iff.mpr (by linarith only [hu])
  have q₂ : 1-exp (-2*u)≤2*u := by linarith only [add_one_le_exp (-2*u)]
  have HB (t : ℕ) : live c u t 1≤2*u+live 0 (-u) t 1 := by
    apply (live_parameters c u 0 u t 1 (fun i _ => by simp; positivity)).trans
    rw [homogeneous_live u t 1,pow_one]
    exact add_le_add q₂ (mul_le_of_le_one_left (live_nonneg ..) q₁)
  have H := Finset.sum_le_sum (s:=Finset.range L) (fun t _ => HB t)
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_comm (L:ℝ)] at H
  have K : ∑ t∈Finset.range L,live 0 (-u) t 1≤1/tanh u := (le_div_iff₀ hd).mpr (by
    simpa only [Nat.cast_one,mul_comm] using negative_drift_lifetime u L 1)
  exact (prefix_occupation_bound c u hL).trans (mul_le_mul_of_nonneg_left
    (H.trans (add_le_add (le_refl _) K)) (by positivity))

theorem normalized_occupation_variance {m L : ℕ} (hm : 0<m) (hL : L≤m) {c u σ z f G κ den : ℝ}
    (hc : 0≤c) (hu : 0<u) (hz : 0<z) (hf : 0≤f) (hκ : 0<κ) (hd : 0<den)
    (hT : (L:ℝ)≤f*m) (hG : 2*u*√m≤G) (hDrift : κ≤tanh u*√m)
    (hden : den≤live c u L 1*√m) (hzlo : sizeScale m*z≤σ) :
    (∑ w∈ballots L, signMass c u w*(centeredRank c u m w)^2)/(live c u L 1*σ^2) ≤
      (f*G+1/κ)/(4*den*z^2) := by
  let P := live c u L 1
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hr := sqrt_pos.mpr hm'
  have hp : 0<P := pos_of_mul_pos_left (hd.trans_le hden) hr.le
  have hs : 0<sizeScale m := mul_pos hm' hr
  have hσ : 0<σ := (mul_pos hs hz).trans_le hzlo
  have hG₀ : 0≤G := (by positivity : (0:ℝ)≤2*u*√m).trans hG
  have h₁ : 2*u*L≤√m*(f*G) := by
    have K := mul_le_mul_of_nonneg_left hT (by positivity : 0≤2*u)
    have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hf) hr.le
    nlinarith only [K,H,congrArg (fun x : ℝ => 2*u*f*x) (sq_sqrt hm'.le)]
  have hd₀ := pos_of_mul_pos_left (hκ.trans_le hDrift) hr.le
  have h₂ : 1/tanh u≤√m*(1/κ) := by
    rw [← mul_div_assoc,mul_one]; apply (div_le_div_iff₀ hd₀ hκ).mpr
    linarith only [hDrift]
  have htime : 2*u*L+1/tanh u≤√m*(f*G+1/κ) := by linarith only [h₁,h₂]
  have H := (prefix_occupation_drift hL hc hu).trans (mul_le_mul_of_nonneg_left htime (by positivity : 0≤(m:ℝ)^2/4))
  have hfac : den*((m:ℝ)^2*√m)*z^2≤P*σ^2 := by
    have K := mul_le_mul hden (pow_le_pow_left₀ (mul_nonneg hs.le hz.le) hzlo 2) (sq_nonneg _) (mul_nonneg hp.le hr.le)
    change den*((m:ℝ)*√m*z)^2≤P*√m*σ^2 at K
    apply le_of_mul_le_mul_right (a:=√(m:ℝ)) _ hr
    nlinarith only [K]
  apply (div_le_div_iff₀ (mul_pos hp (sq_pos_of_pos hσ)) (by positivity)).mpr
  have HE := mul_le_mul_of_nonneg_right H (by positivity : 0≤4*den*z^2)
  have K := mul_le_mul_of_nonneg_right hfac (add_nonneg (mul_nonneg hf hG₀) (by positivity : 0≤1/κ))
  dsimp only [P] at K
  nlinarith only [HE,K]

end CentralUnimodality.MarkedExcursion
