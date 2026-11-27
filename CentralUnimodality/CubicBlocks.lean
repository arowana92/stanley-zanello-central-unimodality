module

public import CentralUnimodality.PointHitBound

/-! Pair opposite positions at each length, including odd lengths. The
quadratic contributions telescope to (j³-j)/96 in the free kernel. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def cubicEnvelope (v θ : ℝ) (j : ℕ) :=
  Real.exp (-(v*θ^2*((j:ℝ)^3-j)/96))

private theorem small_pair_exp {x H v : ℝ} (hx : 0 ≤ x) (hH : x ≤ H)
    (hH' : H^2 ≤ 6) (hv : v ≤ (1-H^2/6)^2) :
    (1+|Real.cos x|)/2 ≤ Real.exp (-(v*x^2/4)) := by
  have hs : x*(1-x^2/6) ≤ Real.sin x := by
    rcases hx.eq_or_lt with he|h
    · simp [← he]
    · linarith only [Real.sin_gt_sub_cube h]
  have hsq := (sq_le_sq₀ hx (hx.trans hH)).mpr hH
  have hprod : 0 ≤ x*(1-H^2/6) := mul_nonneg hx (by linarith)
  have hs' : x*(1-H^2/6) ≤ Real.sin x :=
    (mul_le_mul_of_nonneg_left (by linarith only [hsq]) hx).trans hs
  have hl := pow_le_pow_left₀ hprod hs' 2
  have hvl := mul_le_mul_of_nonneg_right hv (sq_nonneg x)
  apply le_trans _ (Real.add_one_le_exp _)
  nlinarith only [hl,hvl,Real.sin_sq_add_cos_sq x,sq_abs (Real.cos x),
    sq_nonneg (1-|Real.cos x|)]

private theorem cubic_zero (θ : ℝ) : EndpointNormBound (θ/2) 0 1 := by
  simpa [pairFactor] using endpoint_norm_even (θ/2) 0

theorem free_cubic_block {v θ H : ℝ} {L : ℕ} (hθ : 0 ≤ θ) (hL : θ/2*L ≤ H)
    (hH : H^2 ≤ 6) (hv : v ≤ (1-H^2/6)^2) (j : ℕ) (hj : j ≤ L) :
    EndpointNormBound (θ/2) j ((2:ℝ)^j*cubicEnvelope v θ j) := by
  induction j using Nat.twoStepInduction with
  | zero => simpa [cubicEnvelope] using cubic_zero θ
  | one => simpa [cubicEnvelope] using endpoint_norm_one (cubic_zero θ)
  | more n ih _ =>
    have h := endpoint_norm_pair (ih (by omega))
    have hx : (θ/2)*((n:ℝ)+1) ≤ H :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : n+1 ≤ L)) (by positivity)).trans hL
    have hf := small_pair_exp (by positivity : 0 ≤ θ/2*((n:ℝ)+1)) hx hH hv
    have hm : 2+2*|Real.cos (θ/2*(n+1))| ≤ 4*Real.exp (-(v*(θ/2*(n+1))^2/4)) := by linarith only [hf]
    intro s
    apply (h s).trans
    apply (mul_le_mul_of_nonneg_right hm (by unfold cubicEnvelope; positivity)).trans_eq
    unfold cubicEnvelope
    rw [show 4*Real.exp (-(v*(θ/2*(n+1))^2/4))*((2:ℝ)^n*Real.exp (-(v*θ^2*((n:ℝ)^3-n)/96))) =
        2^(n+2)*(Real.exp (-(v*(θ/2*(n+1))^2/4))*Real.exp (-(v*θ^2*((n:ℝ)^3-n)/96))) by rw [pow_add]; ring,
      ← Real.exp_add]
    congr 2
    push_cast
    ring

end CentralUnimodality
