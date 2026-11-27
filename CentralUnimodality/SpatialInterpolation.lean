module

public import CentralUnimodality.SpatialDerivatives
public import Mathlib.Analysis.Convex.Deriv

/-! Uniform interpolation on a spatial mesh, with the factor 1/8 from
the second derivative. Endpoint errors enter through their convex average. -/
@[expose] public section

namespace CentralUnimodality

def chord (u a b : ℝ) := (1-u)*a+u*b

private theorem chord_upper {f g d : ℝ → ℝ} {M : ℝ} (hf : ∀ x, HasDerivAt f (g x) x)
    (hg : ∀ x, HasDerivAt g (d x) x) (hd : ∀ x, -M ≤ d x) (u a b : ℝ) (hu : 0 ≤ u) (hv : u ≤ 1) :
    f (chord u a b)-chord u (f a) (f b) ≤ (M/2)*u*(1-u)*(b-a)^2 := by
  let F := fun x : ℝ => f x + M/2*x^2
  let H := fun x : ℝ => g x + M*x
  have hF (x : ℝ) : HasDerivAt F (H x) x := by
    dsimp [F,H]
    convert (hf x).add ((hasDerivAt_pow 2 x).const_mul (M/2)) using 1
    norm_num
    ring
  have hH (x : ℝ) : HasDerivAt H (d x+M) x := by
    simpa [H] using (hg x).fun_add ((hasDerivAt_id x).const_mul M)
  have he : deriv F = H := funext fun x => (hF x).deriv
  have hc : ConvexOn ℝ Set.univ F := by
    apply convexOn_univ_of_deriv2_nonneg (fun x => (hF x).differentiableAt)
    · rw [he]
      exact fun x => (hH x).differentiableAt
    · intro x
      change 0 ≤ deriv (deriv F) x
      rw [he,(hH x).deriv]
      linarith only [hd x]
  have h := hc.2 (Set.mem_univ a) (Set.mem_univ b) (sub_nonneg.mpr hv) hu (by ring : (1-u)+u=1)
  change f (chord u a b)+M/2*(chord u a b)^2 ≤ (1-u)*(f a+M/2*a^2)+u*(f b+M/2*b^2) at h
  unfold chord at h ⊢
  linarith only [h]

theorem interpolation_error {f g d : ℝ → ℝ} {M : ℝ} (hf : ∀ x, HasDerivAt f (g x) x)
    (hg : ∀ x, HasDerivAt g (d x) x) (hd : ∀ x, |d x| ≤ M) (a b u : ℝ) (hu : 0 ≤ u) (hv : u ≤ 1) :
    |f (chord u a b)-chord u (f a) (f b)| ≤ (b-a)^2*M/8 := by
  have hM := (abs_nonneg _).trans (hd a)
  have hcap : (M/2)*u*(1-u)*(b-a)^2 ≤ (b-a)^2*M/8 := by
    nlinarith only [mul_nonneg (mul_nonneg hM (sq_nonneg (u-1/2))) (sq_nonneg (b-a))]
  have h₁ := chord_upper hf hg (fun x => (abs_le.mp (hd x)).1) u a b hu hv
  have h₂ := chord_upper (fun x => (hf x).neg) (fun x => (hg x).neg)
    (M := M) (fun x => neg_le_neg (abs_le.mp (hd x)).2) u a b hu hv
  apply abs_le.mpr
  constructor
  · dsimp only [Pi.neg_apply] at h₂
    unfold chord at h₂ ⊢
    linarith only [h₂,hcap]
  · exact h₁.trans hcap

theorem spatial_mesh_error {Q J : ℕ} {G : ℝ} (hG : 0 ≤ G) (A : ℕ → ℝ) (r : ℕ)
    (a b u L R e : ℝ) (hu : 0 ≤ u) (hv : u ≤ 1)
    (ha : |spatialDerivative Q J G A r a-L| ≤ e) (hb : |spatialDerivative Q J G A r b-R| ≤ e) :
    |spatialDerivative Q J G A r (chord u a b)-chord u L R| ≤
      e + (b-a)^2*spectralAllowance G Q J (r+2) (fun t => |A t|)/8 := by
  let F := spatialDerivative Q J G A r
  have h := interpolation_error (spatial_derivative_step Q J r G A)
    (spatial_derivative_step Q J (r+1) G A) (spatial_derivative_bound hG A (r+2)) a b u hu hv
  have hc : |chord u (F a) (F b)-chord u L R| ≤ e := by
    rw [show chord u (F a) (F b)-chord u L R = (1-u)*(F a-L)+u*(F b-R) by unfold chord; ring]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hv),abs_of_nonneg hu]
    apply (add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hv)) (mul_le_mul_of_nonneg_left hb hu)).trans_eq
    ring
  apply (abs_sub_le _ (chord u (F a) (F b)) _).trans
  exact (add_le_add h hc).trans_eq (add_comm ..)

end CentralUnimodality
