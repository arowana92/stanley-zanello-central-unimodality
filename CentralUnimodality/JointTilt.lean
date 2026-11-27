module

public import CentralUnimodality.RankTilt
import Mathlib.Algebra.BigOperators.Intervals

/-! Exact cost of changing the rank parameter and the prefix height
parameter together under the independent sign law. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- Mean down-label sum under natural parameters c, 2c, ..., mc. -/
noncomputable def meanRank (c : ℝ) (m : ℕ) :=
  ∑ i ∈ Finset.range m, ((i:ℝ)+1)*(1-tanh (c*(i+1)))/2

/-- Sum of the t largest labels of a length-m walk. -/
noncomputable def prefixLabels (m t : ℕ) : ℝ := t*((m:ℝ)-((t:ℝ)-1)/2)

/-- Sum of the squared labels. -/
noncomputable def labelSquares (m : ℕ) : ℝ := (m:ℝ)*(m+1)*(2*m+1)/6

theorem sum_prefixLabels (m t : ℕ) :
    (∑ i ∈ Finset.range t, ((m:ℝ)-i)) = prefixLabels m t := by
  induction t with
  | zero => simp [prefixLabels]
  | succ t ih => rw [Finset.sum_range_succ,ih]; unfold prefixLabels; push_cast; ring

theorem sum_labelSquares (m : ℕ) :
    (∑ i ∈ Finset.range m, ((m:ℝ)-i)^2) = labelSquares m := by
  have h := linear_sum_sq 1 m m
  simp only [one_mul,one_pow] at h
  rw [h,labelSquares]; ring

theorem reverse_labels (m : ℕ) (f : ℝ → ℝ) :
    ∑ i ∈ Finset.range m, f ((i:ℝ)+1) = ∑ i ∈ Finset.range m, f ((m:ℝ)-i) := by
  rw [← Finset.sum_range_reflect (fun i : ℕ => f ((i:ℝ)+1)) m]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  congr 1
  rw [Nat.cast_sub (by omega : i ≤ m-1),Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one]; ring

private theorem restrict_sum {m t : ℕ} (ht : t ≤ m) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range m, if i<t then f i else 0) = ∑ i ∈ Finset.range t, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

private theorem log_label (u : ℝ) : log (1+exp (-2*u)) = log 2 + log (cosh u)-u := by
  have h : 1+exp (-2*u) = 2*cosh u*exp (-u) := by
    rw [cosh_eq]
    have he := exp_add u (-u)
    have he' := exp_add (-u) (-u)
    rw [show u+-u=0 by ring,exp_zero] at he
    rw [show -u+-u = -2*u by ring] at he'
    nlinarith only [he,he']
  rw [h,log_mul (by positivity) (exp_pos _).ne',log_mul (by norm_num) (cosh_pos _).ne',log_exp]; ring

private theorem log_rank (u : ℝ) (m : ℕ) :
    log (rankNormalizer u m) = ∑ i ∈ Finset.range m, log (1+exp (-2*(u*((m:ℝ)-i)))) := by
  rw [rankNormalizer,log_prod (fun _ _ => by positivity)]
  simpa only [mul_assoc] using reverse_labels m (fun r => log (1+exp (-2*(u*r))))

private theorem log_prefix (v b : ℝ) (m t : ℕ) :
    log (coshProduct v (v*m-b) t) =
      ∑ i ∈ Finset.range t, log (cosh (v*((m:ℝ)-i)-b)) := by
  rw [coshProduct,log_prod (fun _ _ => (cosh_pos _).ne')]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ring

private theorem site_cost (c z b r : ℝ) :
    z*(r*(1-tanh (c*r))) + (log (1+exp (-2*((c+z)*r)))-log (1+exp (-2*(c*r)))) +
        (log (cosh ((c+z)*r-b))-log (cosh ((c+z)*r))) ≤
      (z*r)^2/2 + (b^2/2-b*tanh (c*r)-b*z*r) := by
  rw [log_label,log_label]
  have h := log_cosh_shift (c*r) (z*r-b)
  rw [show c*r+(z*r-b) = (c+z)*r-b by ring] at h
  linarith only [h]

/-- R times the prefix height Laplace transform, evaluated at the
unrestricted mean rank. The first factor is the rank change of measure. -/
noncomputable def jointCost (c z b : ℝ) (m t : ℕ) :=
  (rankNormalizer (c+z) m/rankNormalizer c m)*exp (2*z*meanRank c m) *
    (coshProduct (c+z) ((c+z)*m-b) t/coshProduct (c+z) ((c+z)*m) t)

theorem joint_cost_log {m t : ℕ} (ht : t ≤ m) (c z b : ℝ) :
    log (jointCost c z b m t) ≤ z^2*labelSquares m/2 + b^2*t/2 -
      b*(∑ i ∈ Finset.range t, tanh (c*((m:ℝ)-i))) - b*z*prefixLabels m t := by
  let r := fun i : ℕ => (m:ℝ)-i
  let C := fun i : ℕ => log (cosh ((c+z)*r i-b))-log (cosh ((c+z)*r i))
  let E := fun i : ℕ => b^2/2-b*tanh (c*r i)-b*z*r i
  have term (i : ℕ) : z*(r i*(1-tanh (c*r i))) +
      (log (1+exp (-2*((c+z)*r i)))-log (1+exp (-2*(c*r i)))) +
      (if i<t then C i else 0) ≤ (z*r i)^2/2 + (if i<t then E i else 0) := by
    by_cases hi : i<t
    · simpa only [ite_eq_left hi,C,E] using site_cost c z b (r i)
    · simpa [hi] using site_cost c z 0 (r i)
  have h := Finset.sum_le_sum (s := Finset.range m) (fun i _ => term i)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,restrict_sum ht] at h
  have hm : 2*z*meanRank c m = ∑ i ∈ Finset.range m, z*(r i*(1-tanh (c*r i))) := by
    rw [meanRank,reverse_labels m (fun x => x*(1-tanh (c*x))/2),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [r]; ring
  have hl : log (jointCost c z b m t) =
      (∑ i ∈ Finset.range m, z*(r i*(1-tanh (c*r i)))) +
      ((∑ i ∈ Finset.range m, log (1+exp (-2*((c+z)*r i))))-
       ∑ i ∈ Finset.range m, log (1+exp (-2*(c*r i)))) + ∑ i ∈ Finset.range t, C i := by
    unfold jointCost
    rw [log_mul (mul_pos (div_pos (rankNormalizer_pos ..) (rankNormalizer_pos ..)) (exp_pos _)).ne'
      (div_pos (coshProduct_pos ..) (coshProduct_pos ..)).ne',
      log_mul (div_pos (rankNormalizer_pos ..) (rankNormalizer_pos ..)).ne' (exp_pos _).ne',
      log_div (rankNormalizer_pos ..).ne' (rankNormalizer_pos ..).ne',
      log_div (coshProduct_pos ..).ne' (coshProduct_pos ..).ne',log_exp,hm,log_rank,log_rank,log_prefix,
      show log (coshProduct (c+z) ((c+z)*m) t) = ∑ i ∈ Finset.range t, log (cosh ((c+z)*r i)) by
        simpa only [sub_zero,r] using log_prefix (c+z) 0 m t]
    simp only [C,Finset.sum_sub_distrib,r]
    ring
  rw [hl]
  apply h.trans_eq
  have hs : (∑ i ∈ Finset.range m, (z*r i)^2/2) = z^2*labelSquares m/2 := by
    simp only [mul_pow,div_eq_mul_inv,← Finset.sum_mul,← Finset.mul_sum,r,sum_labelSquares]
  rw [hs]
  simp only [E,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    ← Finset.mul_sum,r]
  rw [← sum_prefixLabels]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring

theorem jointCost_pos (c z b : ℝ) (m t : ℕ) : 0 < jointCost c z b m t :=
  mul_pos (mul_pos (div_pos (rankNormalizer_pos ..) (rankNormalizer_pos ..)) (exp_pos _))
    (div_pos (coshProduct_pos ..) (coshProduct_pos ..))

theorem joint_cost_bound {m t : ℕ} (hm : 0 < m) (ht : t ≤ m) {c b : ℝ} (hc : 0 ≤ c)
    (hb : 0 ≤ b) (z : ℝ) :
    jointCost c z b m t ≤ exp (z^2*labelSquares m/2 + b^2*t/2 -
      b*(tanh (c*m)/m+z)*prefixLabels m t) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hx (i : ℕ) (hi : i ∈ Finset.range t) :
      (tanh (c*m)/m)*((m:ℝ)-i) ≤ tanh (c*((m:ℝ)-i)) := by
    have hil : (i:ℝ) ≤ m := by exact_mod_cast ((Finset.mem_range.mp hi).le.trans ht)
    let a := ((m:ℝ)-i)/m
    have h := tanh_chord (mul_nonneg hc hm'.le) (div_nonneg (sub_nonneg.mpr hil) hm'.le)
      (show a ≤ 1 from (div_le_one hm').mpr (sub_le_self _ (Nat.cast_nonneg _)))
    rw [show ((m:ℝ)-i)/m * (c*m) = c*(m-i) by field_simp] at h
    convert h using 1; ring
  have h := Finset.sum_le_sum hx
  rw [← Finset.mul_sum,sum_prefixLabels] at h
  rw [← log_le_iff_le_exp (jointCost_pos ..)]
  apply (joint_cost_log ht c z b).trans
  linarith only [mul_le_mul_of_nonneg_left h hb]

/-- The centered first-hit shift b=(c+z)(m-d) at time 2d+1. -/
theorem centered_joint_cost {m d : ℕ} (ht : 2*d+1 ≤ m) {c z : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) :
    jointCost c z ((c+z)*(m-d)) m (2*d+1) ≤
      exp (z^2*labelSquares m/2 -
        (2*(d:ℝ)+1)*((m:ℝ)-d)^2*(c+z)*(c*(1-2*(c*m)^2/3)+z)/2) := by
  have hm : 0 < m := by omega
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hr : 0 ≤ (m:ℝ)-d := sub_nonneg.mpr (by exact_mod_cast (show d ≤ m by omega))
  let b := (c+z)*((m:ℝ)-d)
  have hb : 0 ≤ b := mul_nonneg (add_nonneg hc hz) hr
  have hk : c*(1-(c*m)^2/3) ≤ tanh (c*m)/m := by
    apply (le_div_iff₀ hm').mpr
    linarith only [tanh_cubic_lower (mul_nonneg hc hm'.le)]
  have hp : prefixLabels m (2*d+1) = (2*(d:ℝ)+1)*(m-d) := by unfold prefixLabels; push_cast; ring
  apply (joint_cost_bound hm ht hc hb z).trans
  apply exp_le_exp.mpr
  rw [hp]
  push_cast
  have hcoef : 0 ≤ b*((2*(d:ℝ)+1)*(m-d)) := mul_nonneg hb (mul_nonneg (by positivity) hr)
  have hprod := mul_le_mul_of_nonneg_right hk hcoef
  dsimp [b] at hprod ⊢
  linarith only [hprod]

end CentralUnimodality.MarkedExcursion
