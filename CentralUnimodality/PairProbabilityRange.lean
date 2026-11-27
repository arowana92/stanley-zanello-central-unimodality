module

public import CentralUnimodality.WeightedEndpointPair

/-! The pair cancellation coefficient on each of the two probability
ranges in the increasing-side Fourier estimates. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion

private def gap (w p q : ℝ) := 2*p*(1-p)*q*(1-q)-w*(p*(1-q)+(1-p)*q)

private theorem gap_symm (w p q : ℝ) : gap w p q=gap w q p := by unfold gap; ring

/-- Interpolation between the endpoints leaves a nonnegative quadratic remainder. -/
private theorem gap_segment {w l h p q : ℝ} (hlh : l < h) (hl : l ≤ p) (hh : p ≤ h)
    (hq : 0 ≤ q) (hq' : q ≤ 1) (h₁ : 0 ≤ gap w l q) (h₂ : 0 ≤ gap w h q) : 0 ≤ gap w p q := by
  have he : (h-l)*gap w p q = (h-p)*gap w l q+(p-l)*gap w h q+
      2*q*(1-q)*(h-l)*(p-l)*(h-p) := by unfold gap; ring
  apply nonneg_of_mul_nonneg_right (a := h-l) _ (sub_pos.mpr hlh)
  rw [he]
  have hm := sub_nonneg.mpr hh
  have hn := sub_nonneg.mpr hl
  exact add_nonneg (add_nonneg (mul_nonneg hm h₁) (mul_nonneg hn h₂))
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hq) (sub_nonneg.mpr hq'))
      (sub_nonneg.mpr hlh.le)) hn) hm)

private theorem gap_box {w l h p q : ℝ} (hl : 0 ≤ l) (hh : h ≤ 1) (hlh : l < h)
    (hp : l ≤ p ∧ p ≤ h) (hq : l ≤ q ∧ q ≤ h)
    (h₁ : 0 ≤ gap w l l) (h₂ : 0 ≤ gap w l h) (h₃ : 0 ≤ gap w h h) : 0 ≤ gap w p q := by
  apply gap_segment hlh hp.1 hp.2 (hl.trans hq.1) (hq.2.trans hh)
  · rw [gap_symm]
    exact gap_segment hlh hq.1 hq.2 hl (hlh.le.trans hh) h₁ (by rwa [gap_symm])
  · rw [gap_symm]
    exact gap_segment hlh hq.1 hq.2 (hl.trans hlh.le) hh h₂ h₃

theorem pair_probability_ranges (p q : ℝ) :
    (9/25 ≤ p ∧ p ≤ 31/50 → 9/25 ≤ q ∧ q ≤ 31/50 →
      1/5*(p*(1-q)+(1-p)*q) ≤ 2*(p*(1-q))*((1-p)*q)) ∧
    (11/50 ≤ p ∧ p ≤ 17/25 → 11/50 ≤ q ∧ q ≤ 17/25 →
      3/25*(p*(1-q)+(1-p)*q) ≤ 2*(p*(1-q))*((1-p)*q)) := by
  constructor
  · intro hp hq
    have H := gap_box (w := 1/5) (by norm_num) (by norm_num) (by norm_num) hp hq
      (by norm_num [gap]) (by norm_num [gap]) (by norm_num [gap])
    dsimp [gap] at H; linarith only [H]
  · intro hp hq
    have H := gap_box (w := 3/25) (by norm_num) (by norm_num) (by norm_num) hp hq
      (by norm_num [gap]) (by norm_num [gap]) (by norm_num [gap])
    dsimp [gap] at H; linarith only [H]

end CentralUnimodality.MarkedExcursion
