module

public import CentralUnimodality.FourierCertificate

/-! The three sign tests on the retained inverse imply weak unimodality
of the actual integer rank counts on the specified interval. -/
@[expose] public section

namespace CentralUnimodality

private theorem scaled_real_error {x y : ℂ} {s e : ℝ} (hs : 0 ≤ s) (h : s*‖x-y‖ ≤ e) :
    |s*x.re-s*y.re| ≤ e := by
  rw [← mul_sub,abs_mul,abs_of_nonneg hs,← Complex.sub_re]
  exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hs).trans h

private theorem rank_real (n δ i : ℕ) : (rankProbability n δ i).re =
    (rankCount (2*n+δ) i:ℝ)/((2*n+δ).choose n:ℝ) := by
  rw [rankProbability,← Complex.ofReal_natCast,← Complex.ofReal_natCast,← Complex.ofReal_div,Complex.ofReal_re]

private theorem rank_first_signs (n δ j : ℕ) :
    (0 ≤ (fwdDiff 1 (rankProbability n δ) j).re ↔ rankCount (2*n+δ) j ≤ rankCount (2*n+δ) (j+1)) ∧
    ((fwdDiff 1 (rankProbability n δ) j).re ≤ 0 ↔ rankCount (2*n+δ) (j+1) ≤ rankCount (2*n+δ) j) := by
  have hm : 0 < ((2*n+δ).choose n:ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  simp only [fwdDiff,Complex.sub_re,rank_real,← sub_div,le_div_iff₀ hm,div_le_iff₀ hm,zero_mul,
    sub_nonneg,sub_nonpos,Nat.cast_le,and_self]

private theorem rank_second_sign (n δ j : ℕ) :
    ((fwdDiff 1)^[2] (rankProbability n δ) j).re ≤ 0 ↔
      rankCount (2*n+δ) j+rankCount (2*n+δ) (j+2) ≤ 2*rankCount (2*n+δ) (j+1) := by
  have hm : 0 < ((2*n+δ).choose n:ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  change (fwdDiff 1 (fwdDiff 1 (rankProbability n δ)) j).re ≤ 0 ↔ _
  simp only [fwdDiff,Complex.sub_re,rank_real,← sub_div,div_le_iff₀ hm,zero_mul]
  have he : ∀ x y z : ℝ, z-y-(y-x) ≤ 0 ↔ x+z ≤ 2*y := by intros; constructor <;> intro <;> linarith
  rw [he]
  exact_mod_cast Iff.rfl

theorem rank_window_of_fourier_signs {n δ Q J lo a b hi : ℕ} (hδ : δ ≤ 1)
    (hn : 2049 ≤ n+δ) (hmax : n+δ ≤ 300000) (hNy : 2*J < Q)
    (hQ : 5*Witness.cellScale (n+δ) ≤ Q)
    (hJ : 2048 ≤ (2*Real.pi*Witness.cellScale (n+δ)/Q)*J)
    (hlo : lo ≤ a) (hab : a ≤ b) (hhi : b ≤ hi) (hD : hi+1 ≤ n*(n+δ))
    (hx : ((n*(n+δ)-lo:ℕ):ℝ)+(3*n+2*δ+1)/2 ≤ 0.63*Witness.cellScale (n+δ))
    {G : ℝ} (hG : 0 < G) (hGS : G ≤ Witness.cellScale (n+δ)) (A e : ℕ → ℝ)
    (he : ∀ t ∈ positiveModes J, |signedAmplitude n δ (gridFrequency Q t)-A t| ≤ e t)
    (left : ∀ j, lo ≤ j → j < a → 0.00026+spectralAllowance G Q J 1 e ≤
      G^2*(fwdDiff 1 (cosineInverse n δ Q J A) j).re)
    (middle : ∀ j, a ≤ j → j+1 < b → G^3*((fwdDiff 1)^[2] (cosineInverse n δ Q J A) j).re ≤
      -(0.95+spectralAllowance G Q J 2 e))
    (right : ∀ j, b ≤ j → j < hi → G^2*(fwdDiff 1 (cosineInverse n δ Q J A) j).re ≤
      -(0.00026+spectralAllowance G Q J 1 e)) :
    UnimodalOn (rankCount (2*n+δ)) lo hi := by
  have hs (j : ℕ) (hl : lo ≤ j) (hu : j < hi) := certified_rank_differences hδ hn hmax
    (by omega : j+2 ≤ n*(n+δ)) hNy hQ hJ (by
      have hk : ((n*(n+δ)-j:ℕ):ℝ) ≤ ((n*(n+δ)-lo:ℕ):ℝ) := by exact_mod_cast Nat.sub_le_sub_left hl _
      linarith only [hk,hx]) hG.le hGS A e he
  apply unimodalOn_of_curvature hlo hab hhi
  · intro j hl hu
    apply (rank_first_signs ..).1.mp
    have herr := (abs_le.mp (scaled_real_error (sq_nonneg G) (hs j hl (by omega)).1)).1
    have hsign := left j hl hu
    apply nonneg_of_mul_nonneg_right (a := G^2) _ (by positivity)
    linarith only [herr,hsign]
  · intro j hl hu
    apply (rank_second_sign ..).mp
    have herr := (abs_le.mp (scaled_real_error (pow_nonneg hG.le 3) (hs j (by omega) (by omega)).2)).2
    have hsign := middle j hl hu
    apply nonpos_of_mul_nonpos_right (a := G^3) _ (by positivity)
    linarith only [herr,hsign]
  · intro j hl hu
    apply (rank_first_signs ..).2.mp
    have herr := (abs_le.mp (scaled_real_error (sq_nonneg G) (hs j (by omega) hu).1)).2
    have hsign := right j hl hu
    apply nonpos_of_mul_nonpos_right (a := G^2) _ (by positivity)
    linarith only [herr,hsign]

end CentralUnimodality
