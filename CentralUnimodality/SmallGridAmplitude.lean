module

public import CentralUnimodality.SmallGridCheck

/-! For a sampled frequency in the first-quadrant range, the two Boolean
checks suffice for an enclosure of the actual staircase amplitude. -/
@[expose] public section

namespace CentralUnimodality.SmallGrid

open PowerSeries Residual

def parityRow (F G : List ℤ) (σ : ℕ) := if σ=0 then F else G

theorem grid_frequency (k f : ℕ) : gridFrequency (2^(k+1)) f = 2*frequency k f := by
  unfold gridFrequency frequency
  push_cast
  ring

theorem uniform_error {N M : ℕ} (hn : 1 ≤ N) (hM : N ≤ M^2) {err u : ℝ} (hu : 0 ≤ u)
    (h : err ≤ u/survival N) : err ≤ (2*M:ℝ)*u := by
  have hs := survival_pos N
  have hb := survival_sq_lower hn
  have hm : (N:ℝ) ≤ (M:ℝ)^2 := by exact_mod_cast hM
  have hc := mul_le_mul_of_nonneg_right hm (sq_nonneg (survival N))
  have hz : 0 ≤ (2*M:ℝ)*survival N := by positivity
  have hroot : 1 ≤ (2*M:ℝ)*survival N := by
    apply (sq_le_sq₀ (by norm_num) hz).mp
    nlinarith only [hb,hc]
  apply h.trans
  apply (div_le_iff₀ hs).mpr
  calc u = 1*u := (one_mul _).symm
       _ ≤ _ := by simpa only [mul_right_comm] using mul_le_mul_of_nonneg_right hroot hu

theorem amplitude_of_rows {k f L n δ : ℕ} (hδ : δ ≤ 1)
    (hL : n+δ < L) {s : ℤ} (hs : 0 < s)
    {er ef e v : ℕ} (R F G : List ℤ) (V E : ℕ → List ℤ) (B : ℕ → ℤ)
    (hrow : ∀ i ≤ n+δ, RowClose k f i s er ef ((rowPolynomial R).coeff i)
      ((rowPolynomial F).coeff i) ((rowPolynomial G).coeff i))
    (hC : ∀ σ ≤ 1, Residual.check (B σ) s L (parityRow F G σ) R (V σ) (E σ) = true)
    (hv : ∀ σ ≤ 1, magnitude (V σ) ≤ v) (he : ∀ σ ≤ 1, magnitude (E σ) ≤ e) :
    |signedAmplitude n δ (gridFrequency (2^(k+1)) f) -
      (coeff (n+δ) (scaledSeries s (rowPolynomial (V (1-δ))))).re/survival (n+δ)| ≤
      2*((ef:ℝ)/s+(e:ℝ)/(s:ℝ)^2+(L:ℝ)*((er:ℝ)/s)*((v:ℝ)/s))/survival (n+δ) := by
  rw [grid_frequency]
  have hraw := checked_half_amplitude (n := n) hδ (2*frequency k f) hs B (parityRow F G) V E R v e
    ((ef:ℝ)/s) ((er:ℝ)/s) (fun σ hσ => check_prefix (by omega) (hC σ hσ)) hv he
    (by
      intro σ hσ i hi
      rcases (by omega : σ=0 ∨ σ=1) with rfl|rfl
      · simpa only [map_sub,halfSeries,coeff_mk,scaledSeries,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0),
          parityRow,ite_true,Nat.add_zero,Close] using (hrow i hi).evenFree
      · simpa only [map_sub,halfSeries,coeff_mk,scaledSeries,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0),
          parityRow,one_ne_zero,ite_false,Close] using (hrow i hi).oddFree)
    (by
      intro i hi
      simpa only [map_sub,halfSeries,coeff_mk,scaledSeries,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0),
        Nat.add_zero,Close] using (hrow i hi).bridge)
  apply hraw.trans
  have hs' : 0 < (s:ℝ) := by exact_mod_cast hs
  have hsur := (survival_pos (n+δ)).le
  gcongr
  exact_mod_cast hL

theorem input_amplitude {d k f L n δ : ℕ} (hd : 0 < d) (hδ : δ ≤ 1)
    (hL : n+δ < L) (ht : (2*(n+δ)+1)*f ≤ 2^k) {s : ℤ} (hs : 0 < s)
    {er ef e v : ℕ} (R F G : List ℤ) (V E : ℕ → List ℤ) (B : ℕ → ℤ)
    (hlen : L ≤ R.length) (hI : check d k f s er ef (start d k f) R F G = true)
    (hC : ∀ σ ≤ 1, Residual.check (B σ) s L (parityRow F G σ) R (V σ) (E σ) = true)
    (hv : ∀ σ ≤ 1, magnitude (V σ) ≤ v) (he : ∀ σ ≤ 1, magnitude (E σ) ≤ e) :
    |signedAmplitude n δ (gridFrequency (2^(k+1)) f) -
      (coeff (n+δ) (scaledSeries s (rowPolynomial (V (1-δ))))).re/survival (n+δ)| ≤
      2*((ef:ℝ)/s+(e:ℝ)/(s:ℝ)^2+(L:ℝ)*((er:ℝ)/s)*((v:ℝ)/s))/survival (n+δ) :=
  amplitude_of_rows hδ hL hs R F G V E B (fun i hi => check_sound hd hs hI i ((hi.trans_lt hL).trans_le hlen)
    ((Nat.mul_le_mul_right f (show 2*i+1 ≤ 2*(n+δ)+1 by omega)).trans ht)) hC hv he

end CentralUnimodality.SmallGrid
