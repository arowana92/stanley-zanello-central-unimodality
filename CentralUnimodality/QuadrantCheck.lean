module

public import CentralUnimodality.QuadrantTail
public import CentralUnimodality.SmallGridAmplitude

/-! A positive interval prefix followed by a norm bound for all later
inputs. The two parts certify each coefficient of the exported arrays. -/
@[expose] public section

namespace CentralUnimodality.SmallGrid

open PowerSeries Residual

def tailFits (s : ℤ) (e : ℕ) (z : ℤ) : Bool := decide (s+2^57*|z| ≤ 2^57*e)

private theorem close_tail {s : ℤ} (hs : 0 < s) {e : ℕ} {z : ℤ} {w : ℂ}
    (hf : tailFits s e z = true) (hw : ‖w‖ ≤ 1/(2:ℝ)^57) : Close s e z w := by
  have he := of_decide_eq_true hf
  have he' : (s:ℝ)+2^57*|(z:ℝ)| ≤ 2^57*(e:ℝ) := by exact_mod_cast he
  have hs' : 0 < (s:ℝ) := by exact_mod_cast hs
  unfold Close
  apply (norm_sub_le ..).trans
  rw [norm_div]
  have hn (a : ℤ) : ‖(a:ℂ)‖ = |(a:ℝ)| := by simp
  rw [hn,hn,abs_of_pos hs']
  apply (add_le_add hw le_rfl).trans
  rw [div_add_div _ _ (by norm_num : (2:ℝ)^57 ≠ 0) hs'.ne']
  apply (div_le_div_iff₀ (by positivity) hs').mpr
  have hh := mul_le_mul_of_nonneg_right he' hs'.le
  linarith only [show ((1:ℝ)*s+2^57*|(z:ℝ)|)*s ≤ (e:ℝ)*(2^57*s) by convert hh using 1 <;> ring]

def cutCheck (d k f l : ℕ) (s : ℤ) (er ef : ℕ) (R F G : List ℤ) : Bool :=
  (decide (F.length=R.length ∧ G.length=R.length) &&
    check d k f s er ef (start d k f) (R.take (l+1)) (F.take (l+1)) (G.take (l+1))) &&
  ((R.drop (l+1)).all (tailFits s er) && ((F.drop (l+1)).all (tailFits s ef) &&
    (G.drop (l+1)).all (tailFits s ef)))

private theorem fits_in_drop {s : ℤ} {e l i : ℕ} {A : List ℤ} (hi : i < A.length) (hl : l ≤ i)
    (h : (A.drop l).all (tailFits s e) = true) : tailFits s e (A[i]?.getD 0) = true := by
  have hp : i-l < (A.drop l).length := by simp; omega
  have hm := List.getElem_mem (l := A.drop l) hp
  have hh := List.all_eq_true.mp h _ hm
  simpa only [List.getElem?_eq_getElem hi,Option.getD_some,List.getElem_drop,Nat.add_sub_of_le hl] using hh

theorem cut_sound {d k f l i : ℕ} (hd : 0 < d) {s : ℤ} (hs : 0 < s) {er ef : ℕ}
    (hl : 200 ≤ l) (hlo : (2*l+1)*f ≤ 2^k) (hhi : 2^k ≤ (2*l+3)*f)
    {R F G : List ℤ} (hc : cutCheck d k f l s er ef R F G = true) (hi : i < R.length) :
    RowClose k f i s er ef ((rowPolynomial R).coeff i) ((rowPolynomial F).coeff i) ((rowPolynomial G).coeff i) := by
  simp only [cutCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  by_cases hh : i ≤ l
  · have hlen : i < (R.take (l+1)).length := by simp; omega
    have ht := (Nat.mul_le_mul_right f (show 2*i+1 ≤ 2*l+1 by omega)).trans hlo
    have hp := check_sound hd hs hc.1.2 i hlen ht
    simpa only [coeff_rowPolynomial,List.getElem?_take_of_lt (show i < l+1 by omega)] using hp
  · have h₁ := grid_quadrant_tail hl hlo hhi (n := 2*i) (by omega)
    have h₂ := grid_quadrant_tail hl hlo hhi (n := 2*i+1) (by omega)
    have hF : i < F.length := hc.1.1.1.symm ▸ hi
    have hG : i < G.length := hc.1.1.2.symm ▸ hi
    simp only [coeff_rowPolynomial]
    exact ⟨close_tail hs (fits_in_drop hi (by omega) hc.2.1) h₁.2,
      close_tail hs (fits_in_drop hF (by omega) hc.2.2.1) h₁.1,
      close_tail hs (fits_in_drop hG (by omega) hc.2.2.2) h₂.1⟩

theorem cut_amplitude {d k f l L n δ : ℕ} (hd : 0 < d) (hδ : δ ≤ 1)
    (hL : n+δ < L) (hl : 200 ≤ l) (hlo : (2*l+1)*f ≤ 2^k) (hhi : 2^k ≤ (2*l+3)*f)
    {s : ℤ} (hs : 0 < s) {er ef e v : ℕ} (R F G : List ℤ) (V E : ℕ → List ℤ) (B : ℕ → ℤ)
    (hlen : L ≤ R.length) (hI : cutCheck d k f l s er ef R F G = true)
    (hC : ∀ σ ≤ 1, Residual.check (B σ) s L (parityRow F G σ) R (V σ) (E σ) = true)
    (hv : ∀ σ ≤ 1, magnitude (V σ) ≤ v) (he : ∀ σ ≤ 1, magnitude (E σ) ≤ e) :
    |signedAmplitude n δ (gridFrequency (2^(k+1)) f) -
      (coeff (n+δ) (scaledSeries s (rowPolynomial (V (1-δ))))).re/survival (n+δ)| ≤
      2*((ef:ℝ)/s+(e:ℝ)/(s:ℝ)^2+(L:ℝ)*((er:ℝ)/s)*((v:ℝ)/s))/survival (n+δ) :=
  amplitude_of_rows hδ hL hs R F G V E B (fun _ hi => cut_sound hd hs hl hlo hhi hI ((hi.trans_lt hL).trans_le hlen)) hC hv he

end CentralUnimodality.SmallGrid
