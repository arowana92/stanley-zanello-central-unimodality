module

public import CentralUnimodality.SmallGridInputs
public import CentralUnimodality.PackedAmplitude

/-! Check exported dyadic input rows against rigorously rounded
enclosures for their exact walk transforms. -/
@[expose] public section

namespace CentralUnimodality.SmallGrid

open PowerSeries PositiveEnclosure Residual

def fits (d : ℕ) (s : ℤ) (e : ℕ) (a : ℕ × ℕ) (z : ℤ) : Bool :=
  decide ((z-e)*d ≤ (a.1:ℤ)*s ∧ (a.2:ℤ)*s ≤ (z+e)*d)

def Close (s : ℤ) (e : ℕ) (z : ℤ) (w : ℂ) := ‖w-(z:ℂ)/s‖ ≤ (e:ℝ)/s

private theorem close_of_fits {d : ℕ} {s : ℤ} (hd : 0 < d) (hs : 0 < s) {e : ℕ} {a : ℕ × ℕ}
    {z : ℤ} {w : ℂ} (h : Contains d a w) (hf : fits d s e a z = true) : Close s e z w := by
  obtain ⟨x,rfl,hlo,hhi⟩ := h
  obtain ⟨hl,hu⟩ := of_decide_eq_true hf
  have h₁ : ((z:ℝ)-e)*d ≤ (a.1:ℝ)*s := by exact_mod_cast hl
  have h₂ : (a.2:ℝ)*s ≤ ((z:ℝ)+e)*d := by exact_mod_cast hu
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hl' := h₁.trans (mul_le_mul_of_nonneg_right hlo hs'.le)
  have hu' := (mul_le_mul_of_nonneg_right hhi hs'.le).trans h₂
  have hl'' : (z:ℝ)-e ≤ x*s := by
    apply le_of_mul_le_mul_right (a := (d:ℝ)) _ hd'
    convert hl' using 1; ring
  have hu'' : x*s ≤ (z:ℝ)+e := by
    apply le_of_mul_le_mul_right (a := (d:ℝ)) _ hd'
    convert hu' using 1; ring
  unfold Close
  change ‖(x:ℂ)-((z:ℝ):ℂ)/((s:ℝ):ℂ)‖ ≤ _
  rw [← Complex.ofReal_div,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    sub_div' (ne_of_gt hs'),abs_div,abs_of_pos hs',div_le_div_iff_of_pos_right hs',abs_le]
  constructor <;> linarith

def check (d k f : ℕ) (s : ℤ) (er ef : ℕ) :
    Inputs → List ℤ → List ℤ → List ℤ → Bool
  | _,[],[],[] => true
  | v,r::rs,a::as,b::bs =>
    (v.valid && (fits d s er v.bridge r && (fits d s ef v.evenFree a && fits d s ef v.oddFree b))) &&
    check d k f s er ef (next d k f v) rs as bs
  | _,_,_,_ => false

structure RowClose (k f j : ℕ) (s : ℤ) (er ef : ℕ) (r a b : ℤ) : Prop where
  bridge : Close s er r (coeff (2*j) (fairSeries (areaCharacter (frequency k f)) bridges))
  evenFree : Close s ef a (coeff (2*j) (fairSeries (areaCharacter (frequency k f)) words))
  oddFree : Close s ef b (coeff (2*j+1) (fairSeries (areaCharacter (frequency k f)) words))

private theorem check_at {d k f : ℕ} {s : ℤ} {er ef : ℕ} (hd : 0 < d) (hs : 0 < s)
    (R F G : List ℤ) (j i : ℕ) (hi : i < R.length) (ht : (2*(j+i)+1)*f ≤ 2^k)
    (hc : check d k f s er ef (inputs d k f j) R F G = true) :
    RowClose k f (j+i) s er ef (R[i]?.getD 0) (F[i]?.getD 0) (G[i]?.getD 0) := by
  induction R generalizing j i F G with
  | nil => simp at hi
  | cons r rs ih =>
    cases F with
    | nil => simp [check] at hc
    | cons a as =>
      cases G with
      | nil => simp [check] at hc
      | cons b bs =>
        simp only [check,Bool.and_eq_true] at hc
        cases i with
        | zero =>
          have h := inputs_sound hd (by simpa using ht) hc.1.1
          exact ⟨close_of_fits hd hs h.bridge hc.1.2.1,close_of_fits hd hs h.evenFree hc.1.2.2.1,
            close_of_fits hd hs h.oddFree hc.1.2.2.2⟩
        | succ i =>
          have he : j+(i+1) = j+1+i := by omega
          rw [he] at ht ⊢
          exact ih as bs (j+1) i (by simpa using hi) ht hc.2

theorem check_sound {d k f : ℕ} {s : ℤ} {er ef : ℕ} (hd : 0 < d) (hs : 0 < s)
    {R F G : List ℤ} (h : check d k f s er ef (start d k f) R F G = true)
    (i : ℕ) (hi : i < R.length) (ht : (2*i+1)*f ≤ 2^k) :
    RowClose k f i s er ef ((rowPolynomial R).coeff i) ((rowPolynomial F).coeff i) ((rowPolynomial G).coeff i) := by
  simp only [coeff_rowPolynomial]
  simpa only [Nat.zero_add] using check_at hd hs R F G 0 i hi (by simpa using ht) h

end CentralUnimodality.SmallGrid
