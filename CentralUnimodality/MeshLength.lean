module

public import CentralUnimodality.SpatialWindow
public import CentralUnimodality.SmallGridAmplitude

/-! Integer rounding after dividing a stored amplitude by its exact survival
probability, and the length interpolation error at a retained frequency. -/
@[expose] public section

namespace CentralUnimodality.MeshLength

/-- Round down a scaled signed numerator after conditioning on survival. -/
def rounded (d : ℕ) (s v : ℤ) (N : ℕ) : ℤ :=
  ((d:ℤ)*v*4^N)/(s*Nat.fast_choose (2*N) N)

private theorem quotient_error (v : ℤ) {b : ℤ} (hb : 0 < b) :
    0 ≤ (v:ℝ)/b-(v/b:ℤ) ∧ (v:ℝ)/b-(v/b:ℤ) ≤ 1 := by
  have hb' : 0 < (b:ℝ) := by exact_mod_cast hb
  have hl : ((v/b:ℤ):ℝ)*b ≤ v := by exact_mod_cast Int.ediv_mul_le v hb.ne'
  have hu : (v:ℝ) < (((v/b:ℤ):ℝ)+1)*b := by exact_mod_cast Int.lt_ediv_add_one_mul_self v hb
  have h₁ := (le_div_iff₀ hb').mpr hl
  have h₂ := (div_lt_iff₀ hb').mpr hu
  constructor <;> linarith

theorem rounded_error {d : ℕ} (hd : 0 < d) {s : ℤ} (hs : 0 < s) (v : ℤ) (N : ℕ) :
    |(v:ℝ)/s/survival N-(rounded d s v N:ℝ)/d| ≤ 1/(d:ℝ) := by
  have hc : 0 < N.centralBinom := Nat.centralBinom_pos _
  have hc' : 0 < (N.centralBinom:ℝ) := by exact_mod_cast hc
  have hs' : 0 < (s:ℝ) := by exact_mod_cast hs
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  obtain ⟨hl,hu⟩ := quotient_error ((d:ℤ)*v*4^N) (b := s*N.centralBinom) (mul_pos hs (by exact_mod_cast hc))
  have hb : Nat.fast_choose (2*N) N = N.centralBinom := by
    rw [← Nat.choose_eq_fast_choose,Nat.centralBinom_eq_two_mul_choose]
  rw [← hb] at hl hu
  change 0 ≤ _-(rounded d s v N:ℝ) at hl
  change _-(rounded d s v N:ℝ) ≤ 1 at hu
  push_cast at hl hu
  rw [hb] at hl hu
  have h : (v:ℝ)/s/survival N-(rounded d s v N:ℝ)/d =
      ((d*v*4^N)/((s:ℝ)*N.centralBinom)-(rounded d s v N:ℝ))/d := by
    rw [survival]
    field_simp
  rw [h,abs_div,abs_of_nonneg hl,abs_of_pos hd']
  exact div_le_div_of_nonneg_right hu hd'.le

/-- Integer discrepancy from the chord of the stored length endpoints. -/
def discrepancy (span i : ℕ) (a left right : ℤ) : ℤ :=
  span*a-(span-i:ℕ)*left-i*right

private theorem chord_error {d span i : ℕ} (hd : 0 < d) (hs : 0 < span) (hi : i ≤ span)
    (a left right : ℤ) :
    |(a:ℝ)/d-chord ((i:ℝ)/span) ((left:ℝ)/d) ((right:ℝ)/d)| =
      |(discrepancy span i a left right:ℝ)|/((span:ℝ)*d) := by
  have hs' : 0 < (span:ℝ) := by exact_mod_cast hs
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have h : (a:ℝ)/d-chord ((i:ℝ)/span) ((left:ℝ)/d) ((right:ℝ)/d) =
      (discrepancy span i a left right:ℝ)/((span:ℝ)*d) := by
    unfold discrepancy chord
    push_cast [Nat.cast_sub hi]
    field_simp
    ring
  rw [h,abs_div,abs_of_pos (mul_pos hs' hd')]

/-- A residual-based amplitude enclosure and one integer chord test give the
error at any intermediate length in either staircase family. -/
theorem amplitude_chord {d span i n δ : ℕ} (hd : 0 < d) (hs : 0 < span) (hi : i ≤ span)
    {s : ℤ} (hs' : 0 < s) (v : List ℤ) (left right : ℤ) {e θ : ℝ} {E : ℕ}
    (ha : |signedAmplitude n δ θ -
      (PowerSeries.coeff (n+δ) (scaledSeries s (Residual.rowPolynomial v))).re/survival (n+δ)| ≤ e)
    (hw : |discrepancy span i (rounded d s (v[n+δ]?.getD 0) (n+δ)) left right| ≤ E) :
    |signedAmplitude n δ θ-chord ((i:ℝ)/span) ((left:ℝ)/d) ((right:ℝ)/d)| ≤
      e+((span:ℝ)+E)/((span:ℝ)*d) := by
  let z := (v[n+δ]?.getD 0)
  let a := rounded d s z (n+δ)
  let base := (z:ℝ)/s/survival (n+δ)
  have hbase : |signedAmplitude n δ θ-base| ≤ e := by
    simpa only [base,z,scaledSeries,PowerSeries.coeff_mk,Residual.coeff_rowPolynomial,
      ← Complex.ofReal_intCast,← Complex.ofReal_div,Complex.ofReal_re] using ha
  have ha' : |base-(a:ℝ)/d| ≤ 1/(d:ℝ) := rounded_error hd hs' z _
  have he : |(discrepancy span i a left right:ℝ)| ≤ (E:ℝ) := by exact_mod_cast hw
  have hsR : 0 < (span:ℝ) := by exact_mod_cast hs
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hc := (chord_error hd hs hi a left right).le.trans
    (div_le_div_of_nonneg_right he (mul_pos hsR hdR).le)
  calc
    _ ≤ |signedAmplitude n δ θ-base| + |base-(a:ℝ)/d| +
      |(a:ℝ)/d-chord ((i:ℝ)/span) ((left:ℝ)/d) ((right:ℝ)/d)| :=
      (abs_sub_le _ ((a:ℝ)/d) _).trans (add_le_add (abs_sub_le _ base _) le_rfl)
    _ ≤ e+1/(d:ℝ)+(E:ℝ)/((span:ℝ)*d) := add_le_add (add_le_add hbase ha') hc
    _ = _ := by field_simp; ring

/-- Integer tests at all intermediate lengths, including a singleton group. -/
def check (first last d : ℕ) (s : ℤ) (v : List ℤ) (left right : ℤ) (E : ℕ) : Bool :=
  (List.range (last-first+1)).all fun i =>
    let N := first+i
    decide (|discrepancy (max 1 (last-first)) i (rounded d s (v[N]?.getD 0) N) left right| ≤ E)

theorem checked_chord {first last d n δ : ℕ} (hd : 0 < d)
    (hlo : first ≤ n+δ) (hhi : n+δ ≤ last) {s : ℤ} (hs : 0 < s)
    (v : List ℤ) (left right : ℤ) {e θ : ℝ} {E : ℕ}
    (h : check first last d s v left right E = true)
    (ha : |signedAmplitude n δ θ -
      (PowerSeries.coeff (n+δ) (scaledSeries s (Residual.rowPolynomial v))).re/survival (n+δ)| ≤ e) :
    let span := max 1 (last-first)
    |signedAmplitude n δ θ-chord (((n+δ-first:ℕ):ℝ)/span) ((left:ℝ)/d) ((right:ℝ)/d)| ≤
      e+((span:ℝ)+E)/((span:ℝ)*d) := by
  apply amplitude_chord hd (by omega) (by omega) hs v left right ha
  have hi := List.all_eq_true.mp h (n+δ-first) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le hlo,decide_eq_true_eq] using hi

end CentralUnimodality.MeshLength
