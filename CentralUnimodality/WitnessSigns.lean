module

public import CentralUnimodality.NormalizedCells

/-! Soundness of the witness bound. Evaluate the polynomials at 1/N and
linearly interpolate between the two checked Wallis bounds. -/
@[expose] public section

namespace CentralUnimodality.Witness

open Laurent

noncomputable def polyExpectation (f : ℕ → ℝ) : ℕ → List ℚ → ℝ
  | _, [] => 0
  | r, c::cs => (c:ℝ)*f r + polyExpectation f (r+1) cs

private theorem buildPair_sound (F : ℕ → ℝ) (M : ℕ → Option (List ℚ)) (x s : ℝ)
    (cs : List ℚ) (r : ℕ) {pair : Pair} (hp : buildPair M r cs = some pair)
    (hF : ∀ j, r ≤ j → j < r+cs.length → ∀ q, M j = some q →
      F j = (if j%2 = 0 then 1 else s)*horner x q) :
    polyExpectation F r cs = horner x pair.1 + s*horner x pair.2 := by
  induction cs generalizing r pair with
  | nil =>
    obtain rfl : pair = ([],[]) := by simpa [buildPair] using hp.symm
    simp [polyExpectation,horner]
  | cons c cs ih =>
    cases hm : M r with
    | none => simp [buildPair,hm] at hp
    | some q =>
      cases htail : buildPair M (r+1) cs with
      | none => simp [buildPair,hm,htail] at hp
      | some v =>
        have tail := ih (r+1) htail (fun j hj hj' q hq =>
          hF j (by omega) (by simp only [List.length_cons]; omega) q hq)
        have head := hF r le_rfl (by simp) q hm
        rcases v with ⟨a,b⟩
        by_cases hpar : r%2 = 0
        · obtain rfl : pair = (addCoeffs (q.map (c*·)) a,b) := by simpa [buildPair,hm,htail,hpar] using hp.symm
          rw [polyExpectation,head,ite_eq_left hpar,tail,horner_add,horner_scale]
          simp; ring
        · obtain rfl : pair = (a,addCoeffs (q.map (c*·)) b) := by simpa [buildPair,hm,htail,hpar] using hp.symm
          rw [polyExpectation,head,ite_eq_right hpar,tail,horner_add,horner_scale]
          ring

theorem familyPair_sound (v : Data) (n δ : ℕ) (hδ : δ ≤ 1) (hn : 0 < n+δ)
    {pair : Pair} (hp : familyPair δ v = some pair) :
    polyExpectation (normalizedCell n δ) 0 (coefficients v.B v.t v.roots) =
      horner ((n+δ:ℕ):ℝ)⁻¹ pair.1 + wallisFactor (n+δ)*horner ((n+δ:ℕ):ℝ)⁻¹ pair.2 := by
  let cs := coefficients v.B v.t v.roots
  let T := tables (cs.length-1)
  let R := rawNumerator (lookup T.1) (lookup T.2) δ
  let P (i : ℕ) := ((List.range cs.length).map R)[i]?.getD []
  apply buildPair_sound _ (momentPolynomial P δ) _ _ cs 0 hp
  intro j _ hj q hq
  apply normalizedCell_exact hn _ hq
  intro i hi
  have hil : i < cs.length := by omega
  have he : P i = R i := by simp [P,hil]
  rw [he]
  exact rawNumerator_exact (cs.length-1) n δ i hδ (by omega)

theorem checkPair_sound (v : Data) {n δ : ℕ} (hδ : δ ≤ 1) (hn : 96 ≤ n+δ)
    {ε : ℚ} (h : checkPair v δ ε = true) :
    polyExpectation (normalizedCell n δ) 0 (coefficients v.B v.t v.roots) ≤ -(ε:ℝ) := by
  cases hp : familyPair δ v with
  | none => simp [checkPair,hp] at h
  | some pair =>
    rw [familyPair_sound v n δ hδ (by omega) hp]
    simp only [checkPair,hp,Bool.and_eq_true] at h
    let x := ((n+δ:ℕ):ℝ)⁻¹
    have hi : (96:ℝ) ≤ (n+δ:ℕ) := by exact_mod_cast hn
    have bound (u : List ℚ) (c : ℚ) (hu : upperTest pair u c ε = true) :
        horner x pair.1 + ((c:ℝ)*horner x u)*horner x pair.2 ≤ -(ε:ℝ) := by
      have hx : x ≤ ((1/96:ℚ):ℝ) := by simpa [x] using inv_anti₀ (by norm_num : 0 < (96:ℝ)) hi
      have hh := nonpositive_sound (by dsimp [x]; positivity : 0 ≤ x) hx _ hu
      rw [horner_add,horner_add,horner_scale,horner_times] at hh
      simp only [horner,mul_zero,add_zero] at hh
      linarith only [hh]
    obtain ⟨hl,hr⟩ := Wallis.uniform hn
    by_cases hs : 0 ≤ horner x pair.2
    · exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right hr hs)).trans (bound _ _ h.2)
    · exact (add_le_add le_rfl (mul_le_mul_of_nonpos_right hl (le_of_not_ge hs))).trans (bound _ _ h.1)

end CentralUnimodality.Witness
