module

public import CentralUnimodality.AlternatingLift
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Coefficient functionals on the actual diagonal coinvariant quotient.
Substitute yᵢ=tᵢ and xᵢ=tᵢ U(tᵢ), antisymmetrize, and extract the coefficient
of the staircase exponent vector (0,1,...,n-1). -/
@[expose] public section

namespace CentralUnimodality.Polarization
open MvPolynomial

variable {n : ℕ}

abbrev SinglePoly (n : ℕ) := MvPolynomial (Fin n) ℚ

noncomputable def curve (U : Polynomial ℚ) : Poly n →ₐ[ℚ] SinglePoly n :=
  aeval fun z => if z.1 then X z.2 else X z.2 * Polynomial.aeval (X z.2) U

@[simp] theorem curve_X (U : Polynomial ℚ) (b : Bool) (i : Fin n) :
    curve U (X (b,i)) = if b then X i else X i * Polynomial.aeval (X i) U := by
  simp [curve]

theorem curve_rename (U : Polynomial ℚ) (σ : Perm n) (p : Poly n) :
    curve U (rename (reindex σ) p) = rename σ (curve U p) := by
  have hx (i : Fin n) : rename σ (Polynomial.aeval (X i : SinglePoly n) U) =
      Polynomial.aeval (X (σ i) : SinglePoly n) U := by
    rw [← Polynomial.aeval_algHom_apply,rename_X]
  induction p using MvPolynomial.induction_on with
  | C c => simp [curve]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i ih =>
    obtain ⟨b,i⟩ := i
    cases b <;> simp [reindex,ih,hx]

theorem constant_curve (U : Polynomial ℚ) (p : Poly n) :
    constantCoeff (curve U p) = constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [curve]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i _ => obtain ⟨b,i⟩ := i; cases b <;> simp

noncomputable def stairExponent (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (i:ℕ)

@[simp] theorem stairExponent_apply (i : Fin n) : stairExponent n i = i := rfl

private theorem fixed_below_stair {e : Fin n →₀ ℕ} (hle : e ≤ stairExponent n)
    (hi : Function.Injective e) : e = stairExponent n := by
  let f : Fin n → Fin n := fun i => ⟨e i,lt_of_le_of_lt (hle i) i.isLt⟩
  have hf : Function.Injective f := fun i j h => hi (congrArg Fin.val h)
  let σ := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  have hsum := Equiv.sum_comp σ (fun i : Fin n => (i:ℕ))
  change ∑ i : Fin n, e i = ∑ i : Fin n, (i:ℕ) at hsum
  ext i
  by_contra hn
  have hlt : e i < (i:ℕ) := lt_of_le_of_ne (hle i) hn
  have h := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hle j)
    ⟨i,Finset.mem_univ _,hlt⟩
  simp only [stairExponent_apply] at h
  omega

private theorem distinct_single {q : SinglePoly n} (ha : ∀ σ : Perm n, rename σ q = (σ.sign:ℤ) • q)
    {e : Fin n →₀ ℕ} (hm : q.coeff e ≠ 0) : Function.Injective e := by
  intro i j he
  by_contra hn
  let σ := Equiv.swap i j
  have hfixed : e.mapDomain σ = e := by
    ext k
    have h := Finsupp.mapDomain_apply_of_injective σ.injective e (σ k)
    rw [show σ (σ k) = k by simp [σ]] at h
    rw [h]
    by_cases h₁ : k=i
    · subst k; simpa [σ] using he.symm
    by_cases h₂ : k=j
    · subst k; simpa [σ] using he
    · rw [show σ k = k from Equiv.swap_apply_of_ne_of_ne h₁ h₂]
  have h := coeff_rename_mapDomain σ σ.injective q e
  rw [ha σ,hfixed,show σ.sign = -1 from Equiv.Perm.sign_swap hn] at h
  simp only [Units.val_neg,Units.val_one,neg_smul,one_smul,coeff_neg] at h
  exact hm (by linarith)

/-- A factor with zero constant term contributes no staircase coefficient
when the other factor is alternating. -/
theorem stair_coeff_mul {p q : SinglePoly n} (hp : constantCoeff p = 0)
    (hq : ∀ σ : Perm n, rename σ q = (σ.sign:ℤ) • q) :
    (p*q).coeff (stairExponent n) = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a,b⟩ hab
  have h : a+b=stairExponent n := Finset.mem_antidiagonal.mp hab
  by_cases hb : q.coeff b = 0
  · simp [hb]
  have hle : b ≤ stairExponent n := h ▸ le_add_self
  have he := fixed_below_stair hle (distinct_single hq hb)
  have ha : a=0 := by rw [← he,add_eq_right] at h; exact h
  simp [ha,← constantCoeff_eq,hp]

/-- The signed coefficient on an arbitrary bivariate polynomial. -/
noncomputable def curveProbe (U : Polynomial ℚ) : Poly n →ₗ[ℚ] ℚ where
  toFun p := (curve U (signedSum p)).coeff (stairExponent n)
  map_add' p q := by simp [signedSum,smul_add,Finset.sum_add_distrib]
  map_smul' c p := by simp [signedSum,smul_comm (M := ℤ) (N := ℚ),← Finset.smul_sum]

private theorem probe_product (U : Polynomial ℚ) {p : Poly n} (hp : positiveInvariant p) (q : Poly n) :
    curveProbe U (q*p) = 0 := by
  have h : signedSum (q*p) = p*signedSum q := by
    simp only [signedSum,map_mul,hp.2,← smul_mul_assoc,Finset.sum_mul,mul_comm p]
  change (curve U (signedSum (q*p))).coeff _ = _
  rw [h,map_mul]
  apply stair_coeff_mul ((constant_curve U p).trans hp.1)
  intro σ
  rw [← curve_rename,(sum_alternating q) σ,map_zsmul]

theorem probe_kills_relations (U : Polynomial ℚ) {p : Poly n} (hp : p ∈ relations n) :
    curveProbe U p = 0 := by
  change p ∈ Submodule.span (Poly n) {q | positiveInvariant q} at hp
  suffices ∀ h : Poly n, curveProbe U (h*p) = 0 by simpa using this 1
  induction hp using Submodule.span_induction with
  | mem p hp => exact probe_product U hp
  | zero => simp
  | add p q _ _ hp hq => intro h; rw [mul_add,map_add,hp,hq,add_zero]
  | smul c p _ ih => intro h; simpa only [smul_eq_mul,← mul_assoc] using ih (h*c)

/-- Every rational curve gives a linear functional on the quotient used
in the Dyck Hilbert specialization. -/
noncomputable def quotientProbe (U : Polynomial ℚ) : (Poly n ⧸ relations n) →ₗ[ℚ] ℚ :=
  (relations n).liftQ (curveProbe U) fun _ hp => probe_kills_relations U hp

@[simp] theorem quotientProbe_mk (U : Polynomial ℚ) (p : Poly n) :
    quotientProbe U ((relations n).mkQ p) = curveProbe U p := rfl

end CentralUnimodality.Polarization
