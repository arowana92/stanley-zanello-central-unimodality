module

public import CentralUnimodality.FourierCertificate
public import Mathlib.Algebra.Polynomial.Inductions

/-! Exact signed Kronecker substitution for a truncated convolution.
A congruence at one integer base verifies all the low coefficient
equations. The magnitude bound prevents carries between signed digits. -/
@[expose] public section

namespace CentralUnimodality

open Polynomial

theorem packed_zero_coefficients {B : ℤ} (hB : 0 < B) (L : ℕ) (P : ℤ[X])
    (hval : B^L ∣ P.eval B) (hcoeff : ∀ i < L, |P.coeff i| < B) :
    ∀ i < L, P.coeff i = 0 := by
  induction L generalizing P with
  | zero => omega
  | succ L ih =>
    have he := congrArg (Polynomial.eval B) (P.X_mul_divX_add)
    simp only [eval_add,eval_mul,eval_X,eval_C] at he
    obtain ⟨v,hv⟩ := hval
    have hd : B ∣ P.coeff 0 := by
      refine ⟨B^L*v-P.divX.eval B,?_⟩
      rw [hv,pow_succ] at he
      linarith only [he]
    have hz : P.coeff 0 = 0 := by
      by_contra h
      have hab : B ∣ |P.coeff 0| := by
        rcases le_total 0 (P.coeff 0) with hp|hn
        · rwa [abs_of_nonneg hp]
        · rw [abs_of_nonpos hn]; exact dvd_neg.mpr hd
      have hle := Int.le_of_dvd (abs_pos.mpr h) hab
      exact (not_le_of_gt (hcoeff 0 (by omega))) hle
    have hv' : B^L ∣ P.divX.eval B := by
      refine ⟨v,?_⟩
      apply mul_left_cancel₀ hB.ne'
      rw [hz,add_zero,hv,pow_succ] at he
      rw [he]
      ring
    intro i hi
    cases i with
    | zero => exact hz
    | succ i =>
      simpa only [coeff_divX] using ih P.divX hv' (fun k hk => by simpa using hcoeff (k+1) (by omega)) i (by omega)

private theorem convolution_magnitude (P V : ℤ[X]) {L : ℕ} {p v : ℤ}
    (hp : ∀ i < L, |P.coeff i| ≤ p) (hv : ∀ i < L, |V.coeff i| ≤ v) {i : ℕ} (hi : i < L) :
    |(P*V).coeff i| ≤ (L:ℤ)*p*v := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  have h := Finset.sum_le_sum (s := Finset.range (i+1)) (fun j hj =>
    show |P.coeff j*V.coeff (i-j)| ≤ p*v by
      rw [abs_mul]
      exact mul_le_mul (hp j (by have := Finset.mem_range.mp hj; omega)) (hv _ (by omega))
        (abs_nonneg _) ((abs_nonneg _).trans (hp i hi)))
  apply h.trans
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Int.natCast_succ]
  rw [mul_assoc (L:ℤ)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi : (i:ℤ)+1 ≤ L)
    (mul_nonneg ((abs_nonneg _).trans (hp i hi)) ((abs_nonneg _).trans (hv i hi)))

/-- At scale s the candidate error array E certifies F/s - (R/s)(V/s).
The integer identity has denominator s² and holds coefficient by
coefficient through L-1, independently of how the candidate was found. -/
theorem packed_residual_coefficients {B s f p v e : ℤ} {L : ℕ} (hB : 0 < B)
    (hs : 0 ≤ s) (F R V E : ℤ[X])
    (hf : ∀ i < L, |F.coeff i| ≤ f) (hp : ∀ i < L, |R.coeff i| ≤ p)
    (hv : ∀ i < L, |V.coeff i| ≤ v) (he : ∀ i < L, |E.coeff i| ≤ e)
    (hsize : s*f+(L:ℤ)*p*v+e < B)
    (hc : B^L ∣ s*F.eval B-R.eval B*V.eval B-E.eval B) :
    ∀ i < L, s*F.coeff i-(R*V).coeff i = E.coeff i := by
  let D := C s*F-R*V-E
  have hc' : B^L ∣ D.eval B := by simpa [D] using hc
  have hz := packed_zero_coefficients hB L D hc' (by
    intro i hi
    simp only [D,coeff_sub,coeff_C_mul]
    apply lt_of_le_of_lt _ hsize
    apply (abs_sub _ _).trans
    apply add_le_add _ (he i hi)
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg hs]
    exact add_le_add (mul_le_mul_of_nonneg_left (hf i hi) hs) (convolution_magnitude R V hp hv hi))
  intro i hi
  exact sub_eq_zero.mp (by simpa [D] using hz i hi)

end CentralUnimodality
