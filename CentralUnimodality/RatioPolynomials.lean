module

public import CentralUnimodality.RootCoefficients
public import CentralUnimodality.PolynomialBounds

/-! Negative powers of the Catalan root reduce, after scaling, to
polynomials in the reciprocal size. Even negative exponents carry one
common factor, independent of the exponent. -/
@[expose] public section

namespace CentralUnimodality

open Witness

theorem rootRatio_lower_two (h : ℤ) (n : ℕ) :
    (h:ℚ)*rootRatio (h-2) n = (h-2*(n:ℚ))*rootRatio h n := by
  induction n with
  | zero => simp [rootRatio]
  | succ n ih =>
    rw [rootRatio,rootRatio,Int.cast_sub,Int.cast_ofNat,Nat.cast_succ]
    field_simp
    linear_combination (2*(n:ℚ)-h+2)*ih

theorem rootRatio_neg_one (n : ℕ) : rootRatio (-1) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rootRatio,ih]; push_cast; field_simp; ring

theorem rootRatio_neg_two (n : ℕ) : (n.centralBinom:ℚ)*rootRatio (-2) n = 4^n := by
  induction n with
  | zero => simp [rootRatio]
  | succ n ih =>
    have hc : ((n:ℚ)+1)*(n+1).centralBinom = 2*(2*(n:ℚ)+1)*n.centralBinom := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    rw [rootRatio,pow_succ,← ih]
    push_cast
    field_simp
    linear_combination 2*rootRatio (-2) n*hc

/-- For p = 1 and 2 these are the successive rising factors of the two
parities. Each factor is already written in the reciprocal-size variable. -/
def reciprocalFactors (p : ℕ) : ℕ → List ℚ
  | 0 => [1]
  | a+1 => times (reciprocalFactors p a) [2/(p+2*(a:ℚ)),1]

theorem rootRatio_reciprocal (p : ℕ) (hp : 0 < p) {n : ℕ} (hn : 0 < n) (a : ℕ) :
    rootRatio (-((p:ℤ)+2*a)) n =
      rootRatio (-(p:ℤ)) n * (n:ℚ)^a * horner (n:ℚ)⁻¹ (reciprocalFactors p a) := by
  induction a with
  | zero => simp [reciprocalFactors,horner]
  | succ a ih =>
    have h := rootRatio_lower_two (-((p:ℤ)+2*a)) n
    have h' : -((p:ℤ)+2*(a+1:ℕ)) = -((p:ℤ)+2*a)-2 := by omega
    rw [h',reciprocalFactors,horner_times,pow_succ]
    have hp' : 0 < (p:ℚ) := by exact_mod_cast hp
    have hn' : (n:ℚ) ≠ 0 := by positivity
    have hd : (p:ℚ)+2*a ≠ 0 := by positivity
    rw [ih] at h
    push_cast at h
    simp only [horner,Rat.cast_id, mul_zero,add_zero,mul_one]
    generalize horner (n:ℚ)⁻¹ (reciprocalFactors p a) = v at *
    field_simp
    linear_combination -h

end CentralUnimodality
