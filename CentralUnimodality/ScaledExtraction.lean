module

public import CentralUnimodality.RatioPolynomials
public import CentralUnimodality.CellMoments

/-! Check the support of a Laurent numerator and extract its polynomial
in 1/N. The parity and degree tests are part of the proved implication. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open Witness

def pad (p : List ℚ) : ℕ → List ℚ
  | 0 => p
  | k+1 => 0::pad p k

theorem horner_pad {R : Type*} [Field R] [CharZero R] (x : R) (p : List ℚ) (k : ℕ) :
    horner x (pad p k) = x^k * horner x p := by
  induction k with
  | zero => simp [pad]
  | succ k ih => simp only [pad,horner, Rat.cast_zero,zero_add,ih,pow_succ]; ring

def extractPolynomial (t d : ℕ) : Laurent → Option (List ℚ)
  | [] => some []
  | (h,c)::p => do
    let q ← extractPolynomial t d p
    if h = 0 then return q
    let a := (-h-(t:ℤ)).toNat / 2
    if h = -((t:ℤ)+2*a) ∧ a ≤ d then
      return addCoeffs (pad ((reciprocalFactors t a).map (c*·)) (d-a)) q
    else none

private theorem rootRatio_zero_succ (n : ℕ) : rootRatio 0 (n+1) = 0 := by
  induction n with
  | zero => norm_num [rootRatio]
  | succ n ih => rw [rootRatio,ih,zero_mul]

theorem extractPolynomial_exact {t d n : ℕ} (ht : 0 < t) (hn : 0 < n) (p : Laurent)
    {q : List ℚ} (hq : extractPolynomial t d p = some q) :
    ratioSum n p = rootRatio (-(t:ℤ)) n * (n:ℚ)^d * horner (n:ℚ)⁻¹ q := by
  induction p generalizing q with
  | nil => obtain rfl : q = [] := by simpa [extractPolynomial] using hq.symm
           simp [ratioSum,horner]
  | cons u p ih =>
    obtain ⟨h,c⟩ := u
    cases he : extractPolynomial t d p with
    | none => simp [extractPolynomial,he] at hq
    | some v =>
      have hp := ih he
      by_cases hz : h = 0
      · subst h
        obtain rfl : v = q := by simpa [extractPolynomial,he] using hq
        obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
        simpa only [ratioSum,rootRatio_zero_succ,mul_zero,zero_add] using hp
      · let a := (-h-(t:ℤ)).toNat/2
        rw [extractPolynomial,he] at hq
        change (if h = 0 then some v else if h = -((t:ℤ)+2*a) ∧ a ≤ d then
          some (addCoeffs (pad ((reciprocalFactors t a).map (c*·)) (d-a)) v) else none) = some q at hq
        rw [ite_eq_right hz] at hq
        by_cases ha : h = -((t:ℤ)+2*a) ∧ a ≤ d
        · have hq' : addCoeffs (pad ((reciprocalFactors t a).map (c*·)) (d-a)) v = q := by
            exact Option.some.inj ((ite_eq_left ha).symm.trans hq)
          rw [← hq',ratioSum,ha.1,rootRatio_reciprocal t ht hn a,hp,horner_add,horner_pad,horner_scale]
          have hpow : (n:ℚ)^d * ((n:ℚ)⁻¹)^(d-a) = (n:ℚ)^a := by
            have heq : d = a+(d-a) := by omega
            calc
              _ = ((n:ℚ)^a * n^(d-a)) * ((n:ℚ)^(d-a))⁻¹ := by rw [← pow_add,← heq,inv_pow]
              _ = _ := by rw [mul_assoc,mul_inv_cancel₀ (by positivity),mul_one]
          linear_combination -(rootRatio (-(t:ℤ)) n*c*horner (n:ℚ)⁻¹ (reciprocalFactors t a))*hpow
        · simp only [ite_eq_right ha,reduceCtorEq] at hq

end CentralUnimodality.Laurent
