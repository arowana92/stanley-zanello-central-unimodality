module

public import CentralUnimodality.WitnessPolynomial

/-! Rational power-basis certificates on a nonnegative interval. The sign
test retains the constant exactly and bounds positive nonconstant terms at
the right endpoint. Initial zero coefficients contribute factors of x. -/
@[expose] public section

namespace CentralUnimodality.Witness

def times (p q : List ℚ) : List ℚ := match p with
  | [] => []
  | a::t => addCoeffs (q.map (a*·)) (0::times t q)

theorem horner_times {R : Type*} [Field R] [CharZero R] (x : R) (p q : List ℚ) :
    horner x (times p q) = horner x p * horner x q := by
  induction p with
  | nil => simp [times,horner]
  | cons a p ih => rw [times,horner_add,horner_scale,horner,ih,horner]; simp; ring

def power (p : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n+1 => times (power p n) p

theorem horner_power {R : Type*} [Field R] [CharZero R] (x : R) (p : List ℚ) (n : ℕ) :
    horner x (power p n) = (horner x p)^n := by
  induction n with
  | zero => simp [power,horner]
  | succ n ih => rw [power,horner_times,ih,pow_succ]

def positiveSum (b : ℚ) : List ℚ → ℚ
  | [] => 0
  | c::t => max c 0 + b*positiveSum b t

theorem positiveSum_nonneg {b : ℚ} (hb : 0 ≤ b) (t : List ℚ) : 0 ≤ positiveSum b t := by
  induction t with
  | nil => rfl
  | cons c t ih => exact add_nonneg (le_max_right ..) (mul_nonneg hb ih)

theorem horner_le_positiveSum {b : ℚ} {x : ℝ} (hx : 0 ≤ x) (hb : x ≤ b) (t : List ℚ) :
    horner x t ≤ (positiveSum b t:ℝ) := by
  induction t with
  | nil => simp [horner,positiveSum]
  | cons c t ih =>
    simp only [horner,positiveSum,Rat.cast_add,Rat.cast_mul,Rat.cast_max,Rat.cast_zero]
    refine add_le_add (le_max_left ..) ((mul_le_mul_of_nonneg_left ih hx).trans ?_)
    apply mul_le_mul_of_nonneg_right hb
    have hb' : (0:ℚ) ≤ b := by exact_mod_cast hx.trans hb
    exact_mod_cast positiveSum_nonneg hb' t

def nonpositive (b : ℚ) : List ℚ → Bool
  | [] => true
  | c::t => if c = 0 then nonpositive b t else decide (c + b*positiveSum b t ≤ 0)

theorem nonpositive_sound {b : ℚ} {x : ℝ} (hx : 0 ≤ x) (hb : x ≤ b) (p : List ℚ)
    (h : nonpositive b p = true) : horner x p ≤ 0 := by
  induction p with
  | nil => simp [horner]
  | cons c t ih =>
    by_cases hc : c = 0
    · subst c
      simpa only [horner,Rat.cast_zero,zero_add] using
        mul_nonpos_of_nonneg_of_nonpos hx (ih (by simpa [nonpositive] using h))
    · have ht : c + b*positiveSum b t ≤ 0 := by simpa [nonpositive,hc] using h
      have hh : (c:ℝ)+b*(positiveSum b t:ℝ) ≤ 0 := by exact_mod_cast ht
      change (c:ℝ) + x*horner x t ≤ 0
      refine (add_le_add (le_refl (c:ℝ)) ((mul_le_mul_of_nonneg_left (horner_le_positiveSum hx hb t) hx).trans ?_)).trans hh
      apply mul_le_mul_of_nonneg_right hb
      have hb' : (0:ℚ) ≤ b := by exact_mod_cast hx.trans hb
      exact_mod_cast positiveSum_nonneg hb' t

/-- Clear the denominator of p(x/(1+x)) using the list length, even when
the input has a trailing zero coefficient. -/
def shiftedCoeffs : List ℚ → List ℚ
  | [] => []
  | c::t => addCoeffs ((power [1,1] t.length).map (c*·)) (0::shiftedCoeffs t)

theorem horner_shifted {x : ℝ} (hx : 0 ≤ x) (p : List ℚ) :
    horner x (shiftedCoeffs p) = (1+x)^(p.length-1)*horner (x/(1+x)) p := by
  induction p with
  | nil => simp [shiftedCoeffs,horner]
  | cons c t ih =>
    rw [shiftedCoeffs,horner_add,horner_scale,horner_power]
    simp only [horner,ih, List.length_cons, Nat.add_sub_cancel, Rat.cast_one, Rat.cast_zero,
      mul_zero, add_zero, mul_one, zero_add]
    cases t with
    | nil => simp [horner]
    | cons b t =>
      simp only [List.length_cons,Nat.add_sub_cancel,pow_succ]
      field_simp

def ratioPolynomial (p : List ℚ) : List ℚ :=
  let e := p.length-1
  addCoeffs (times (power [1,1] (2*e+1)) (times p p))
    ((times [1,1,1/4] (times (shiftedCoeffs p) (shiftedCoeffs p))).map ((-1)*·))

theorem horner_ratioPolynomial {x : ℝ} (hx : 0 ≤ x) (p : List ℚ) :
    horner x (ratioPolynomial p) = (1+x)^(2*(p.length-1)) *
      ((1+x)*(horner x p)^2-(1+x/2)^2*(horner (x/(1+x)) p)^2) := by
  simp only [ratioPolynomial,horner_add,horner_scale,horner_times,horner_power,horner_shifted hx,
    horner,Rat.cast_one,Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat, mul_zero,
    add_zero,mul_one,pow_succ]
  rw [Nat.mul_comm 2, pow_mul]
  ring

end CentralUnimodality.Witness
