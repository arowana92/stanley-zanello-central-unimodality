module

public import CentralUnimodality.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Arithmetic on fixed-width digits used by the rounded endpoint recurrence. -/
@[expose] public section

namespace CentralUnimodality.EndpointDeficit

theorem digit_add {b x y i : ℕ} (h : ∀ j≤i, digit b x j + digit b y j < 2^b) :
    digit b (x+y) i = digit b x i + digit b y i := by
  induction i generalizing x y with
  | zero =>
    have lo := h 0 (Nat.zero_le _)
    simp only [digit_zero] at lo ⊢
    rw [Nat.add_mod,Nat.mod_eq_of_lt lo]
  | succ i IH =>
    have lo := h 0 (Nat.zero_le _)
    simp only [digit_zero] at lo
    have e : (x+y) >>> b = (x >>> b) + (y >>> b) := by
      simp only [Nat.shiftRight_eq_div_pow,Nat.add_div (Nat.two_pow_pos b),
        ite_eq_right (Nat.not_le.mpr lo),Nat.add_zero]
    rw [digit_succ,digit_succ,digit_succ,e]
    apply IH
    intro j hj
    simpa only [digit_succ] using h (j+1) (by omega)

theorem digit_right (b x s i : ℕ) : digit b (x >>> (b*s)) i = digit b x (s+i) := by
  simp only [digit,Nat.shiftRight_add,Nat.mul_add]

theorem digit_left (b x s i : ℕ) :
    digit b (x <<< (b*s)) i = if s≤i then digit b x (i-s) else 0 := by
  split
  next h =>
    unfold digit
    rw [show b*i=b*s+b*(i-s) by rw [← Nat.mul_add]; congr 1; omega,
      Nat.shiftRight_add,Nat.shiftLeft_shiftRight]
  next h =>
    have e : b*s = (b*(s-i-1)+b)+b*i := by
      rw [← Nat.mul_succ,← Nat.mul_add]; congr 1; omega
    unfold digit
    rw [e,Nat.shiftLeft_add,Nat.shiftLeft_shiftRight,Nat.shiftLeft_add,Nat.shiftLeft_eq]
    exact Nat.mul_mod_left _ _

private def repeatBase (B u : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => u+B*repeatBase B u n

/-- The first `n` digits equal `u`. Higher digits vanish. -/
def repeatDigit (b n u : ℕ) : ℕ :=
  (((1 <<< (b*n))-1)/((1 <<< b)-1))*u

private theorem repeatDigit_eq {b : ℕ} (hb : 0<b) (n u : ℕ) :
    repeatDigit b n u = repeatBase (2^b) u n := by
  let B : ℕ := 2^b
  have hB : 1<B := Nat.one_lt_pow (by omega) (by decide)
  have H (k : ℕ) : (B-1)*repeatBase B 1 k+1=B^k := by
    induction k with
    | zero => simp [repeatBase]
    | succ k ih =>
      simp only [repeatBase,pow_succ']
      nlinarith only [congrArg (B*·) ih,show B-1+1=B by omega]
  have he : (B^n-1)/(B-1)=repeatBase B 1 n := by
    apply Nat.div_eq_of_eq_mul_right (by omega)
    have := H n
    omega
  have scale (k : ℕ) : repeatBase B 1 k*u=repeatBase B u k := by
    induction k with
    | zero => simp [repeatBase]
    | succ k ih => simp only [repeatBase,Nat.add_mul,Nat.one_mul,Nat.mul_assoc,ih]
  simp only [repeatDigit,Nat.shiftLeft_eq,Nat.one_mul,pow_mul]
  exact he ▸ scale n

theorem digit_repeat {b u : ℕ} (hb : 0<b) (hu : u<2^b) (n i : ℕ) :
    digit b (repeatDigit b n u) i = if i<n then u else 0 := by
  rw [repeatDigit_eq hb]
  induction n generalizing i with
  | zero => simp [repeatBase,digit]
  | succ n ih =>
    cases i with
    | zero => simp [digit_zero,repeatBase,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hu]
    | succ i =>
      rw [digit_succ,repeatBase,Nat.shiftRight_eq_div_pow,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt hu,Nat.zero_add,ih]
      simp

theorem digit_half_mask (w n z i : ℕ) :
    digit (w+1) ((z >>> 1) &&& repeatDigit (w+1) n (2^w-1)) i =
      if i<n then digit (w+1) z i / 2 else 0 := by
  have hg : 2^w-1<2^(w+1) := by rw [pow_succ]; have := Nat.two_pow_pos w; omega
  have distribute (x y : ℕ) : digit (w+1) (x &&& y) i =
      digit (w+1) x i &&& digit (w+1) y i := by
    simp only [digit,Nat.shiftRight_and_distrib,Nat.and_mod_two_pow]
  rw [distribute,digit_repeat (by omega) hg]
  split
  next =>
    rw [Nat.and_two_pow_sub_one_eq_mod]
    unfold digit
    rw [← Nat.shiftRight_add,Nat.add_comm 1,Nat.shiftRight_add,
      Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))]
    rw [Nat.shiftRight_eq_div_pow _ 1,show (2:ℕ)^1=2 by decide,
      pow_succ',Nat.mod_mul_right_div_self]
  next => simp

end CentralUnimodality.EndpointDeficit
