module

public import CentralUnimodality.MomentExtraction

/-! A sum of d Catalan-root powers is determined by its first d
coefficients. Eliminating one exponent with the coefficient recurrence
reduces d by one. The statement also holds with repeated exponents. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

private def eliminate (h : ℤ) (p : Laurent) : Laurent :=
  p.map fun t => (t.1, 2*((t.1:ℚ)-h)*t.2)

private theorem coeff_eliminate (p : Laurent) (h : ℤ) (n : ℕ) :
    coeff n (eval (eliminate h p)) =
      (4*(n:ℚ)-2*h)*coeff n (eval p) - ((n:ℚ)+1)*coeff (n+1) (eval p) := by
  induction p with
  | nil => simp [eliminate,eval]
  | cons t p ih =>
    obtain ⟨k,c⟩ := t
    change coeff n (C (2*((k:ℚ)-h)*c)*rootPower k+eval (eliminate h p)) = _
    rw [eval]
    simp only [map_add,coeff_C_mul,ih]
    linear_combination c*rootPower_coeff_step k n

private theorem coeff_drop (p : Laurent) (h : ℤ) (c : ℚ) (n : ℕ) :
    coeff n (eval (eliminate h p)) =
      (4*(n:ℚ)-2*h)*coeff n (eval ((h,c)::p)) - ((n:ℚ)+1)*coeff (n+1) (eval ((h,c)::p)) := by
  rw [coeff_eliminate,eval]
  simp only [map_add,coeff_C_mul]
  linear_combination c*rootPower_coeff_step h n

theorem coeff_zero_from_block (p : Laurent) (N : ℕ)
    (hz : ∀ n < p.length, coeff (N+n) (eval p) = 0) : ∀ n, coeff (N+n) (eval p) = 0 := by
  suffices H : ∀ m (q : Laurent), q.length = m → (∀ n < m, coeff (N+n) (eval q) = 0) →
      ∀ n, coeff (N+n) (eval q) = 0 by exact H _ p rfl hz
  intro m
  induction m with
  | zero =>
    intro q hq _ n
    obtain rfl : q = [] := List.length_eq_zero_iff.mp hq
    simp [eval]
  | succ m ih =>
    intro q hq hinit
    cases q with
    | nil => simp at hq
    | cons t p =>
      obtain ⟨h,c⟩ := t
      have hp : p.length = m := by simpa only [List.length_cons,Nat.succ.injEq] using hq
      have hsource := ih (eliminate h p) (by simpa [eliminate] using hp) (by
        intro n hn
        rw [coeff_drop,hinit n (by omega),Nat.add_assoc N n 1,hinit (n+1) (by omega)]; ring)
      intro n
      induction n with
      | zero => exact hinit 0 (by omega)
      | succ n ih' =>
        have he := coeff_drop p h c (N+n)
        rw [hsource n,ih',mul_zero,zero_sub] at he
        exact (mul_eq_zero.mp (neg_eq_zero.mp he.symm)).resolve_left (by positivity)

theorem eval_zero_of_initial (p : Laurent) (hz : ∀ n < p.length, coeff n (eval p) = 0) :
    eval p = 0 := by
  apply PowerSeries.ext
  intro n
  simpa only [Nat.zero_add,map_zero] using coeff_zero_from_block p 0 (by simpa only [Nat.zero_add] using hz) n

theorem eval_eq_of_initial (p q : Laurent)
    (h : ∀ n < (add p (scaleShift (-1) 0 q)).length, coeff n (eval p) = coeff n (eval q)) :
    eval p = eval q := by
  let d := add p (scaleShift (-1) 0 q)
  have he : eval d = eval p-eval q := by simp [d,eval_add,eval_scaleShift,rootPower_zero,sub_eq_add_neg]
  apply sub_eq_zero.mp
  rw [← he]
  apply eval_zero_of_initial
  intro n hn
  rw [he,map_sub,h n hn,sub_self]

end CentralUnimodality.Laurent
