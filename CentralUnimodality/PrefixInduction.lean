module

public import CentralUnimodality.IntervalProduct

/-! Transfer an ordinary Dyck interval decomposition and reflected comparisons
of smaller odd-part rows to the nondecreasing prefix of each staircase. -/
@[expose] public section

namespace CentralUnimodality

open Polynomial

def ReflectedCoeffs (P : Polynomial ℕ) (T : ℤ) : Prop :=
  ∀ i j : ℕ, i < j → (i:ℤ)+j ≤ T → P.coeff i ≤ P.coeff j

def IntervalDecomposition (Q : Polynomial ℕ) (E : ℤ) : Prop :=
  ∃ intervals : List (ℕ × ℕ),
    Q = (intervals.map fun p => intervalPoly p.1 p.2).sum ∧
    ∀ p ∈ intervals, E ≤ 2*(p.1:ℤ)+p.2

theorem intervalPoly_shift (s a w : ℕ) : (X:Polynomial ℕ)^s * intervalPoly a w = intervalPoly (s+a) w := by
  rw [intervalPoly, Finset.mul_sum, intervalPoly]
  apply Finset.sum_congr rfl
  intro t _
  rw [← pow_add, Nat.add_assoc]

theorem shifted_product_step {P Q : Polynomial ℕ} {T E : ℤ} (hr : ReflectedCoeffs P T)
    (hd : IntervalDecomposition Q E) (s k : ℕ) (hk : 2*(k:ℤ)+1 ≤ T+2*s+E) :
    (Q * (X^s * P)).coeff k ≤ (Q * (X^s * P)).coeff (k+1) := by
  obtain ⟨L,rfl,hL⟩ := hd
  induction L with
  | nil => simp
  | cons p L ih =>
    have hstep := interval_product_step hr (s+p.1) p.2 k
      (by have := hL p List.mem_cons_self; push_cast; omega)
    have hmul : intervalPoly p.1 p.2 * (X^s*P) = P*intervalPoly (s+p.1) p.2 := by
      rw [← intervalPoly_shift]
      ac_rfl
    simp only [List.map_cons, List.sum_cons, add_mul, coeff_add]
    exact add_le_add (hmul ▸ hstep) (ih fun t ht => hL t (List.mem_cons_of_mem _ ht))

theorem interval_decomposition_step {Q : Polynomial ℕ} {E : ℤ} (hd : IntervalDecomposition Q E)
    (k : ℕ) (hk : 2*(k:ℤ)+1 ≤ E) : Q.coeff k ≤ Q.coeff (k+1) := by
  have hr : ReflectedCoeffs (1:Polynomial ℕ) 0 := by intro i j hij ht; omega
  simpa using shifted_product_step hr hd 0 k (by simpa using hk)

theorem oddPart_prefix_step (n k : ℕ) (E T : ℕ → ℤ)
    (hD : ∀ i ≤ n+1, IntervalDecomposition (dyckPoly i) (E i))
    (hB : ∀ h ≤ n, ReflectedCoeffs (ballotPoly (2*h)) (T h))
    (h₀ : 2*(k:ℤ)+1 ≤ E (n+1))
    (hcut : ∀ i ≤ n, 2*(k:ℤ)+1 ≤ T (n-i)+2*(2*((n-i:ℕ):ℤ)+1)+E (i+1)) :
    (ballotPoly (2*(n+1))).coeff k ≤ (ballotPoly (2*(n+1))).coeff (k+1) := by
  have he := stump_convolution (X:Polynomial ℕ) n
  change ballotPoly (2*(n+1)) = dyckPoly (n+1) + ∑ i ∈ Finset.range (n+1),
    dyckPoly (i+1) * (X^(2*(n-i)+1)*ballotPoly (2*(n-i))) at he
  simp only [he, coeff_add, finsetSum_coeff]
  apply add_le_add (interval_decomposition_step (hD _ le_rfl) k h₀)
  apply Finset.sum_le_sum
  intro i hi
  have h := Finset.mem_range.mp hi
  apply shifted_product_step (hB _ (Nat.sub_le ..)) (hD _ (by omega))
  simpa using hcut i (by omega)

theorem evenPart_prefix_step (n k : ℕ) (E T : ℕ → ℤ)
    (hD : ∀ i ≤ n, IntervalDecomposition (dyckPoly i) (E i))
    (hB : ∀ h ≤ n, ReflectedCoeffs (ballotPoly (2*h)) (T h))
    (hcut : ∀ i ≤ n, 2*(k:ℤ)+1 ≤ T (n-i)+2*((n-i:ℕ):ℤ)+E i) :
    (ballotPoly (2*n+1)).coeff k ≤ (ballotPoly (2*n+1)).coeff (k+1) := by
  have he := odd_ballot_convolution (X:Polynomial ℕ) n
  change ballotPoly (2*n+1) = ∑ i ∈ Finset.range (n+1),
    dyckPoly i * (X^(n-i)*ballotPoly (2*(n-i))) at he
  simp only [he, finsetSum_coeff]
  apply Finset.sum_le_sum
  intro i hi
  have h := Finset.mem_range.mp hi
  exact shifted_product_step (hB _ (Nat.sub_le ..)) (hD _ (by omega)) _ _ (hcut i (by omega))

end CentralUnimodality
