module

public import CentralUnimodality.WindowInduction
public import CentralUnimodality.MidpointTail

/-! The central estimates need only reach the midpoint. Unimodality of the
earlier odd-part rows supplies the entire remaining rank interval. -/
@[expose] public section

namespace CentralUnimodality

def CentralToMidpoint (n δ : ℕ) : Prop :=
  UnimodalOn (fun k => rankCount (2*n+δ) (n*(n+δ)-k)) (centralStart n (2*n+δ)) (n*(n+δ)/2)

private theorem extend_right {f : ℕ → ℕ} {a b d : ℕ} (hu : UnimodalOn f a b) (hd : b ≤ d)
    (hr : ∀ k ≥ b, k < d → f (k+1) ≤ f k) : UnimodalOn f a d := by
  obtain ⟨p,ha,hb,hinc,hdec⟩ := hu
  refine ⟨p,ha,hb.trans hd,hinc,?_⟩
  intro k hk hkd
  by_cases hkb : k < b
  · exact hdec k hk hkb
  · exact hr k (by omega) hkd

theorem suffix_from_midpoint {n δ : ℕ} (hn : 96 ≤ n) (hδ : δ ≤ 1) (hc : CentralToMidpoint n δ)
    (hu : ∀ h, h < n ∨ (δ = 1 ∧ h = n) → UnimodalOn (rankCount (2*h)) 0 (h*h)) : CentralSuffix n δ := by
  apply extend_right hc (Nat.div_le_self ..)
  intro k hk hkd
  rw [← ballotPoly_coeff n δ (k+1) hδ (by omega),← ballotPoly_coeff n δ k hδ hkd.le]
  rcases (by omega : δ = 0 ∨ δ = 1) with rfl|rfl
  · cases n with
    | zero => omega
    | succ n =>
      simp only [Nat.add_zero] at hk ⊢
      exact odd_midpoint_tail hn hk (fun h hh => hu h (Or.inl (by omega)))
  · have hmid : n*n/2 ≤ k := (Nat.div_le_div_right (Nat.mul_le_mul_left n (by omega : n ≤ n+1))).trans hk
    exact even_midpoint_tail hn hmid (fun h hh => hu h (by omega))

theorem central_from_midpoints (E : ℕ → ℤ)
    (hD : ∀ l, IntervalDecomposition (dyckPoly l) (E l))
    (hE : ∀ l, dyckLower l ≤ (E l:ℝ))
    (href : ∀ n, UnimodalOn (rankCount (2*n)) 0 (n*n) →
      ReflectedCoeffs (ballotPoly (2*n)) ⌊oddCutoff n⌋)
    (hc : ∀ n ≥ 96, ∀ δ ≤ 1, CentralToMidpoint n δ) : Conjecture34 :=
  central_from_inductive_windows E hD hE href (fun n hn δ hδ hu => suffix_from_midpoint hn hδ (hc n hn δ hδ) hu)

end CentralUnimodality
