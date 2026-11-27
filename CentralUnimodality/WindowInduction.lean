module

public import CentralUnimodality.StaircasePrefix
public import CentralUnimodality.ReflectedBase

/-! Glue each central interval and its right flank to the increasing prefix.
The odd-part family at size n is available before the even-part step at n. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def centralStart (n m : ℕ) : ℕ :=
  if n ≤ 2048 then ⌊0.1*(m:ℝ)*Real.sqrt m⌋₊
  else if n < 300000 then ⌊0.1366*(m:ℝ)*Real.sqrt m⌋₊
  else ⌈0.1375*(m:ℝ)*Real.sqrt m⌉₊

theorem before_centralStart {n m k : ℕ} (hn : 96 ≤ n) (hm : m ≤ 2*n+1) (hk : k < centralStart n m) :
    2*(k:ℝ)+1 ≤ (prefixConstant:ℝ)*n*Real.sqrt n-n-1 := by
  unfold centralStart at hk
  split at hk
  · have hx := (Nat.floor_le (by positivity : 0 ≤ 0.1*(m:ℝ)*Real.sqrt m))
    have hy : (k:ℝ) ≤ ⌊0.1*(m:ℝ)*Real.sqrt m⌋₊ := by exact_mod_cast hk.le
    linarith only [hx,hy,prefix_window_64 (by omega : 64 ≤ n) hm]
  · split at hk
    · have hx := (Nat.floor_le (by positivity : 0 ≤ 0.1366*(m:ℝ)*Real.sqrt m))
      have hy : (k:ℝ) ≤ ⌊0.1366*(m:ℝ)*Real.sqrt m⌋₊ := by exact_mod_cast hk.le
      linarith only [hx,hy,prefix_window_2049 (by omega : 2049 ≤ n) hm]
    · have hx := Nat.lt_ceil.mp hk
      have hnon : 0 ≤ (m:ℝ)*Real.sqrt m := by positivity
      linarith only [hx,hnon,prefix_window_4096 (by omega : 4096 ≤ n) hm]

/-- The analytic input includes the right flank through the last corank. -/
def CentralSuffix (n δ : ℕ) : Prop :=
  UnimodalOn (fun k => rankCount (2*n+δ) (n*(n+δ)-k)) (centralStart n (2*n+δ)) (n*(n+δ))

private theorem attach_prefix {n δ : ℕ} (hδ : δ ≤ 1) (hs : CentralSuffix n δ)
    (hp : ∀ k < centralStart n (2*n+δ),
      (ballotPoly (2*n+δ)).coeff k ≤ (ballotPoly (2*n+δ)).coeff (k+1)) :
    UnimodalOn (rankCount (2*n+δ)) 0 (n*(n+δ)) := by
  have hlo : centralStart n (2*n+δ) ≤ n*(n+δ) := by
    obtain ⟨p,hl,hr,_⟩ := hs
    exact hl.trans hr
  apply (unimodalOn_reverse_iff _ _).mp
  apply UnimodalOn.extend hs (le_refl _)
  · intro k hk
    simpa only [ballotPoly_coeff n δ k hδ (by omega),ballotPoly_coeff n δ (k+1) hδ (by omega)] using hp k hk
  · omega

theorem central_from_windows (E : ℕ → ℤ)
    (hD : ∀ l, IntervalDecomposition (dyckPoly l) (E l))
    (hE : ∀ l, dyckLower l ≤ (E l:ℝ))
    (href : ∀ n, UnimodalOn (rankCount (2*n)) 0 (n*n) →
      ReflectedCoeffs (ballotPoly (2*n)) ⌊oddCutoff n⌋)
    (hs : ∀ n ≥ 96, ∀ δ ≤ 1, CentralSuffix n δ) : Conjecture34 := by
  have odd (n : ℕ) : UnimodalOn (rankCount (2*n)) 0 (n*n) := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases hn : n ≤ 95
      · exact (central_through_95 hn).1
      cases n with
      | zero => omega
      | succ n =>
        have h := attach_prefix (δ := 0) (by decide) (hs (n+1) (by omega) 0 (by decide)) (by
          intro k hk
          simp only [Nat.add_zero] at hk ⊢
          apply odd_prefix_from_bounds n k E (fun l _ => hD l) (fun l _ => hE l) (fun i hi => href i (ih i (by omega)))
          exact_mod_cast before_centralStart (by omega : 96 ≤ n+1) (by omega : 2*(n+1) ≤ 2*(n+1)+1) hk)
        simpa only [Nat.add_zero] using h
  intro n _
  refine ⟨odd n, ?_⟩
  by_cases hn : n ≤ 95
  · exact (central_through_95 hn).2
  apply attach_prefix (δ := 1) (by decide) (hs n (by omega) 1 (by decide))
  intro k hk
  exact even_prefix_from_bounds n k E (fun l _ => hD l) (fun l _ => hE l) (fun i _ => href i (odd i))
    (before_centralStart (by omega : 96 ≤ n) (le_refl _) hk)

end CentralUnimodality
