module

public import CentralUnimodality.PrefixWindows
public import CentralUnimodality.PrefixInduction

/-! Use the two endpoint bounds in the actual shifted Dyck convolutions.
The floor is applied after moving the integer offsets to the other side. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def oddCutoff (h : ℕ) : ℝ := (131/250)*Witness.cellScale h-3*h-1
noncomputable def dyckLower (l : ℕ) : ℝ := (2*Real.sqrt 2/3)*l*Real.sqrt l-l

private theorem combined_endpoint {h l k s : ℕ} {e : ℤ} (hs : h ≤ s)
    (he : dyckLower l ≤ e)
    (hk : 2*(k:ℝ)+1 ≤ (prefixConstant:ℝ)*(h+l)*Real.sqrt (h+l)-(h+l)-1) :
    2*(k:ℤ)+1 ≤ ⌊oddCutoff h⌋+2*s+e := by
  have hmin := prefix_minimum (l := l) (h := h) (by positivity) (by positivity)
  rw [add_comm (l:ℝ) h] at hmin
  have hs' : (h:ℝ) ≤ s := by exact_mod_cast hs
  have hfloor : 2*(k:ℤ)+1-2*s-e ≤ ⌊oddCutoff h⌋ := by
    apply Int.le_floor.mpr
    push_cast
    unfold oddCutoff Witness.cellScale
    unfold dyckLower at he
    linarith only [hk,hmin,he,hs']
  omega

private theorem isolated_endpoint {n k : ℕ} {e : ℤ} (he : dyckLower n ≤ e)
    (hk : 2*(k:ℝ)+1 ≤ (prefixConstant:ℝ)*n*Real.sqrt n-n-1) :
    2*(k:ℤ)+1 ≤ e := by
  have hm := prefix_minimum (l := n) (h := 0) (by positivity) le_rfl
  simp only [add_zero,mul_zero,Real.sqrt_zero] at hm
  unfold dyckLower at he
  exact_mod_cast (show 2*(k:ℝ)+1 ≤ e by linarith only [hk,he,hm])

theorem odd_prefix_from_bounds (n k : ℕ) (E : ℕ → ℤ)
    (hD : ∀ l ≤ n+1, IntervalDecomposition (dyckPoly l) (E l))
    (hE : ∀ l ≤ n+1, dyckLower l ≤ (E l:ℝ))
    (hB : ∀ h ≤ n, ReflectedCoeffs (ballotPoly (2*h)) ⌊oddCutoff h⌋)
    (hk : 2*(k:ℝ)+1 ≤ (prefixConstant:ℝ)*(n+1)*Real.sqrt (n+1)-(n+1)-1) :
    (ballotPoly (2*(n+1))).coeff k ≤ (ballotPoly (2*(n+1))).coeff (k+1) := by
  apply oddPart_prefix_step n k E (fun h => ⌊oddCutoff h⌋) hD hB
  · apply isolated_endpoint (hE _ le_rfl)
    simpa only [Nat.cast_add,Nat.cast_one] using hk
  · intro i hi
    have hsum : ((n-i:ℕ):ℝ)+((i+1:ℕ):ℝ) = n+1 := by exact_mod_cast (by omega : n-i+(i+1) = n+1)
    have h := combined_endpoint (s := 2*(n-i)+1) (h := n-i) (l := i+1) (k := k)
      (by omega) (hE _ (by omega)) (by rwa [hsum])
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using h

theorem even_prefix_from_bounds (n k : ℕ) (E : ℕ → ℤ)
    (hD : ∀ l ≤ n, IntervalDecomposition (dyckPoly l) (E l))
    (hE : ∀ l ≤ n, dyckLower l ≤ (E l:ℝ))
    (hB : ∀ h ≤ n, ReflectedCoeffs (ballotPoly (2*h)) ⌊oddCutoff h⌋)
    (hk : 2*(k:ℝ)+1 ≤ (prefixConstant:ℝ)*n*Real.sqrt n-n-1) :
    (ballotPoly (2*n+1)).coeff k ≤ (ballotPoly (2*n+1)).coeff (k+1) := by
  apply evenPart_prefix_step n k E (fun h => ⌊oddCutoff h⌋) hD hB
  intro i hi
  have hsum : ((n-i:ℕ):ℝ)+(i:ℝ) = n := by exact_mod_cast (by omega : n-i+i = n)
  apply combined_endpoint (by omega) (hE _ hi)
  rwa [hsum]

end CentralUnimodality
