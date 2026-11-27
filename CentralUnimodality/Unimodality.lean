module

public import CentralUnimodality.Ranks
public import Mathlib.Data.Nat.Find

/-! Order lemmas used by both the finite and the uniform corank estimates. -/
@[expose] public section

namespace CentralUnimodality

theorem UnimodalOn.extend {f : ℕ → ℕ} {lo hi d : ℕ}
    (h : UnimodalOn f lo hi) (hd : hi ≤ d)
    (left : ∀ i < lo, f i ≤ f (i+1))
    (right : ∀ i, hi ≤ i → i < d → f (i+1) ≤ f i) : UnimodalOn f 0 d := by
  obtain ⟨p, hlp, hpr, hup, hdown⟩ := h
  refine ⟨p, Nat.zero_le _, by omega, ?_, ?_⟩
  · intro i _ hip
    by_cases hil : i < lo
    · exact left i hil
    · exact hup i (by omega) hip
  · intro i hpi hid
    by_cases hir : i < hi
    · exact hdown i hpi hir
    · exact right i (by omega) hid

theorem UnimodalOn.reverse {f : ℕ → ℕ} {d : ℕ} (h : UnimodalOn f 0 d) :
    UnimodalOn (fun j => f (d-j)) 0 d := by
  obtain ⟨p, _, hp, hu, hd⟩ := h
  refine ⟨d-p, Nat.zero_le _, by omega, ?_, ?_⟩
  · intro j _ hj
    have hx := hd (d-(j+1)) (by omega) (by omega)
    rwa [show d-(j+1)+1 = d-j by omega] at hx
  · intro j hj hjd
    have hx := hu (d-(j+1)) (Nat.zero_le _) (by omega)
    rwa [show d-(j+1)+1 = d-j by omega] at hx

theorem unimodalOn_reverse_iff (f : ℕ → ℕ) (d : ℕ) :
    UnimodalOn (fun j => f (d-j)) 0 d ↔ UnimodalOn f 0 d := by
  refine ⟨?_, UnimodalOn.reverse⟩
  intro h
  obtain ⟨p, hp, hpd, hu, hd⟩ := h.reverse
  refine ⟨p, hp, hpd, ?_, ?_⟩
  · intro j hj hjp
    have hx := hu j hj hjp
    simpa only [show d-(d-j) = j by omega, show d-(d-(j+1)) = j+1 by omega] using hx
  · intro j hj hjd
    have hx := hd j hj hjd
    simpa only [show d-(d-j) = j by omega, show d-(d-(j+1)) = j+1 by omega] using hx

/-- An interval is unimodal iff no strict fall is followed by a strict rise. -/
theorem unimodalOn_iff_no_valley (f : ℕ → ℕ) {lo hi : ℕ} (hlh : lo ≤ hi) :
    UnimodalOn f lo hi ↔
      ∀ i j, lo ≤ i → i < j → j < hi → f (i+1) < f i → f (j+1) ≤ f j := by
  constructor
  · rintro ⟨p, _, _, hu, hd⟩ i j hli hij hjh hfi
    by_cases hip : i < p
    · have := hu i hli hip; omega
    · exact hd j (by omega) hjh
  · intro hv
    by_cases he : ∃ i, lo ≤ i ∧ i < hi ∧ f (i+1) < f i
    · let p := Nat.find he
      obtain ⟨hlp, hph, hfp⟩ := Nat.find_spec he
      refine ⟨p, hlp, by omega, ?_, ?_⟩
      · intro i hli hip
        have := Nat.find_min he hip
        change ¬(lo ≤ i ∧ i < hi ∧ f (i+1) < f i) at this
        omega
      · intro j hpj hjh
        rcases Nat.eq_or_lt_of_le hpj with rfl | hpj
        · exact Nat.le_of_lt hfp
        · exact hv p j hlp hpj hjh hfp
    · exact ⟨hi, hlh, Nat.le_refl _, fun i hli hih =>
        Nat.le_of_not_gt (fun h => he ⟨i, hli, hih, h⟩), by omega⟩

/-- First differences on the flanks and nonpositive second differences in
the middle suffice. A zero difference is allowed anywhere. -/
theorem unimodalOn_of_curvature {f : ℕ → ℕ} {lo a b hi : ℕ}
    (hla : lo ≤ a) (hab : a ≤ b) (hbh : b ≤ hi)
    (left : ∀ j, lo ≤ j → j < a → f j ≤ f (j+1))
    (middle : ∀ j, a ≤ j → j+1 < b → f j + f (j+2) ≤ 2*f (j+1))
    (right : ∀ j, b ≤ j → j < hi → f (j+1) ≤ f j) : UnimodalOn f lo hi := by
  apply (unimodalOn_iff_no_valley f (by omega)).mpr
  intro i j hli hij hjh hfall
  by_cases hb : b ≤ j
  · exact right j hb hjh
  have hai : a ≤ i := by
    by_contra! hi
    have := left i hli hi
    omega
  have propagate : ∀ t, i ≤ t → t < b → f (t+1) < f t := by
    intro t hit
    induction t, hit using Nat.le_induction with
    | base => exact fun _ => hfall
    | succ k hik ih =>
      intro hkb
      have hprev := ih (by omega)
      have hcurv := middle k (by omega) hkb
      change f (k+2) < f (k+1)
      omega
  exact Nat.le_of_lt (propagate j (by omega) (by omega))

end CentralUnimodality
