module

public import CentralUnimodality.AlternatingDegrees

/-! The usual Dyck area word lists the height before each up-step. Its
area is the exponent used in the staircase recurrence. -/
@[expose] public section

namespace CentralUnimodality

def upHeights : ℕ → List Bool → List ℕ
  | _, [] => []
  | h, false :: w => h :: upHeights (h+1) w
  | h, true :: w => upHeights (h-1) w

private theorem twice_up_length (h : ℕ) (w : List Bool) :
    2*((upHeights h w).length:ℤ) = (w.length:ℤ)+displacement w := by
  induction w generalizing h with
  | nil => simp [upHeights,displacement]
  | cons b w ih =>
    have hd : displacement (b::w) = step b+displacement w := rfl
    cases b <;> simp only [upHeights,List.length_cons,Nat.cast_add,Nat.cast_one,hd,step]
    · linarith only [ih (h+1)]
    · linarith only [ih (h-1)]

private theorem height_balance (h : ℕ) (w : List Bool) (hw : BallotFrom h w) :
    let e := (h:ℤ)+displacement w
    2*(heights h w).sum+e*(e-1)-(h:ℤ)*(h-1) =
      4*((upHeights h w).sum:ℤ)+2*((upHeights h w).length:ℤ) := by
  induction w generalizing h with
  | nil => simp [heights,upHeights,displacement]
  | cons b w ih =>
    have hd : displacement (b::w) = step b+displacement w := rfl
    cases b with
    | false =>
      have hh := ih (h+1) hw
      simp only [upHeights,heights,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,hd,step] at hh ⊢
      nlinarith only [hh]
    | true =>
      obtain ⟨hp,hw⟩ := hw
      have hh := ih (h-1) hw
      simp only [upHeights,heights,List.sum_cons,hd,step,Nat.cast_sub hp,Nat.cast_one] at hh ⊢
      change _ + _ - _ = _
      rw [show (h:ℤ)+ -1 = h-1 by ring]
      nlinarith only [hh]

theorem dyck_up_heights {w : List Bool} {n : ℕ} (hw : w ∈ dycks n) :
    (upHeights 0 w).length = n ∧ (upHeights 0 w).sum = walkCorank w := by
  obtain ⟨⟨hl,hb⟩,hd⟩ := mem_dycks.mp hw
  have hu := twice_up_length 0 w
  rw [hl,hd,add_zero] at hu
  push_cast at hu
  have hc : (upHeights 0 w).length = n := by omega
  have hh := height_balance 0 w hb
  have ha := walkArea_eq_corank hb
  rw [hl] at ha
  have hp : (2*n+1)/2 = n := by omega
  rw [hp] at ha
  simp only [hd,Nat.cast_zero,zero_mul,add_zero,sub_zero,hc] at hh
  change 2*walkArea w = _ at hh
  exact ⟨hc,by omega⟩

end CentralUnimodality
