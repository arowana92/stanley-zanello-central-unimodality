module

public import CentralUnimodality.IntervalProduct

/-! Transfer in the area variable. Each surviving step to height k adds
floor(k/2) to the corank. Keeping the terminal height distinguishes
ordinary Dyck paths from the two free-endpoint staircase families. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock
open Polynomial

def nextHeight (h : ℕ) : Bool → ℕ
  | false => h+1
  | true => h-1

def cost (h : ℕ) : List Bool → ℕ
  | [] => 0
  | b::w => nextHeight h b/2 + cost (nextHeight h b) w

def finish (h : ℕ) : List Bool → ℕ
  | [] => h
  | b::w => finish (nextHeight h b) w

theorem finish_eq {h : ℕ} {w : List Bool} (hw : BallotFrom h w) :
    (finish h w:ℤ)=h+displacement w := by
  induction w generalizing h with
  | nil => simp [finish,displacement]
  | cons b w ih =>
    have he : displacement (b::w)=step b+displacement w := rfl
    cases b with
    | false => rw [finish,nextHeight,ih hw,he]; simp [step]; omega
    | true => rw [finish,nextHeight,ih hw.2,he]; simp [step]; have := hw.1; omega

private theorem area_cost {h : ℕ} {w : List Bool} (hw : BallotFrom h w) :
    (heights h w).sum=2*(cost h w:ℤ)+((w.length+1-h%2)/2:ℕ) := by
  induction w generalizing h with
  | nil => simp [heights,cost]; omega
  | cons b w ih =>
    cases b with
    | false =>
      have he : (h:ℤ)+step false=(h+1:ℕ) := by simp [step]
      rw [heights,he,List.sum_cons,ih hw,cost]
      simp only [nextHeight,List.length_cons,Nat.cast_add]
      omega
    | true =>
      have hp := hw.1
      have he : (h:ℤ)+step true=(h-1:ℕ) := by simp [step]; omega
      rw [heights,he,List.sum_cons,ih hw.2,cost]
      simp only [nextHeight,List.length_cons,Nat.cast_add]
      omega

theorem cost_eq_corank {w : List Bool} (hw : BallotFrom 0 w) : cost 0 w=walkCorank w := by
  have he := area_cost hw
  change walkArea w=_ at he
  rw [walkArea_eq_corank hw] at he
  omega

def transfer {R : Type*} [Semiring R] (q : R) : ℕ → ℕ → (ℕ → R) → R
  | 0, h, f => f h
  | m+1, h, f => q^((h+1)/2)*transfer q m (h+1) f +
      if h=0 then 0 else q^((h-1)/2)*transfer q m (h-1) f

theorem transfer_add {R : Type*} [Semiring R] (q : R) (a b h : ℕ) (f : ℕ → R) :
    transfer q (a+b) h f=transfer q a h (fun k => transfer q b k f) := by
  induction a generalizing h with
  | zero => simp [transfer]
  | succ a ih => rw [Nat.succ_add,transfer,transfer,ih,ih]

theorem transfer_sum {R : Type*} [Semiring R] (q : R) (m h : ℕ) (f : ℕ → R) :
    transfer q m h f=∑ w ∈ words m, if BallotFrom h w then q^(cost h w)*f (finish h w) else 0 := by
  induction m generalizing h with
  | zero => simp [words,transfer,BallotFrom,cost,finish]
  | succ m ih =>
    have dis : Disjoint ((words m).image (false::·)) ((words m).image (true::·)) := by
      simp [Finset.disjoint_left]
    rw [transfer,words,Finset.sum_union dis,Finset.sum_image (fun _ _ _ _ eq => (List.cons.inj eq).2),
      Finset.sum_image (fun _ _ _ _ eq => (List.cons.inj eq).2),ih,ih]
    apply congrArg₂ (·+·)
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      by_cases ok : BallotFrom (h+1) w <;> simp [BallotFrom,cost,finish,nextHeight,ok,pow_add,mul_assoc]
    · by_cases hh : h=0
      · simp [hh,BallotFrom]
      · simp only [ite_eq_right hh,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        by_cases ok : BallotFrom (h-1) w <;> simp [BallotFrom,cost,finish,nextHeight,ok,
          Nat.pos_of_ne_zero hh,pow_add,mul_assoc]

theorem ballot_eq_transfer (m : ℕ) :
    ballotPoly m=transfer X m 0 (fun _ => 1) := by
  rw [ballotPoly,corankSum,ballots,Finset.sum_filter,transfer_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : BallotFrom 0 w <;> simp [hw,cost_eq_corank]

theorem dyck_eq_transfer (n : ℕ) :
    dyckPoly n=transfer X (2*n) 0 (fun h => if h=0 then 1 else 0) := by
  rw [dyckPoly,corankSum,dycks,Finset.sum_filter,ballots,Finset.sum_filter,transfer_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : BallotFrom 0 w
  · have he := finish_eq hw
    have hh : finish 0 w=0 ↔ displacement w=0 := by omega
    by_cases hz : displacement w=0 <;> simp [hw,hh,hz,cost_eq_corank hw]
  · simp [hw]

end CentralUnimodality.HeightBlock
