module

public import CentralUnimodality.HeightBlockTransfer
public import CentralUnimodality.HeightBlockClosure
public import CentralUnimodality.ReverseWalk
import Mathlib.Tactic.Ring

/-! Reversal exchanges the two boundary heights. Its change of weight
is the difference between the half-heights at the endpoints. Thus the
ground column also determines both free-endpoint staircase polynomials. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock
open Polynomial

private theorem vertex_cost {h : ℕ} {w : List Bool} (hw : BallotFrom h w) :
    ((vertices h w).map (fun z : ℤ => z.toNat/2)).sum=h/2+cost h w := by
  induction w generalizing h with
  | nil => simp [vertices,heights,cost]
  | cons b w ih =>
    have hv : vertices h (b::w)=(h:ℤ)::vertices ((h:ℤ)+step b) w := rfl
    rw [hv,List.map_cons,List.sum_cons,cost]
    cases b with
    | false =>
      rw [show (h:ℤ)+step false=(h+1:ℕ) by simp [step],ih hw]; rfl
    | true =>
      have hp := hw.1
      rw [show (h:ℤ)+step true=(h-1:ℕ) by simp [step]; omega,ih hw.2]; rfl

private theorem reverse_good {h t : ℕ} {w : List Bool} (hw : BallotFrom h w) (ht : finish h w=t) :
    BallotFrom t (reverseWalk w) ∧ finish t (reverseWalk w)=h := by
  have he := finish_eq hw
  rw [ht] at he
  have rev : vertices t (reverseWalk w)=(vertices h w).reverse := by rw [he,reverse_vertices]
  have ok : BallotFrom t (reverseWalk w) := by
    apply (ballot_iff_heights ..).mpr
    intro y hy
    have hv : y∈vertices t (reverseWalk w) := List.mem_cons_of_mem _ hy
    rw [rev,List.mem_reverse] at hv
    rcases List.mem_cons.mp hv with rfl|hy
    · positivity
    · exact (ballot_iff_heights ..).mp hw _ hy
  refine ⟨ok,?_⟩
  have hr := finish_eq ok
  rw [reverseWalk_disp] at hr
  omega

theorem kernel_reversal (m h t : ℕ) :
    (X:ℕ[X])^(h/2)*kernel m h t=X^(t/2)*kernel m t h := by
  simp only [kernel,transfer_sum,Finset.mul_sum]
  apply Finset.sum_bij' (fun w _ => reverseWalk w) (fun w _ => reverseWalk w)
  · intro w hw; exact mem_words.mpr (by rw [reverseWalk_length,mem_words.mp hw])
  · intro w hw; exact mem_words.mpr (by rw [reverseWalk_length,mem_words.mp hw])
  · intro w _; exact reverseWalk_twice w
  · intro w _; exact reverseWalk_twice w
  · intro w _
    by_cases good : BallotFrom h w ∧ finish h w=t
    · obtain ⟨ok,back⟩ := reverse_good good.1 good.2
      have he := finish_eq good.1
      rw [good.2] at he
      have hv := reverse_vertices (h:ℤ) w
      rw [← he] at hv
      have same := congrArg (fun a : List ℤ => (a.map (fun z => z.toNat/2)).sum) hv
      simp only [List.map_reverse,List.sum_reverse,vertex_cost good.1,vertex_cost ok] at same
      simp only [ite_eq_left good.1,ite_eq_left good.2,ite_eq_left ok,ite_eq_left back,mul_one,← pow_add,same]
    · have bad : ¬(BallotFrom t (reverseWalk w) ∧ finish t (reverseWalk w)=h) := by
        rintro ⟨a,b⟩
        have H := reverse_good a b
        exact good (by simpa using H)
      by_cases a : BallotFrom h w <;> by_cases b : BallotFrom t (reverseWalk w) <;> simp_all

private theorem even_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R) (s : ℕ)
    (odd : ∀ j, f (2*j+1)=0) :
    ∑ t ∈ Finset.range (2*s+1), f t=∑ h ∈ Finset.range (s+1), f (2*h) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show 2*(s+1)+1=(2*s+1)+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,
      odd,add_zero,ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show 2*s+1+1=2*(s+1) by omega]

theorem ballot_from_ground_column (s δ : ℕ) :
    ballotPoly (2*s+δ)=∑ h ∈ Finset.range (s+1),
      X^h*kernel (2*s) (2*h) 0 * transfer X δ (2*h) (fun _ => 1) := by
  rw [ballot_eq_transfer,transfer_add,transfer_expand,Nat.zero_add,even_sum]
  · apply Finset.sum_congr rfl
    intro h _
    have H := kernel_reversal (2*s) 0 (2*h)
    simp only [Nat.zero_div,pow_zero,one_mul,show 2*h/2=h by omega] at H
    rw [H]
  · intro j
    suffices kernel (2*s) 0 (2*j+1)=0 by rw [this,zero_mul]
    rw [kernel,transfer_sum]
    apply Finset.sum_eq_zero
    intro w hw
    have hl := mem_words.mp hw
    by_cases ok : BallotFrom 0 w
    · have he := finish_eq ok
      have parity := displacement_length w
      rw [hl] at parity
      have ht : finish 0 w≠2*j+1 := by omega
      simp [ok,ht]
    · simp [ok]

end CentralUnimodality.HeightBlock
