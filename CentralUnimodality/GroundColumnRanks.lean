module

public import CentralUnimodality.PairedDyckColumn
public import CentralUnimodality.ReversedHeightBlock
import Mathlib.Algebra.BigOperators.ModEq

/-! Reassemble both staircase corank rows from the same paired column
that computes ordinary Dyck area. Shifting the terminal height by
reversal accounts for the powers in the two endpoint sums. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock
open Polynomial

def weightedPrefix (b : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | _+1, [] => 0
  | s+1, a::r => a+(weightedPrefix b s r <<< b)

private theorem weighted_eq (b s : ℕ) (r : List ℕ) :
    weightedPrefix b s r=∑ h ∈ Finset.range s, entry r h*(2^b)^h := by
  induction s generalizing r with
  | zero => simp [weightedPrefix]
  | succ s ih =>
    cases r with
    | nil => simp [weightedPrefix,entry]
    | cons a r =>
      rw [weightedPrefix,Finset.sum_range_succ',Nat.shiftLeft_eq,ih,Finset.sum_mul]
      have tail (h : ℕ) : entry (a::r) (h+1)=entry r h := rfl
      simp only [pow_zero,mul_one,tail,pow_succ,mul_assoc]
      change a+_= _+a
      rw [add_comm]

def assembleGround (b s δ : ℕ) (r : List ℕ) : ℕ :=
  if δ=0 then weightedPrefix b (s+1) r
  else
    let tail := weightedPrefix (2*b) s r.tail
    r.headD 0+(tail <<< b)+(tail <<< (2*b))

private theorem assemble_eq {δ : ℕ} (hs : δ≤1) (b s : ℕ) (r : List ℕ) :
    assembleGround b s δ r=∑ h ∈ Finset.range (s+1), entry r h*(2^b)^h*
      transfer (2^b) δ (2*h) (fun _ => 1) := by
  rcases (show δ=0 ∨ δ=1 by omega) with rfl|rfl
  · simp [assembleGround,transfer,weighted_eq]
  · have tail (h : ℕ) : entry r.tail h=entry r (h+1) := by cases r <;> rfl
    have head : r.headD 0=entry r 0 := by cases r <;> rfl
    change r.headD 0+(weightedPrefix (2*b) s r.tail <<< b)+(weightedPrefix (2*b) s r.tail <<< (2*b))=_
    rw [head,weighted_eq,Nat.shiftLeft_eq,Nat.shiftLeft_eq]
    conv_rhs => rw [Finset.sum_range_succ']
    have ground : transfer (2^b) 1 0 (fun _ => 1)=1 := by simp [transfer]
    simp only [mul_zero,ground,pow_zero,mul_one]
    rw [show 2*b=b*2 by omega,Nat.pow_mul,Finset.sum_mul,Finset.sum_mul]
    calc _ = (∑ h ∈ Finset.range s, ((entry r.tail h * ((2^b)^2)^h)*(2^b)+
          (entry r.tail h*((2^b)^2)^h)*(2^b)^2))+entry r 0 := by rw [Finset.sum_add_distrib]; omega
         _ = _ := by
          apply congrArg (·+entry r 0)
          apply Finset.sum_congr rfl; intro h _
          simp only [transfer,ite_eq_right (show 2*(h+1)≠0 by omega),mul_one,tail,
            show (2*(h+1)+1)/2=h+1 by omega,show (2*(h+1)-1)/2=h by omega,pow_succ,
            ← pow_mul]
          ring

theorem assemble_ground_congr {b e H s δ : ℕ} (height : e+1≤H*(H-1)) (hs : δ≤1) :
    assembleGround b s δ (pairedRows b (2^(b*(e+1))) H s) ≡
      (ballotPoly (2*s+δ)).eval (2^b) [MOD 2^(b*(e+1))] := by
  rw [assemble_eq hs,ballot_from_ground_column,Polynomial.eval_finsetSum]
  apply Nat.ModEq.sum
  intro h _
  have he : (transfer (X:ℕ[X]) δ (2*h) (fun _ => 1)).eval (2^b)=
      transfer (2^b) δ (2*h) (fun _ => 1) := by
    rcases (show δ=0 ∨ δ=1 by omega) with rfl|rfl
    · simp [transfer]
    · by_cases z : h=0 <;> simp [transfer,z]
  rw [eval_mul,eval_mul,eval_pow,eval_X,he,eval_kernel,Nat.mul_comm ((2^b)^h)]
  exact ((paired_congr height s h).mul_right _).mul_right _

end CentralUnimodality.HeightBlock
