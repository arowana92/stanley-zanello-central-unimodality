module

public import CentralUnimodality.PackedIntegerPolynomial
import Mathlib.Tactic.LinearCombination

/-! Divide-and-conquer decoding of centered digits. One geometric bias
makes each centered remainder an ordinary nonnegative radix digit. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

private def biasSum (b : ℕ) : ℕ → ℤ
  | 0 => 0
  | n+1 => 2^b+2^(b+1)*biasSum b n

def geometricBias (b n : ℕ) : ℤ :=
  ((2:ℤ)^b*(((1:ℤ) <<< ((b+1)*n))-1))/((2:ℤ)^(b+1)-1)

private theorem bias_exact (b n : ℕ) : geometricBias b n=biasSum b n := by
  let B : ℤ := 2^(b+1)
  have bound : 1<B := by dsimp only [B]; rw [pow_succ]; have := (one_le_pow₀ (by decide : (1:ℤ)≤2) : 1≤(2:ℤ)^b); omega
  have id : biasSum b n*(B-1)=2^b*(B^n-1) := by
    induction n with
    | zero => simp [biasSum]
    | succ n ih =>
      change (2^b+B*biasSum b n)*(B-1)=2^b*(B^(n+1)-1)
      rw [pow_succ]; linear_combination B*ih
  unfold geometricBias
  rw [Int.shiftLeft_eq,one_mul,pow_mul,← id,Int.mul_ediv_cancel _ (by omega : B-1≠0)]

def ordinaryDigits (b : ℕ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | n+1, z => (z%2^(b+1)-2^b)::ordinaryDigits b n (z >>> (b+1))

private theorem centered_ordinary (b n : ℕ) (z : ℤ) :
    ordinaryDigits b n (z+biasSum b n)=centeredDigits b n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    let B : ℤ := 2^(b+1)
    have B0 : B≠0 := by dsimp [B]; positivity
    have eq : z+biasSum b (n+1)=(z+2^b)+biasSum b n*B := by change z+(2^b+B*_)=_; ring
    rw [ordinaryDigits,centeredDigits,eq]
    simp only [Int.shiftRight_eq_div_pow,Int.shiftLeft_eq,Nat.cast_pow,Nat.cast_ofNat]
    change (((z+2^b)+biasSum b n*B)%B-2^b)::_=(z-((z+2^b)/B)*B)::_
    rw [Int.add_mul_emod_self_right]
    congr 1
    · have H := Int.emod_add_mul_ediv (z+2^b) B; linarith only [H]
    · change ordinaryDigits b n (((z+2^b)+biasSum b n*B)/B)=_
      rw [Int.add_mul_ediv_right _ _ B0]; exact ih _

private theorem ordinary_append (b a n : ℕ) (z : ℤ) :
    ordinaryDigits b (a+n) z=ordinaryDigits b a z++ordinaryDigits b n (z >>> ((b+1)*a)) := by
  induction a generalizing z with
  | zero => simp [ordinaryDigits]
  | succ a ih =>
    rw [Nat.succ_add,ordinaryDigits,ordinaryDigits,List.cons_append,ih]
    simp only [← Int.shiftRight_add,Nat.mul_succ,Nat.add_comm (b+1)]

private theorem ordinary_translate (b n : ℕ) (z h : ℤ) :
    ordinaryDigits b n (z+h*((2:ℤ)^(b+1))^n)=ordinaryDigits b n z := by
  induction n generalizing z h with
  | zero => rfl
  | succ n ih =>
    let B : ℤ := 2^(b+1)
    have B0 : B≠0 := by dsimp [B]; positivity
    rw [ordinaryDigits,ordinaryDigits,pow_succ,← mul_assoc]
    simp only [Int.shiftRight_eq_div_pow,Nat.cast_pow,Nat.cast_ofNat]
    change ((z+h*B^n*B)%B-2^b)::ordinaryDigits b n ((z+h*B^n*B)/B)=_::_
    rw [Int.add_mul_emod_self_right,Int.add_mul_ediv_right _ _ B0,ih]

def splitDigits (b : ℕ) : ℕ → ℕ → ℤ → List ℤ
  | 0, n, z => ordinaryDigits b n z
  | d+1, n, z =>
    let a := n/2
    let s := (b+1)*a
    let high := z >>> s
    splitDigits b d a (z-(high <<< s)) ++ splitDigits b d (n-a) high

private theorem splitDigits_exact (b d n : ℕ) (z : ℤ) : splitDigits b d n z=ordinaryDigits b n z := by
  induction d generalizing n z with
  | zero => rfl
  | succ d ih =>
    let a := n/2
    let h := z >>> ((b+1)*a)
    rw [splitDigits,ih,ih]
    change ordinaryDigits b a (z-(h <<< ((b+1)*a)))++ordinaryDigits b (n-a) h=_
    rw [show z-(h <<< ((b+1)*a))=z+(-h)*((2:ℤ)^(b+1))^a by rw [Int.shiftLeft_eq,pow_mul]; ring,
      ordinary_translate]
    have size : a+(n-a)=n := by dsimp [a]; omega
    rw [← ordinary_append, size]

def blockCenteredDigits (b d n : ℕ) (z : ℤ) := splitDigits b d n (z+geometricBias b n)

theorem blockCenteredDigits_exact (b d n : ℕ) (z : ℤ) : blockCenteredDigits b d n z=centeredDigits b n z := by
  rw [blockCenteredDigits,splitDigits_exact,bias_exact,centered_ordinary]

end CentralUnimodality.PolynomialTrial
