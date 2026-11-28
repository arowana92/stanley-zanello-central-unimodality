module

public import CentralUnimodality.HeightBlockClosure
public import CentralUnimodality.Finite
public import CentralUnimodality.FirstReturn
import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Data.Nat.ModEq

/-! Compute an entire column of the area transfer matrix modulo a power
of the digit base. Every retained digit is an exact path count. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock
open Polynomial

private theorem eval_digit (p : ℕ[X]) (b i : ℕ) (small : ∀ j, p.coeff j<2^b) :
    digit b (p.eval (2^b)) i=p.coeff i := by
  have split (p : ℕ[X]) : p.eval (2^b)=p.coeff 0+p.divX.eval (2^b)*2^b := by
    have H := congrArg (Polynomial.eval (2^b)) (divX_mul_X_add p)
    simpa only [eval_add,eval_mul,eval_X,eval_C,add_comm (p.coeff 0)] using H.symm
  induction i generalizing p with
  | zero =>
    rw [digit_zero,split,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt (small 0)]
  | succ i ih =>
    rw [digit_succ,Nat.shiftRight_eq_div_pow,split,Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (small 0),zero_add,ih p.divX (fun j => by simpa using small (j+1)),coeff_divX]

private theorem kernel_small (m h t i : ℕ) : (kernel m h t).coeff i≤2^m := by
  rw [kernel,transfer_sum,finsetSum_coeff]
  calc _ ≤ ∑ _ ∈ words m, (1:ℕ) := by
        apply Finset.sum_le_sum
        intro w _
        by_cases ok : BallotFrom h w <;> by_cases e : finish h w=t <;>
          simp [ok,e,coeff_X_pow]; split <;> omega
       _ = _ := by simp [card_words]

theorem eval_kernel (B m h t : ℕ) :
    (kernel m h t).eval B = transfer B m h (fun k => if k=t then 1 else 0) := by
  unfold kernel
  induction m generalizing h with
  | zero => by_cases e : h=t <;> simp [transfer,e]
  | succ m ih => by_cases e : h=0 <;> simp [transfer,e,ih]

def column (b M t size : ℕ) : ℕ → List ℕ
  | 0 => (List.range size).map fun h => if h=t then 1 else 0
  | m+1 =>
    let old := column b M t size m
    (List.range (size-(m+1))).map fun h =>
      (((entry old (h+1)) <<< (b*((h+1)/2)))+
        (if h=0 then 0 else (entry old (h-1)) <<< (b*((h-1)/2))))%M

private theorem column_eval (b M t size m h : ℕ) (hh : h+m<size) :
    entry (column b M t size m) h ≡ (kernel m h t).eval (2^b) [MOD M] := by
  rw [eval_kernel]
  induction m generalizing h with
  | zero =>
    simp only [column,entry,List.getElem?_map,List.getElem?_range (by omega : h<size),
      Option.map_some,Option.getD_some,transfer,Nat.ModEq.refl]
  | succ m ih =>
    simp only [column,entry,List.getElem?_map,List.getElem?_range (by omega : h<size-(m+1)),
      Option.map_some,Option.getD_some,transfer,Nat.shiftLeft_eq,← Nat.pow_mul]
    apply (Nat.mod_modEq ..).trans
    apply Nat.ModEq.add
    · exact (ih (h+1) (by omega)).mul_right _ |>.trans (by rw [Nat.mul_comm])
    · by_cases z : h=0
      · simp [z,Nat.ModEq.refl]
      · simp only [ite_eq_right z]
        exact (ih (h-1) (by omega)).mul_right _ |>.trans (by rw [Nat.mul_comm])

theorem kernel_digit_of_congr {m h t e b i value : ℕ} (hb : m<b) (hi : i≤e)
    (H : value ≡ (kernel m h t).eval (2^b) [MOD 2^(b*(e+1))]) :
    digit b value i=(kernel m h t).coeff i := by
  have dvd : 2^(b*i)*2^b ∣ 2^(b*(e+1)) := by
    rw [← Nat.pow_add,← Nat.mul_succ]
    exact pow_dvd_pow _ (Nat.mul_le_mul_left b (by omega))
  have eq := H.of_dvd dvd
  rw [← eval_digit (kernel m h t) b i (fun j =>
    (kernel_small m h t j).trans_lt (Nat.pow_lt_pow_right (by decide) hb))]
  simp only [digit,Nat.shiftRight_eq_div_pow,← Nat.mod_mul_right_div_self]
  exact congrArg (· / 2^(b*i)) eq

theorem column_digit {m t h size e b i : ℕ} (hh : h+m<size) (hb : m<b) (hi : i≤e) :
    digit b (entry (column b (2^(b*(e+1))) t size m) h) i=(kernel m h t).coeff i :=
  kernel_digit_of_congr hb hi (column_eval b (2^(b*(e+1))) t size m h hh)

end CentralUnimodality.HeightBlock
