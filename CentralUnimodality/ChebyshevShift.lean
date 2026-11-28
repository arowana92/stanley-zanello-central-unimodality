module

public import CentralUnimodality.CertifiedChebyshev

/-! Multiplication by 2-2X in the symmetric Chebyshev convention uses
only the two neighboring coefficients. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial Polynomial.Chebyshev

def neighbor {A : Type*} [Add A] (c : ℕ → A) : ℕ → A
  | 0 => c 1+c 1
  | i+1 => c i+c (i+2)

private theorem shift (n : ℕ) (c : ℕ → ℝ) (h : c n=0) (f : ℤ → ℝ[X]) :
    (∑ i ∈ Finset.range n, C (c i)*f i)=C (c 0)*f 0+
      ∑ i ∈ Finset.range n, C (c (i+1))*f ((i:ℤ)+1) := by
  let g := fun i : ℕ => C (c i)*f i
  have z : g n=0 := by simp [g,h]
  have a := Finset.sum_range_succ g n
  have b := Finset.sum_range_succ' g n
  rw [z,add_zero] at a
  simpa only [g,Nat.cast_zero,Nat.cast_succ,add_comm (C (c 0)*f 0)] using a.symm.trans b

theorem neighbor_series (n : ℕ) (c : ℕ → ℝ) (hc : c n=0) (hc' : c (n+1)=0) :
    (2*X)*weightedSeries n c=weightedSeries (n+1) (neighbor c) := by
  have adj (i : ℕ) : (2*X)*T ℝ i=T ℝ ((i:ℤ)+1)+T ℝ ((i:ℤ)-1) := by
    rw [T_add_one]; ring
  have sumAdj : (2*X)*(∑ i ∈ Finset.range n, C (c i)*T ℝ i)=
      (∑ i ∈ Finset.range n, C (c i)*T ℝ ((i:ℤ)+1))+
      ∑ i ∈ Finset.range n, C (c i)*T ℝ ((i:ℤ)-1) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_left_comm,adj,mul_add]
  have down := shift n c hc (fun j => T ℝ (j-1))
  simp only [zero_sub,Int.reduceNeg,T_neg_one,add_sub_cancel_right] at down
  have up := shift n (fun i => c (i+1)) hc' (T ℝ)
  simp only [T_zero,mul_one] at up
  rw [up] at down
  rw [weightedSeries,mul_sub,mul_left_comm (2*X) 2,sumAdj,down,weightedSeries,Finset.sum_range_succ']
  simp only [neighbor,Nat.cast_succ,Nat.cast_zero,T_zero,map_add,mul_one,add_mul,Finset.sum_add_distrib]
  ring

theorem weightedSeries_succ_zero (n : ℕ) (c : ℕ → ℝ) (h : c n=0) :
    weightedSeries (n+1) c=weightedSeries n c := by
  simp [weightedSeries,Finset.sum_range_succ,h]

theorem weightedSeries_linear (n : ℕ) (a b : ℝ) (c d : ℕ → ℝ) :
    weightedSeries n (fun i => a*c i+b*d i)=C a*weightedSeries n c+C b*weightedSeries n d := by
  simp only [weightedSeries,map_add,map_mul,add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]
  ring

def scaleShift (c : ℕ → ℤ) (i : ℕ) : ℤ := 2*c i-neighbor c i

theorem scaleShift_series (n : ℕ) (c : ℕ → ℤ) (hc : c n=0) (hc' : c (n+1)=0) :
    weightedSeries (n+1) (fun i => (scaleShift c i:ℝ))=
      (2-2*X)*weightedSeries n (fun i => (c i:ℝ)) := by
  let a := fun i => (c i:ℝ)
  have ns (i : ℕ) : ((neighbor c i:ℤ):ℝ)=neighbor a i := by cases i <;> simp [neighbor,a]
  have form : (fun i => (scaleShift c i:ℝ))=fun i => 2*a i+(-1)*neighbor a i := by
    funext i; simp [scaleShift,ns,a]; ring
  rw [form,weightedSeries_linear,weightedSeries_succ_zero _ _ (by simp [a,hc]),
    ← neighbor_series _ _ (by simp [a,hc]) (by simp [a,hc'])]
  simp only [Polynomial.C_ofNat,map_neg,map_one]
  ring

end CentralUnimodality.PolynomialTrial
