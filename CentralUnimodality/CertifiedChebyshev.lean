module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Chebyshev series with an integer certificate for the derivative row.
Internally the constant coefficient has half weight, so the same
two-step recurrence applies to every coefficient. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Polynomial Polynomial.Chebyshev

noncomputable def weightedSeries (n : ℕ) (c : ℕ → ℝ) : ℝ[X] :=
  2*(∑ i ∈ Finset.range n, C (c i)*T ℝ i)-C (c 0)

private theorem split_first {A : Type*} [AddCommMonoid A] (n : ℕ) (g : ℕ → A) (hn : g n=0) :
    (∑ i ∈ Finset.range n, g i)=g 0+∑ i ∈ Finset.range n, g (i+1) := by
  have a := Finset.sum_range_succ g n
  have b := Finset.sum_range_succ' g n
  rw [hn,add_zero] at a
  rw [← a,b,add_comm]

private theorem shifted_U (n : ℕ) (d : ℕ → ℝ) (hn : d n=0) (hn' : d (n+1)=0) :
    (∑ i ∈ Finset.range n, C (d i)*U ℝ ((i:ℤ)-2)) =
      -C (d 0)+∑ i ∈ Finset.range n, C (d (i+2))*U ℝ i := by
  rw [split_first n _ (by simp [hn])]
  simp only [Nat.cast_zero,zero_sub,U_neg_two, mul_neg,mul_one,Nat.cast_succ]
  rw [split_first n (fun i => C (d (i+1))*U ℝ ((i:ℤ)+1-2)) (by simp [hn'])]
  simp only [Nat.cast_zero,zero_add,show (1:ℤ)-2= -1 by decide,U_neg_one,mul_zero,zero_add,Nat.cast_succ,
    show ∀ i : ℤ, i+1+1-2=i by intro; ring]

private theorem differentiated_modes (n : ℕ) (c : ℕ → ℝ) (hn : c n=0) :
    derivative (∑ i ∈ Finset.range n, C (c i)*T ℝ i) =
      ∑ i ∈ Finset.range n, C (((i:ℝ)+1)*c (i+1))*U ℝ i := by
  simp only [Polynomial.derivative_sum,derivative_C_mul,T_derivative_eq_U]
  rw [split_first n _ (by simp [hn])]
  simp only [Nat.cast_zero,Int.cast_zero,zero_mul,mul_zero,zero_add,Nat.cast_succ,Int.add_sub_cancel,
    map_mul,map_add,map_one]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  simp [mul_left_comm,mul_assoc]

theorem weightedSeries_derivative (n : ℕ) (c d : ℕ → ℝ) (hc : c n=0)
    (hd : d n=0) (hd' : d (n+1)=0)
    (step : ∀ i<n, d i-d (i+2)=2*((i:ℝ)+1)*c (i+1)) :
    derivative (weightedSeries n c)=weightedSeries n d := by
  have twoT (i : ℕ) : 2*T ℝ i=U ℝ i-U ℝ ((i:ℤ)-2) := by
    simpa using two_mul_T_eq_U_sub_U ℝ ((i:ℤ)-2)
  have sumT : 2*(∑ i ∈ Finset.range n, C (d i)*T ℝ i)=
      (∑ i ∈ Finset.range n, C (d i)*U ℝ i)-
        ∑ i ∈ Finset.range n, C (d i)*U ℝ ((i:ℤ)-2) := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_left_comm,twoT,mul_sub]
  unfold weightedSeries
  rw [sumT,shifted_U _ _ hd hd',derivative_sub,derivative_C,sub_zero,
    ← Polynomial.C_ofNat (R:=ℝ) (n:=2),derivative_C_mul,differentiated_modes _ _ hc,Polynomial.C_ofNat]
  rw [show ∀ a b c : ℝ[X], a-(-b+c)-b=a-c by intros; ring,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sub_mul,← map_sub,step _ (Finset.mem_range.mp hi)]
  simp only [map_mul,Polynomial.C_ofNat]
  ring

theorem weightedSeries_bound (n : ℕ) (c : ℕ → ℝ) {x : ℝ} (hx : |x|≤1) :
    |(weightedSeries n c).eval x| ≤ 2*(∑ i ∈ Finset.range n, |c i|)+|c 0| := by
  simp only [weightedSeries,eval_sub,eval_mul,eval_ofNat,eval_finsetSum,eval_C]
  apply (abs_sub ..).trans
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (abs_eval_T_real_le_one (i:ℤ) hx) (abs_nonneg (c i))

end CentralUnimodality.PolynomialTrial
