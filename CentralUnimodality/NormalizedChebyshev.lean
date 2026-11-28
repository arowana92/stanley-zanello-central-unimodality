module

public import CentralUnimodality.IntegerBetaProduct
public import CentralUnimodality.PolynomialTrialBounds

/-! Convert the integer monomial polynomials back to the actual trial
in the scaled time variable. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Polynomial Polynomial.Chebyshev

private theorem integer_value (a : List ℤ) (j : ℕ) (z : ℝ) :
    ((integerChebyshev a j).map (Int.castRingHom ℝ)).eval z =
      ∑ i ∈ Finset.range a.length, (entry a i:ℝ)*(T ℝ ((j+i:ℕ):ℤ)).eval (1-2*z) := by
  induction a generalizing j with
  | nil => simp [integerChebyshev]
  | cons c a ih =>
    simp only [integerChebyshev,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,
      eval_add,eval_mul,eval_C,shiftedT,Polynomial.map_comp,Chebyshev.map_T,Polynomial.map_sub,
      Polynomial.map_one,Polynomial.map_ofNat,map_X,eval_comp,eval_sub,eval_one,eval_X,eval_ofNat,ih,
      List.length_cons,Finset.sum_range_succ',entry,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,Int.coe_castRingHom,Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show j+1+i=j+(i+1) by omega]

theorem normalized_input (b : ℕ) (a : List ℤ) (small : (coefficientMass a:ℤ)*7^a.length<2^b)
    (v : ℝ) : value (doubleHead a) v=(realDense (unpackCheb b a)).eval (v/256)/2^120 := by
  simp only [realDense,unpackCheb_poly b a small,integer_value,zero_add]
  cases a with
  | nil => simp [doubleHead,value,realRow,weightedSeries,entry]
  | cons c a =>
    simp only [doubleHead,value,realRow,weightedSeries,eval_sub,eval_add,eval_mul,eval_ofNat,eval_finsetSum,
      eval_C,List.length_cons,Finset.sum_range_succ',entry,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,Nat.cast_zero,T_zero,eval_one,mul_one,Int.cast_mul,Int.cast_ofNat]
    rw [show 1-2*(v/256)=1-v/128 by ring]
    ring

end CentralUnimodality.PolynomialTrial
