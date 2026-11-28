module

public import CentralUnimodality.NormalizedChebyshev

/-! Sharp absolute-sum bound for the unnormalized shifted Chebyshev row. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial Polynomial.Chebyshev

private theorem shifted_eval {z : ℝ} (hz : |1-2*z|≤1) (n : ℕ) :
    |((shiftedT n).map (Int.castRingHom ℝ)).eval z|≤1 := by
  simpa only [shiftedT,Polynomial.map_comp,Chebyshev.map_T,Polynomial.map_sub,Polynomial.map_one,
    Polynomial.map_mul,Polynomial.map_ofNat,map_X,eval_comp,eval_sub,eval_one,eval_mul,eval_ofNat,eval_X]
    using abs_eval_T_real_le_one (n:ℤ) hz

theorem integerChebyshev_mass (a : List ℤ) (j : ℕ) {z : ℝ} (hz : |1-2*z|≤1) :
    |((integerChebyshev a j).map (Int.castRingHom ℝ)).eval z|≤(coefficientMass a:ℝ) := by
  induction a generalizing j with
  | nil => simp [integerChebyshev,coefficientMass]
  | cons c a ih =>
    simp only [integerChebyshev,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Int.coe_castRingHom,
      eval_add,eval_mul,eval_C,coefficientMass,List.map_cons,List.sum_cons,Nat.cast_add]
    apply (abs_add_le ..).trans
    apply add_le_add _ (ih _)
    rw [abs_mul]
    apply (mul_le_of_le_one_right (abs_nonneg _) (shifted_eval hz j)).trans_eq
    rw [← Int.cast_abs,← Int.natCast_natAbs,Int.cast_natCast]

theorem unpacked_mass (a : List ℤ) (b : ℕ) (small : (coefficientMass a:ℤ)*7^a.length<2^b)
    {z : ℝ} (hz : |1-2*z|≤1) : |(realDense (unpackCheb b a)).eval z|≤(coefficientMass a:ℝ) := by
  rw [realDense,unpackCheb_poly _ _ small]
  exact integerChebyshev_mass a 0 hz

end CentralUnimodality.PolynomialTrial
