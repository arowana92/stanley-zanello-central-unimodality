module

public import CentralUnimodality.StridedSpatialMoments
public import CentralUnimodality.BlockRadixDigits
public meta import CentralUnimodality.StridedSpatialMoments
public meta import CentralUnimodality.BlockRadixDigits
import Mathlib.Tactic.Eval

/-! Compute the 514 moments simultaneously as centered digits of three
integer products. The mass bound below prevents carries from changing
any signed polynomial coefficient. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial

set_option maxRecDepth 40000
set_option maxHeartbeats 0
set_option Elab.async false

private def w0 : List ℤ := eval% weightBand spatialWeights 0
private def q0 : List ℤ := eval% quotientBand 0
private theorem w0_eq : weightBand spatialWeights 0=w0 := by decide +kernel
private theorem q0_eq : quotientBand 0=q0 := by decide +kernel

private def w1 : List ℤ := eval% weightBand spatialWeights 1
private def q1 : List ℤ := eval% quotientBand 1
private theorem w1_eq : weightBand spatialWeights 1=w1 := by decide +kernel
private theorem q1_eq : quotientBand 1=q1 := by decide +kernel

private def w2 : List ℤ := eval% weightBand spatialWeights 2
private def q2 : List ℤ := eval% quotientBand 2
private theorem w2_eq : weightBand spatialWeights 2=w2 := by decide +kernel
private theorem q2_eq : quotientBand 2=q2 := by decide +kernel

private def packedBands : ℤ :=
  packDense 8193 w0*packDense 8193 q0+packDense 8193 w1*packDense 8193 q1+
    packDense 8193 w2*packDense 8193 q2

private noncomputable def momentInteger : ℤ := eval% packedBands
private theorem packed_exact : packedBands=momentInteger := by decide +kernel

private def momentDigits : List ℤ := eval% blockCenteredDigits 8192 10 794 packedBands
private theorem digits_exact : blockCenteredDigits 8192 10 794 momentInteger=momentDigits := by decide +kernel

private theorem moment_lookup : (List.range 514).all (fun i =>
    spatialMoments[i]? == momentDigits[i+140]?)=true := by decide +kernel

private noncomputable def momentProduct : ℤ[X] :=
  bandProduct spatialWeights 0+bandProduct spatialWeights 1+bandProduct spatialWeights 2

private theorem moment_eval : momentProduct.eval (2^8193)=momentInteger := by
  rw [← packed_exact]
  simp only [momentProduct,bandProduct,eval_add,eval_mul,← packDense_eval,w0_eq,w1_eq,w2_eq,q0_eq,q1_eq,q2_eq]
  rfl

private theorem moment_small (i : ℕ) : |momentProduct.coeff i|<2^8192 := by
  have mass : (coefficientMass w0:ℤ)*coefficientMass q0+coefficientMass w1* (coefficientMass q1:ℤ)+
      coefficientMass w2*(coefficientMass q2:ℤ)<2^8192 := by decide +kernel
  rw [momentProduct,coeff_add,coeff_add]
  refine lt_of_le_of_lt ((abs_add_le ..).trans (add_le_add (abs_add_le ..) (le_refl _))) ?_
  refine lt_of_le_of_lt ?_ mass
  simp only [bandProduct,w0_eq,w1_eq,w2_eq,q0_eq,q1_eq,q2_eq]
  exact add_le_add (add_le_add (dense_product_bound _ _ i) (dense_product_bound _ _ i)) (dense_product_bound _ _ i)

theorem spatial_moment_at {i : ℕ} (hi : i<514) : spatialMoments[i]?=some (momentAtIndex i) := by
  have cert := List.all_eq_true.mp moment_lookup i (List.mem_range.mpr hi)
  have digit := centeredDigits_coeff momentProduct 8192 794 moment_small (by omega : i+140<794)
  rw [← blockCenteredDigits_exact 8192 10,moment_eval,digits_exact] at digit
  rw [beq_iff_eq] at cert
  rw [cert,digit]
  congr 1
  rw [momentAtIndex,unit_by_bands (by decide +kernel),momentProduct,coeff_add,coeff_add,
    band_product_coeff _ _ _ hi,band_product_coeff _ _ _ hi,band_product_coeff _ _ _ hi]

end CentralUnimodality.PolynomialTrial
