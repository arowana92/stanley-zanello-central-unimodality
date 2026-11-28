module

public import CentralUnimodality.SpatialIntegralWitnesses
public import CentralUnimodality.PolynomialTrialBounds
import Mathlib.Algebra.BigOperators.Intervals

/-! The even reciprocal moments use just three products. Within each
residue class of the weight index modulo three, incrementing the moment
index shifts the reciprocal sequence by one place. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial

set_option maxRecDepth 4000


def weightBand (w : List ℤ) (s : ℕ) :=
  (List.range 141).map fun j => entry w (3*(140-j)+s)

def quotientBand (s : ℕ) : List ℤ :=
  (List.range 654).map fun t => (common4000/(6*t+3+2*s):ℕ)

def momentTerm (w : List ℤ) (m t s : ℕ) :=
  entry w (3*t+s)*(common4000/(6*(m+t)+3+2*s):ℕ)

private theorem unit_as_sum (q : ℕ → ℕ) (n : ℕ) (w : List ℤ) (k : ℕ) (h : w.length≤n) :
    unitNumerator q w k=∑ j ∈ Finset.range n, entry w j*(q (k+2*j+1):ℤ) := by
  induction n generalizing w k with
  | zero =>
    have z : w=[] := List.length_eq_zero_iff.mp (by omega)
    simp [z,unitNumerator]
  | succ n ih =>
    cases w with
    | nil => simp [unitNumerator,entry]
    | cons c w =>
      have le : w.length≤n := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using h
      rw [unitNumerator,ih _ _ le,Finset.sum_range_succ']
      simp only [entry,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,mul_zero,add_zero,add_comm (c*_)]
      congr 1
      apply Finset.sum_congr rfl; intro j _
      rw [show k+2+2*j+1=k+2*(j+1)+1 by omega]

private theorem triple_range (H : ℕ → ℤ) (n : ℕ) :
    (∑ j ∈ Finset.range (3*n), H j)=∑ t ∈ Finset.range n, (H (3*t)+H (3*t+1)+H (3*t+2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,Finset.sum_range_succ (n:=n)]
    simp only [Finset.sum_range_succ,ih]; abel

theorem unit_by_bands {w : List ℤ} (hw : w.length≤423) (m : ℕ) :
    unitNumerator (fun k => common4000/k) w (6*m+2)=
      (∑ t ∈ Finset.range 141, momentTerm w m t 0)+(∑ t ∈ Finset.range 141, momentTerm w m t 1)+
      ∑ t ∈ Finset.range 141, momentTerm w m t 2 := by
  rw [unit_as_sum _ 423 w _ hw,show 423=3*141 by decide,triple_range,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro t _
  dsimp only [momentTerm]
  simp only [Nat.add_zero,Nat.mul_zero]
  rw [show 6*m+2+2*(3*t)+1=6*(m+t)+3 by omega,
      show 6*m+2+2*(3*t+1)+1=6*(m+t)+3+2*1 by omega,
      show 6*m+2+2*(3*t+2)+1=6*(m+t)+3+2*2 by omega]

noncomputable def bandProduct (w : List ℤ) (s : ℕ) := densePoly (weightBand w s)*densePoly (quotientBand s)

theorem band_product_coeff (w : List ℤ) (s m : ℕ) (hm : m<514) :
    (bandProduct w s).coeff (m+140)=∑ t ∈ Finset.range 141, momentTerm w m t s := by
  let f := fun j => (densePoly (weightBand w s)).coeff j*(densePoly (quotientBand s)).coeff (m+140-j)
  have cut : (∑ j ∈ Finset.range 141, f j)=∑ j ∈ Finset.range (m+140+1), f j :=
    Finset.sum_subset (Finset.range_mono (by omega)) (fun j _ h => by
      have out : (weightBand w s).length≤j := by simp only [weightBand,List.length_map,List.length_range]; simpa using h
      simp [f,dense_coeff,List.getElem?_eq_none out])
  rw [bandProduct,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ j ∈ Finset.range (m+140+1), f j)=_
  rw [← cut,← Finset.sum_range_reflect (fun t => momentTerm w m t s) 141]
  apply Finset.sum_congr rfl; intro j hj
  have jl := Finset.mem_range.mp hj
  have ql : m+140-j<654 := by omega
  simp only [f,dense_coeff,weightBand,quotientBand,List.getElem?_map,List.getElem?_range jl,
    List.getElem?_range ql,Option.map_some,Option.getD_some,momentTerm]
  rw [show m+140-j=m+(140-j) by omega]

end CentralUnimodality.PolynomialTrial
