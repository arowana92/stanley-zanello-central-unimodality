module

public import CentralUnimodality.CompactTrialMoments
public import CentralUnimodality.FourierPhaseTaylor
import Mathlib.Topology.Algebra.Polynomial

/-! The integer coefficient row of the spatial Taylor integral,
including the phase, factorials and exact monomial integrals. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Polynomial intervalIntegral

def momentTop (r D : ℕ) (a : List ℤ) := 3*(r+D+1)+2*a.length

def integralDen (r D : ℕ) (a : List ℤ) : ℕ :=
  momentDivisor (momentTop r D a)*4^a.length*2^120*D.factorial

def integratedCoeff (r factD : ℕ) (q : ℕ → ℕ) (weights : List ℤ) (j : ℕ) : ℤ :=
  let s := phaseInt (r+j)
  if s=0 then 0 else 3*s*(512:ℤ)^(r+j+1)*(factD/j.factorial:ℕ)*
    unitNumerator q weights (3*(r+j)+2)

def integratedRow (r D : ℕ) (a : List ℤ) : List ℤ :=
  let den := momentDivisor (momentTop r D a)
  let q := fun j => den/j
  let w := (quarterWeights a).1
  (List.range (D+1)).map (integratedCoeff r D.factorial q w)

theorem dense_range (n : ℕ) (f : ℕ → ℤ) (x : ℝ) :
    (realDense ((List.range n).map f)).eval x=∑ j ∈ Finset.range n, (f j:ℝ)*x^j := by
  induction n generalizing f with
  | zero => simp [realDense,densePoly]
  | succ n ih =>
    rw [List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [realDense,densePoly,Polynomial.map_add,Polynomial.map_C,Polynomial.map_mul,map_X,eval_add,
      eval_C,eval_mul,eval_X,Int.coe_castRingHom]
    change (f 0:ℝ)+x*(realDense ((List.range n).map (f ∘ Nat.succ))).eval x=_
    rw [ih,Finset.sum_range_succ',Finset.mul_sum]
    simp only [Function.comp_apply,pow_zero,mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _; rw [pow_succ]; ring

theorem integralDen_pos (r D : ℕ) (a : List ℤ) : 0 < integralDen r D a := by
  have h := momentDivisor_pos (momentTop r D a)
  have f := Nat.factorial_pos D
  unfold integralDen; positivity

private theorem coeff_normalized (r D : ℕ) (a : List ℤ) (j : ℕ) (hj : j≤D) :
    (integratedCoeff r D.factorial (fun j => momentDivisor (momentTop r D a)/j)
      (quarterWeights a).1 j:ℝ)=
      (integralDen r D a:ℝ)*(3*(phaseInt (r+j):ℝ)*512^(r+j+1)*unitMoment a (3*(r+j)+2)/
        ((2:ℝ)^120*j.factorial)) := by
  let top := momentTop r D a
  have moment := unitMoment_cleared (fun j => momentDivisor top/j)
    (D:=momentDivisor top) (top:=top) (fun j hj hk => reciprocal_exact hj hk) a (3*(r+j)+2)
    (by dsimp [top,momentTop]; omega)
  have fact : ((D.factorial/j.factorial:ℕ):ℝ)=(D.factorial:ℝ)/j.factorial := by
    apply (eq_div_iff (by positivity)).mpr
    exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial hj)
  rw [integratedCoeff]
  split_ifs with hz
  · simp [hz]
  · simp only [Int.cast_mul,Int.cast_ofNat,Int.cast_pow,Int.cast_natCast]
    rw [fact,← moment]
    simp only [integralDen,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,top]
    ring

noncomputable def integratedTaylor (r D : ℕ) (a : List ℤ) (x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, (1536*t^2)*((realDense a).eval (t^2/4)/2^120)*
    (512*t^3)^r*phaseTaylor r D (x*(512*t^3))

theorem integratedTaylor_exact (r D : ℕ) (a : List ℤ) (x : ℝ) :
    (realDense (integratedRow r D a)).eval x=(integralDen r D a:ℝ)*integratedTaylor r D a x := by
  let pre := fun j : ℕ => 3*(phaseInt (r+j):ℝ)*512^(r+j+1)*x^j/(2^120*j.factorial)
  let mon := fun j (t : ℝ) => pre j*(t^(3*(r+j)+2)*(realDense a).eval (t^2/4))
  have eq (t : ℝ) : (1536*t^2)*((realDense a).eval (t^2/4)/2^120)*(512*t^3)^r*
      phaseTaylor r D (x*(512*t^3))=∑ j ∈ Finset.range (D+1), mon j t := by
    rw [phaseTaylor,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [mon,pre]
    simp only [mul_pow,pow_add,pow_mul]; ring
  have cont : Continuous (fun t : ℝ => (realDense a).eval (t^2/4)) :=
    (realDense a).continuous.comp (by fun_prop)
  rw [integratedRow,dense_range,integratedTaylor]
  simp only [eq]
  rw [integral_finsetSum (fun j _ => by apply Continuous.intervalIntegrable; dsimp only [mon]; fun_prop),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_normalized _ _ _ _ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  dsimp only [mon]
  rw [integral_const_mul]
  change _=(integralDen r D a:ℝ)*(pre j*unitMoment a (3*(r+j)+2))
  dsimp only [pre]; ring

end CentralUnimodality.PolynomialTrial
