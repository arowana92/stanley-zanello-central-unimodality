module

public import CentralUnimodality.IntegerBetaProduct
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Algebra.Polynomial

/-! Exact sign tests on a real interval by a linear fractional change
of variable. A polynomial with nonnegative coefficients is nonnegative
on the half line. Continuity includes the right endpoint. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Polynomial Set

def mulLinear (a b : ℤ) (p : List ℤ) : List ℤ := linearRows a b p (0::p)

def projectiveRows (l h q : ℤ) : List ℤ → List ℤ × List ℤ
  | [] => ([],[1])
  | c::p =>
    let (v,d) := projectiveRows l h q p
    let next := mulLinear q q d
    (linearRows 1 c (mulLinear l h v) next,next)

private theorem dense_cons_real (c : ℤ) (a : List ℤ) (t : ℝ) :
    (realDense (c::a)).eval t=(c:ℝ)+t*(realDense a).eval t := by
  simp [realDense,densePoly]

theorem dense_linear_eval (p q : ℤ) (a b : List ℤ) (t : ℝ) :
    (realDense (linearRows p q a b)).eval t=(p:ℝ)*(realDense a).eval t+(q:ℝ)*(realDense b).eval t := by
  simp [realDense,dense_linear]

private theorem mulLinear_eval (p q : ℤ) (a : List ℤ) (t : ℝ) :
    (realDense (mulLinear p q a)).eval t=((p:ℝ)+q*t)*(realDense a).eval t := by
  rw [mulLinear,dense_linear_eval,dense_cons_real]; push_cast; ring

theorem projective_eval (l h q : ℤ) (a : List ℤ) (t : ℝ) (nz : (q:ℝ)+q*t≠0) :
    (realDense (projectiveRows l h q a).1).eval t=((q:ℝ)+q*t)^a.length*
      (realDense a).eval (((l:ℝ)+h*t)/(q+q*t)) ∧
    (realDense (projectiveRows l h q a).2).eval t=((q:ℝ)+q*t)^a.length := by
  induction a with
  | nil => simp [projectiveRows,realDense,densePoly]
  | cons c a ih =>
    simp only [projectiveRows,dense_linear_eval,mulLinear_eval,ih,List.length_cons,dense_cons_real,
      pow_succ,Int.cast_one,one_mul]
    constructor
    · set D := (q:ℝ)+q*t
      set U := (l:ℝ)+h*t
      set E := (realDense a).eval (U/D)
      field_simp [nz]; ring
    · ring

private theorem dense_nonneg {a : List ℤ} (h : ∀ c∈a, 0≤c) {t : ℝ} (ht : 0≤t) :
    0≤(realDense a).eval t := by
  induction a with
  | nil => simp [realDense,densePoly]
  | cons c a ih =>
    rw [dense_cons_real]
    exact add_nonneg (by exact_mod_cast h c List.mem_cons_self)
      (mul_nonneg ht (ih (fun d hd => h d (List.mem_cons_of_mem _ hd))))

def rowTest (m b : ℤ) (p : List ℤ × List ℤ) : Bool :=
  (linearRows m (-b) p.1 p.2).all (fun c => decide (0≤c))

theorem projective_bound (l h q m b : ℤ) (a : List ℤ) (hpos : l<h) (qpos : 0<q)
    (test : rowTest m b (projectiveRows l h q a)=true) {x : ℝ}
    (hx : x∈Icc ((l:ℝ)/q) ((h:ℝ)/q)) : (b:ℝ)≤m*(realDense a).eval x := by
  have hq : 0<(q:ℝ) := by exact_mod_cast qpos
  have bounds : (l:ℝ)/q<(h:ℝ)/q := div_lt_div_of_pos_right (by exact_mod_cast hpos) hq
  have hc : IsClosed {s : ℝ | (b:ℝ)≤m*(realDense a).eval s} :=
    isClosed_le continuous_const (continuous_const.mul (realDense a).continuous)
  have H : Ico ((l:ℝ)/q) ((h:ℝ)/q) ⊆ {s : ℝ | (b:ℝ)≤m*(realDense a).eval s} := by
    intro s hs
    have hi := (lt_div_iff₀ hq).mp hs.2
    have lo := (div_le_iff₀ hq).mp hs.1
    let t := (s*q-l)/(h-s*q)
    have ht : 0≤t := div_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr hi.le)
    have pos : 0<(q:ℝ)+q*t := by positivity
    have back : ((l:ℝ)+h*t)/(q+q*t)=s := by
      apply (div_eq_iff pos.ne').mpr
      dsimp [t]
      field_simp [(sub_pos.mpr hi).ne']; ring
    have v := dense_nonneg (fun c hc => of_decide_eq_true (List.all_eq_true.mp test c hc)) ht
    have e := projective_eval l h q a t pos.ne'
    rw [dense_linear_eval,e.1,e.2,back,Int.cast_neg] at v
    apply sub_nonneg.mp
    apply nonneg_of_mul_nonneg_right (a:=((q:ℝ)+q*t)^a.length) _ (pow_pos pos _)
    linarith only [v]
  have cov := closure_minimal H hc
  rw [closure_Ico bounds.ne] at cov
  exact cov hx

end CentralUnimodality.PolynomialTrial
