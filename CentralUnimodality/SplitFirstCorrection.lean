module

public import CentralUnimodality.ArcsineDifferentiation
public import CentralUnimodality.CorrectedArcsineQuadrature
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The first binomial correction equals a difference of differential
operators on the beta product and its factors. This form only uses
values of the polynomial on the retained frequency interval. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Polynomial Set

theorem arc_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    arc (fun x => f x+g x)=arc f+arc g := by
  rw [arc,intervalIntegral.integral_add,arc,arc,add_div]
  all_goals apply Continuous.intervalIntegrable; fun_prop

noncomputable def splitFactor (B F : ℝ[X]) (v x : ℝ) := B.eval (v*x)*F.eval (v*(1-x))

noncomputable def splitSpace2 (B F : ℝ[X]) (v x : ℝ) :=
  v^2*(splitFactor (derivative (derivative B)) F v x-
    2*splitFactor (derivative B) (derivative F) v x+splitFactor B (derivative (derivative F)) v x)

noncomputable def quadraticJet (B F : ℝ[X]) (v x : ℝ) :=
  splitFactor (derivative (derivative B)) F v x-
    2*splitFactor (derivative B) (derivative F) v x+splitFactor B (derivative (derivative F)) v x

noncomputable def halfDrift (B : ℝ[X]) : ℝ[X] := C (1/2:ℝ)*(derivative B+X*derivative (derivative B))
noncomputable def fullDrift (B : ℝ[X]) : ℝ[X] := derivative B+C (1/2:ℝ)*X*derivative (derivative B)

theorem split_space_derivative (P Q : ℝ[X]) (v x : ℝ) : HasDerivAt (splitFactor P Q v)
    (v*(splitFactor (derivative P) Q v x-splitFactor P (derivative Q) v x)) x := by
  have left := (P.hasDerivAt (v*x)).comp x ((hasDerivAt_id x).const_mul v)
  have right := (Q.hasDerivAt (v*(1-x))).comp x (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).const_mul v)
  convert left.mul right using 1
  · rfl
  · dsimp [splitFactor]; ring

theorem quadratic_jet_correction (B F : ℝ[X]) (v : ℝ) :
    v*arc (fun x => x*(1-x)*quadraticJet B F v x)=2*((fullDrift (betaProduct B F)).eval v-
      (betaProduct (halfDrift B) F+betaProduct B (halfDrift F)).eval v) := by
  let S := splitFactor
  let B1 := derivative B
  let F1 := derivative F
  let B2 := derivative B1
  let F2 := derivative F1
  let T := fun w x => x*S B1 F w x+(1-x)*S B F1 w x
  let U := fun w x => x^2*S B2 F w x+(2*x*(1-x))*S B1 F1 w x+(1-x)^2*S B F2 w x
  let X1 := fun x => S B1 F v x-S B F1 v x
  let X2 := fun x => v*quadraticJet B F v x
  let H := betaProduct B F
  have cS (P Q : ℝ[X]) : Continuous (splitFactor P Q).uncurry := by
    change Continuous (fun p : ℝ × ℝ => P.eval (p.1*p.2)*Q.eval (p.1*(1-p.2)))
    fun_prop
  have slice (P Q : ℝ[X]) : Continuous (splitFactor P Q v) :=
    (cS P Q).comp (continuous_const.prodMk continuous_id)
  have time (P Q : ℝ[X]) (w x : ℝ) : HasDerivAt (fun t => S P Q t x)
      (x*S (derivative P) Q w x+(1-x)*S P (derivative Q) w x) w := by
    have left := (P.hasDerivAt (w*x)).comp w ((hasDerivAt_id w).mul_const x)
    have right := (Q.hasDerivAt (w*(1-x))).comp w ((hasDerivAt_id w).mul_const (1-x))
    convert left.mul right using 1
    · rfl
    · dsimp [S,splitFactor]; ring
  have tt (w x : ℝ) : HasDerivAt (fun t => T t x) (U w x) w := by
    convert ((time B1 F w x).const_mul x).add ((time B F1 w x).const_mul (1-x)) using 1
    dsimp only [T,U,B2,F2,B1,F1]; ring
  have xx (x : ℝ) : HasDerivAt X1 (X2 x) x := by
    convert (split_space_derivative B1 F v x).sub (split_space_derivative B F1 v x) using 1
    dsimp only [X2,quadraticJet,S,B1,F1]; ring
  have cT : Continuous T.uncurry := by dsimp [T,S,splitFactor,Function.uncurry]; fun_prop
  have cU : Continuous U.uncurry := by dsimp [U,S,splitFactor,Function.uncurry]; fun_prop
  have cX : Continuous X2 := by
    change Continuous (fun x => v*(S B2 F v x-2*S B1 F1 v x+S B F2 v x))
    exact continuous_const.mul (((slice _ _).sub (continuous_const.mul (slice _ _))).add (slice _ _))
  have first (w : ℝ) : arc (T w)=(derivative H).eval w := by
    have D := (arc_parameter (cS B F) cT (time B F) w).deriv
    have eq : (fun t => arc (splitFactor B F t))=fun t => H.eval t :=
      funext (fun t => arc_polynomial t B F)
    rw [eq,(H.hasDerivAt w).deriv] at D
    exact D.symm
  have second : arc (U v)=(derivative (derivative H)).eval v := by
    have D := (arc_parameter cT cU tt v).deriv
    rw [funext first,((derivative H).hasDerivAt v).deriv] at D
    exact D.symm
  have st := arc_stein xx cX
  let V := fun x => splitFactor (halfDrift B) F v x+splitFactor B (halfDrift F) v x
  have cv : Continuous V := (slice _ _).add (slice _ _)
  have Vint : arc V=(betaProduct (halfDrift B) F+betaProduct B (halfDrift F)).eval v := by
    rw [eval_add,← arc_polynomial,← arc_polynomial]; exact arc_add (slice _ _) (slice _ _)
  have ctv : Continuous (T v) := cT.comp (continuous_const.prodMk continuous_id)
  have cuv : Continuous (U v) := cU.comp (continuous_const.prodMk continuous_id)
  have cX1 := continuous_iff_continuousAt.mpr (fun x => (xx x).continuousAt)
  have identity (x : ℝ) : 2*(T v x+(v/2)*U v x-V x)=(2*x-1)*X1 x-x*(1-x)*X2 x := by
    dsimp [T,U,V,X1,X2,S,quadraticJet,splitFactor,halfDrift,B2,F2,B1,F1]
    simp only [eval_mul,eval_add,eval_C,eval_X]; ring
  have integrated := arc_congr (fun x _ => identity x)
  rw [arc_const_mul,arc_sub (f:=fun x => T v x+v/2*U v x) (g:=V) (ctv.add (continuous_const.mul cuv)) cv,
    arc_add (f:=T v) (g:=fun x => v/2*U v x) ctv (continuous_const.mul cuv),arc_const_mul,
    arc_sub (f:=fun x => (2*x-1)*X1 x) (g:=fun x => x*(1-x)*X2 x) (by fun_prop) (by fun_prop),
    st,first,second,Vint] at integrated
  have pull : arc (fun x => x*(1-x)*X2 x)=v*arc (fun x => x*(1-x)*quadraticJet B F v x) := by
    rw [← arc_const_mul]; apply arc_congr; intro x _; dsimp only [X2]; ring
  rw [pull] at integrated
  dsimp only [H] at integrated
  simp only [fullDrift,eval_add,eval_mul,eval_C,eval_X] at integrated ⊢
  linarith only [integrated]

theorem split_first_correction (B F : ℝ[X]) (v : ℝ) :
    arc (fun x => x*(1-x)*splitSpace2 B F v x)=2*v*((fullDrift (betaProduct B F)).eval v-
      (betaProduct (halfDrift B) F+betaProduct B (halfDrift F)).eval v) := by
  have eq : arc (fun x => x*(1-x)*splitSpace2 B F v x)=v^2*arc (fun x => x*(1-x)*quadraticJet B F v x) := by
    rw [← arc_const_mul]; apply arc_congr; intro x _; unfold splitSpace2 quadraticJet; ring
  rw [eq,pow_two,mul_assoc,quadratic_jet_correction]; ring

end CentralUnimodality.ReturnSplit
