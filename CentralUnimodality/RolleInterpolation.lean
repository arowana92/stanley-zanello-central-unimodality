module

public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! A global interpolation remainder for a smooth real function at distinct
nodes. The nodal product can be averaged under the true partition law. -/
@[expose] public section

namespace CentralUnimodality.Interpolation
open Polynomial Set

private theorem rolle_sequence (n : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ n f)
    (x : Fin (n+1) → ℝ) (hx : StrictMono x) (hz : ∀ i, f (x i)=0) :
    ∃ y, iteratedDeriv n f y=0 := by
  induction n generalizing f with
  | zero => exact ⟨x 0,by simpa using hz 0⟩
  | succ n ih =>
    have gap (i : Fin (n+1)) : ∃ c ∈ Ioo (x i.castSucc) (x i.succ), deriv f c=0 :=
      exists_deriv_eq_zero (hx Fin.castSucc_lt_succ) hf.continuous.continuousOn
        ((hz _).trans (hz _).symm)
    choose y hy hyzero using gap
    have mono : StrictMono y := by
      intro i j hij
      have le : i.succ≤j.castSucc := by exact (show i.val<j.val from hij)
      exact (hy i).2.trans_le ((hx.monotone le).trans (hy j).1.le)
    obtain ⟨v,hv⟩ := ih (deriv f) hf.deriv' y mono hyzero
    exact ⟨v,by rwa [iteratedDeriv_succ']⟩

private theorem iterated_eval (n : ℕ) (p : ℝ[X]) :
    iteratedDeriv n p.eval=(derivative^[n] p).eval := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih,Function.iterate_succ_apply']
    funext x; exact Polynomial.deriv _

private theorem top_derivative {n : ℕ} (p : ℝ[X]) (h : p.natDegree≤n) (x : ℝ) :
    iteratedDeriv n p.eval x=(n.factorial:ℝ)*p.coeff n := by
  have eq : derivative^[n] p=C ((n.factorial:ℝ)*p.coeff n) := by
    ext k
    cases k with
    | zero => simp [coeff_iterate_derivative,Nat.descFactorial_self]
    | succ k =>
      rw [coeff_iterate_derivative,coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree<k+1+n)]
      simp
  rw [iterated_eval,eq]; exact eval_C

theorem interpolation_error (S : Finset ℝ) {n : ℕ} (hS : S.card=n) (f : ℝ → ℝ)
    (hf : ContDiff ℝ n f) (p : ℝ[X]) (hd : p.degree<(n:WithBot ℕ))
    (hmatch : ∀ a∈S, p.eval a=f a) {B : ℝ} (hB : 0≤B)
    (bound : ∀ y, |iteratedDeriv n f y|≤B) (x : ℝ) :
    |f x-p.eval x|≤B/(n.factorial:ℝ)*|∏ a ∈ S, (x-a)| := by
  classical
  by_cases hx : x∈S
  · rw [hmatch x hx,sub_self,abs_zero]; positivity
  let W := Lagrange.nodal S id
  have degW : W.natDegree=n := (Lagrange.natDegree_nodal ..).trans hS
  have coeffW : W.coeff n=1 := degW ▸ (monic_prod_X_sub_C id S).coeff_natDegree
  have valW (y : ℝ) : W.eval y=∏ a ∈ S, (y-a) := by simp [W,Lagrange.nodal,eval_prod]
  have nz : W.eval x≠0 := by
    rw [valW]; exact Finset.prod_ne_zero_iff.mpr (fun a ha => sub_ne_zero.mpr (fun eq => hx (eq ▸ ha)))
  let c := (f x-p.eval x)/W.eval x
  let Q : ℝ[X] := p+C c*W
  let g := fun t => f t - Q.eval t
  have Qsmooth : ContDiff ℝ n Q.eval := by simpa only [aeval_def,Algebra.algebraMap_self,eval₂_id] using Q.contDiff_aeval (𝕜:=ℝ) n
  have gsmooth : ContDiff ℝ n g := hf.sub Qsmooth
  let nodes := insert x S
  have card : nodes.card=n+1 := (Finset.card_insert_of_notMem hx).trans (by rw [hS])
  have zero (a : ℝ) (ha : a∈nodes) : g a=0 := by
    rcases Finset.mem_insert.mp ha with rfl|ha
    · dsimp only [g,Q,c]; rw [eval_add,eval_mul,eval_C,div_mul_cancel₀ _ nz]; ring
    · have root : W.eval a=0 := by rw [valW]; exact Finset.prod_eq_zero ha (sub_self a)
      simp [g,Q,root,hmatch a ha]
  obtain ⟨y,hy⟩ := rolle_sequence n g gsmooth (nodes.orderEmbOfFin card)
    (nodes.orderEmbOfFin card).strictMono (fun i => zero _ (nodes.orderEmbOfFin_mem card i))
  have degQ : Q.natDegree≤n := natDegree_add_le_of_degree_le
    (natDegree_le_of_degree_le hd.le) ((natDegree_C_mul_le _ _).trans degW.le)
  have rhs : Q.coeff n=c := by simp [Q,coeff_eq_zero_of_degree_lt hd,coeffW]
  have der : iteratedDeriv n f y = (n.factorial:ℝ)*c := by
    change iteratedDeriv n (f-Q.eval) y=0 at hy
    rw [iteratedDeriv_sub hf.contDiffAt Qsmooth.contDiffAt,top_derivative Q degQ,rhs] at hy
    exact sub_eq_zero.mp hy
  have bc := bound y
  rw [der,abs_mul,Nat.abs_cast] at bc
  have hc : |c|≤B/(n.factorial:ℝ) := (le_div_iff₀ (by positivity)).mpr (by linarith only [bc])
  have factor : f x-p.eval x=c*W.eval x := (div_mul_cancel₀ _ nz).symm
  rw [factor,abs_mul,valW]
  exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)

end CentralUnimodality.Interpolation
