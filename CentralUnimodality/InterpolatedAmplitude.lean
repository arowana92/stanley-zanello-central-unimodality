module

public import CentralUnimodality.PointInterpolationCost
public import CentralUnimodality.RolleInterpolation

/-! Approximate the signed amplitude by interpolating the cosine on the
positive area axis. The nodal products have small checked second moments. -/
@[expose] public section

namespace CentralUnimodality.Witness
open Laurent Polynomial Real

def rationalNodes := interpolationNodes 0++interpolationNodes 1

noncomputable def areaNodes : Finset ℝ :=
  rationalNodes.toFinset.map ⟨fun q : ℚ => (q:ℝ),Rat.cast_injective⟩

private theorem areaNodes_card : areaNodes.card=20 := by
  rw [areaNodes,Finset.card_map]; decide +kernel

private theorem product_nodes (x : ℝ) :
    (∏ a ∈ areaNodes, (x-a))=nodeProduct 0 x*nodeProduct 1 x := by
  have nd : rationalNodes.Nodup := by decide +kernel
  rw [areaNodes,Finset.prod_map]
  change (∏ a ∈ rationalNodes.toFinset, (x-(a:ℝ)))=_
  rw [List.prod_toFinset (fun q : ℚ => x-(q:ℝ)) nd,rationalNodes,List.map_append,List.prod_append]
  rfl

noncomputable def areaInterpolant (ξ : ℝ) : ℝ[X] :=
  Lagrange.interpolate areaNodes id (fun x => cos (ξ*x))

private theorem interpolant_degree (ξ : ℝ) : (areaInterpolant ξ).degree < ((20:ℕ):WithBot ℕ) := by
  simpa only [areaInterpolant,areaNodes_card] using
    (Lagrange.degree_interpolate_lt (s:=areaNodes) (v:=id) (fun x => cos (ξ*x)) (fun _ _ _ _ eq => eq))

private theorem node_error (ξ x : ℝ) :
    |cos (ξ*x)-(areaInterpolant ξ).eval x| ≤
      ((|ξ|^20/(20:ℕ).factorial)/2)*(nodeProduct 0 x^2+nodeProduct 1 x^2) := by
  have smooth : ContDiff ℝ 20 (fun u => cos (ξ*u)) := by fun_prop
  have atNodes (a : ℝ) (ha : a∈areaNodes) : (areaInterpolant ξ).eval a=cos (ξ*a) :=
    Lagrange.eval_interpolate_at_node (s:=areaNodes) (v:=id) (fun x => cos (ξ*x)) (fun _ _ _ _ eq => eq) ha
  have bound (y : ℝ) : |iteratedDeriv 20 (fun u => cos (ξ*u)) y|≤|ξ|^20 := by
    rw [iteratedDeriv_comp_const_mul Real.contDiff_cos ξ]
    change |ξ^20*iteratedDeriv (2*10) cos (ξ*y)|≤_
    rw [iteratedDeriv_even_cos]
    simp only [Pi.mul_apply,Pi.pow_apply,Pi.neg_apply,Pi.one_apply]
    norm_num only [even_two,Even.neg_one_pow,one_mul]
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one _)
  have h := Interpolation.interpolation_error areaNodes areaNodes_card _ smooth _ (interpolant_degree ξ)
    atNodes (by positivity : 0≤|ξ|^20) bound x
  rw [product_nodes,abs_mul] at h
  apply h.trans
  have sqs := sq_nonneg (|nodeProduct 0 x|-|nodeProduct 1 x|)
  have am : |nodeProduct 0 x| * |nodeProduct 1 x| ≤ (nodeProduct 0 x^2+nodeProduct 1 x^2)/2 := by
    nlinarith only [sqs,sq_abs (nodeProduct 0 x),sq_abs (nodeProduct 1 x)]
  exact (mul_le_mul_of_nonneg_left am (by positivity)).trans_eq (by ring)

def pointMomentRow (δ r : ℕ) :=
  polynomialFromCell (lookup (pointsFromCells (sourceCells δ) 21) r) r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem all_moment_rows :
    (List.range 20).all (fun r => (pointMomentRow 0 r).isSome)=true ∧
    (List.range 20).all (fun r => (pointMomentRow 1 r).isSome)=true := by decide +kernel

noncomputable def tabulatedPointValue (N δ r : ℕ) : ℝ :=
  (if r%2=0 then 1 else wallisFactor N)*horner (N:ℝ)⁻¹ ((pointMomentRow δ r).getD [])

private theorem tabulated_value {n δ r : ℕ} (hδ : δ≤1) (hn : 0<n+δ) (hr : r<20) :
    pointMoment n δ r=tabulatedPointValue (n+δ) δ r := by
  have ok : (List.range 20).all (fun r => (pointMomentRow δ r).isSome)=true := by
    rcases (by omega : δ=0 ∨ δ=1) with rfl|rfl
    · exact all_moment_rows.1
    · exact all_moment_rows.2
  have he := List.all_eq_true.mp ok r (List.mem_range.mpr hr)
  cases row : pointMomentRow δ r with
  | none => simp [row] at he
  | some p =>
    rw [tabulatedPointValue,row,Option.getD_some]
    exact tabulated_point_moment hδ hn (by omega) row

/-- Only the twenty cosine values at the rational nodes, the positive-branch
moment polynomials and the Wallis factor enter this finite quadrature. -/
noncomputable def areaQuadrature (N δ : ℕ) (ξ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 20, (areaInterpolant ξ).coeff j*tabulatedPointValue N δ j

private theorem mean_interpolant {n δ : ℕ} (hδ : δ≤1) (hn : 0<n+δ) (ξ : ℝ) :
    rankMean n δ (fun i => (areaInterpolant ξ).eval (scaledSite n δ i))=areaQuadrature (n+δ) δ ξ := by
  let p := areaInterpolant ξ
  have lt : p.natDegree<20 := by
    by_cases h : p=0
    · simp [h]
    · exact (natDegree_lt_iff_degree_lt h).mpr (interpolant_degree ξ)
  change rankMean n δ (fun i => p.eval (scaledSite n δ i))=_
  simp only [Polynomial.eval_eq_sum_range' lt,rankMean_sum,rankMean_mul,rankMean_power]
  apply Finset.sum_congr rfl
  intro j hj; rw [tabulated_value hδ hn (Finset.mem_range.mp hj)]

theorem interpolation_amplitude_error {n δ : ℕ} (hδ : δ≤1) (hn : 96≤n+δ) (ξ : ℝ) :
    |signedAmplitude n δ (ξ/cellScale (n+δ))-areaQuadrature (n+δ) δ ξ| ≤
      (|ξ|^20/(20:ℕ).factorial)/1000000000 := by
  let c := |ξ|^20/(20:ℕ).factorial
  let F := fun i => nodeProduct 0 (scaledSite n δ i)^2
  let G := fun i => nodeProduct 1 (scaledSite n δ i)^2
  rw [signedAmplitude_mean _ _ hδ,← mean_interpolant hδ (by omega),← rankMean_sub]
  have h := rankMean_bound n δ _ (fun i => (c/2)*(F i+G i)) (fun i _ => node_error ξ (scaledSite n δ i))
  have add : rankMean n δ (fun i => F i+G i)=rankMean n δ F+rankMean n δ G := by
    simp [rankMean,mul_add,Finset.sum_add_distrib,add_div]
  rw [rankMean_mul,add] at h
  apply h.trans
  have cost := add_le_add (node_product_cost (d:=0) hδ (by decide) hn)
    (node_product_cost (d:=1) hδ (by decide) hn)
  have scale : 0≤c/2 := by dsimp [c]; positivity
  exact (mul_le_mul_of_nonneg_left cost scale).trans_eq (by ring)

theorem interpolation_twelve {n δ : ℕ} (hδ : δ≤1) (hn : 96≤n+δ) {ξ : ℝ} (hξ : |ξ|≤12) :
    |signedAmplitude n δ (ξ/cellScale (n+δ))-areaQuadrature (n+δ) δ ξ| ≤ 1/600000 := by
  apply (interpolation_amplitude_error hδ hn ξ).trans
  calc
    _ ≤ ((12:ℝ)^20/(20:ℕ).factorial)/1000000000 := by gcongr
    _ ≤ _ := by norm_num [Nat.factorial]

end CentralUnimodality.Witness
