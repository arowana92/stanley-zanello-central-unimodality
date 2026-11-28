module

public import CentralUnimodality.QuadraticSplitResidual
public import CentralUnimodality.CellConditioning

/-! Apply the first-return inverse to the signed quadratic residual and
the cubic remainder separately, retaining the elapsed-time discount. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real ReturnSplit Set Witness

private theorem conditioned_linear (N : ℕ) (D A B : ℕ → ℝ) (s : ℝ) :
    conditionedCost N (fun j => D j*(A j+s*B j))=
      conditionedCost N (fun j => D j*A j)+s*conditionedCost N (fun j => D j*B j) := by
  have prod (j : ℕ) : returnMass j*(D (N-j)*(A (N-j)+s*B (N-j)))=
      returnMass j*(D (N-j)*A (N-j))+s*(returnMass j*(D (N-j)*B (N-j))) := by ring
  simp only [conditionedCost,prod,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

theorem quadratic_amplitude_of_costs {n δ i : ℕ} (hs : δ≤1) (hn : 10000≤n+δ) (hi : i<228)
    {ξ : ℝ} (hξ : |ξ|≤1728) (hu : |ξ|^(2/3:ℝ)∈halfInterval i) (A B : ℕ → ℝ)
    (second : ∀ j≤n+δ, let τ := |ξ|^(2/3:ℝ)/(n+δ:ℕ)
      |secondCurveResidual (value candidate) (correctedValue (1-δ)) (1-δ) ((j:ℝ)*τ)|≤A j)
    (cubic : ∀ j≤n+δ, let τ := |ξ|^(2/3:ℝ)/(n+δ:ℕ); let v := (j:ℝ)*τ
      ‖parityResidual (ξ/cellScale (n+δ)/2) (correctedSeries (1-δ) τ) (1-δ) j-
        ((curveResidual (value candidate) v+τ*firstCurveResidual (value candidate) (correctedValue (1-δ)) (1-δ) v+
          τ^2*secondCurveResidual (value candidate) (correctedValue (1-δ)) (1-δ) v:ℝ):ℂ)‖≤τ^3*B j) :
    let N := n+δ; let u := |ξ|^(2/3:ℝ); let τ := u/(N:ℝ); let D := timeDiscount i N u
    |signedAmplitude n δ (ξ/cellScale N)-value candidate u|≤
      (1+|ξ|/2)*(15/10^16)+(36/10^14)*u+4*sqrt N*τ*(3/10^12)+
      τ^2*conditionedCost N (fun j => D j*A j)+τ^3*conditionedCost N (fun j => D j*B j)+
      τ*|correctedValue (1-δ) u| := by
  let N := n+δ
  let u := |ξ|^(2/3:ℝ)
  let τ := u/(N:ℝ)
  let σ := 1-δ
  let D := timeDiscount i N u
  have n0 : 0<N := by dsimp [N]; omega
  have np : (0:ℝ)<N := by exact_mod_cast n0
  have nr : (10000:ℝ)≤N := by exact_mod_cast hn
  have scale := peak_frequency_scale n0 hξ
  have t0 : 0≤τ := div_nonneg scale.1.1 np.le
  have top : u≤114 := by
    have h : u≤((i:ℝ)+1)/2 := by exact_mod_cast hu.2
    have i' : (i:ℝ)≤227 := by exact_mod_cast (by omega : i≤227)
    linarith only [h,i']
  have step : τ≤0.02 := (div_le_div₀ (by norm_num : (0:ℝ)≤114) top (by norm_num : (0:ℝ)<10000) nr).trans (by norm_num)
  have endpoint : (N:ℝ)*τ=u := by dsimp only [τ]; field_simp
  have current : cappedBin i u=i := by
    apply min_eq_left
    apply (Nat.le_floor_iff (by positivity : 0≤2*u)).mpr
    have lo : (i:ℝ)/2≤u := hu.1
    linarith only [lo]
  have dEnd : D N=1 := by
    change (returnDiscount i (cappedBin i ((N:ℝ)*τ)):ℝ)=1
    simp [endpoint,current]
  have unit (j : ℕ) (_ : j≤N) : D j≤1 := by
    unfold D timeDiscount
    exact_mod_cast (discount_bounds i _).2
  have symbol (j : ℕ) (hj : j≤N) : ‖returnSymbol (ξ/cellScale N/2) j‖≤returnMass j*D (N-j) :=
    return_symbol_discount n0 hj hu step scale.2
  have h := corrected_amplitude_of_weighted_costs hs n0 hξ (fun j => A j+τ*B j) D dEnd unit symbol
    (fun v hv => certified_first_correction (by omega) hv)
  have cost (j : ℕ) (hj : j≤N) :
      let v := (j:ℝ)*τ
      ‖parityResidual (ξ/cellScale N/2) (correctedSeries σ τ) σ j-
        ((curveResidual (value candidate) v+τ*firstCurveResidual (value candidate) (correctedValue σ) σ v:ℝ):ℂ)‖
        ≤τ^2*(A j+τ*B j) := by
    let v := (j:ℝ)*τ
    let S := curveResidual (value candidate) v+τ*firstCurveResidual (value candidate) (correctedValue σ) σ v
    let R := secondCurveResidual (value candidate) (correctedValue σ) σ v
    let Z := parityResidual (ξ/cellScale N/2) (correctedSeries σ τ) σ j
    have tr := norm_sub_le_norm_sub_add_norm_sub Z ((S+τ^2*R:ℝ):ℂ) (S:ℂ)
    have err : ‖Z-((S+τ^2*R:ℝ):ℂ)‖≤τ^3*B j := cubic j hj
    have re : |R|≤A j := second j hj
    rw [← Complex.ofReal_sub,add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg τ)] at tr
    exact tr.trans ((add_le_add err (mul_le_mul_of_nonneg_left re (sq_nonneg τ))).trans_eq (by ring))
  have total := h cost
  rw [conditioned_linear] at total
  apply total.trans_eq
  ring

end CentralUnimodality.PolynomialTrial
