module

public import CentralUnimodality.ContinuousRankInversion
public import CentralUnimodality.Unimodality
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Continuous Fourier derivatives and a peak sign criterion at the
actual ranks, with no upper bound on the number of rows. -/
@[expose] public section

namespace CentralUnimodality.Witness

open Real intervalIntegral MeasureTheory Set Laurent

noncomputable def rankIntegralOrder (n δ r : ℕ) (x : ℝ) : ℝ :=
  ∫ ξ in 0..π*cellScale (n+δ), signedAmplitude n δ (ξ/cellScale (n+δ))*ξ^r*cos (x*ξ+r*π/2)

@[simp] theorem rankIntegralOrder_zero (n δ : ℕ) : rankIntegralOrder n δ 0=rankIntegral n δ := by
  funext x; simp [rankIntegralOrder,rankIntegral]

private theorem continuous_amplitude (n δ : ℕ) (hδ : δ≤1) :
    Continuous (fun ξ => signedAmplitude n δ (ξ/cellScale (n+δ))) := by
  simp_rw [signedAmplitude_mean _ _ hδ,rankMean]
  fun_prop

theorem rankIntegral_derivative (n δ r : ℕ) (hδ : δ≤1) (x : ℝ) :
    HasDerivAt (rankIntegralOrder n δ r) (rankIntegralOrder n δ (r+1) x) x := by
  let A := fun ξ => signedAmplitude n δ (ξ/cellScale (n+δ))
  let F := fun (i : ℕ) (z ξ : ℝ) => A ξ*ξ^i*cos (z*ξ+i*π/2)
  have hA : Continuous A := continuous_amplitude _ _ hδ
  have hF (i : ℕ) (z : ℝ) : Continuous (F i z) := by dsimp [F]; fun_prop
  have diff (z ξ : ℝ) : HasDerivAt (fun t => F r t ξ) (F (r+1) z ξ) z := by
    have inner : HasDerivAt (fun t : ℝ => t*ξ+(r:ℝ)*π/2) ξ z := by
      simpa using (((hasDerivAt_id z).mul_const ξ).add_const ((r:ℝ)*π/2))
    have H := inner.cos.const_mul (A ξ*ξ^r)
    have phase : z*ξ+(r+1:ℕ)*π/2=(z*ξ+r*π/2)+π/2 := by push_cast; ring
    convert H using 1
    dsimp only [F]
    rw [phase,cos_add_pi_div_two,pow_succ]; ring
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F r) (F':=F (r+1))
    (bound:=fun ξ => |A ξ*ξ^(r+1)|) (s:=univ) Filter.univ_mem _ _ _ _ _ _).2
  · exact Filter.Eventually.of_forall (fun z => (hF r z).aestronglyMeasurable)
  · exact (hF r x).intervalIntegrable _ _
  · exact (hF (r+1) x).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro ξ _ z _
    dsimp only [F]
    rw [Real.norm_eq_abs,abs_mul]
    simpa using mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg (A ξ*ξ^(r+1)))
  · apply Continuous.intervalIntegrable; fun_prop
  · exact Filter.Eventually.of_forall (fun ξ _ z _ => diff z ξ)

private theorem sample_sign_criterion {lo hi : ℕ} (hlh : lo≤hi) (row : ℕ → ℕ) (site : ℕ → ℝ)
    (mono : StrictMono site) {g d dd : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (d x) x)
    (hd : ∀ x, HasDerivAt d (dd x) x) {C a b : ℝ} (hc : 0<C)
    (samples : ∀ k ∈ Icc lo hi, g (site k)=C*(row k:ℝ))
    (left : ∀ x ∈ Icc (site lo) a, 0≤d x) (middle : ∀ x ∈ Icc a b, dd x≤0)
    (right : ∀ x ∈ Icc b (site hi), d x≤0) : UnimodalOn row lo hi := by
  apply (unimodalOn_iff_no_valley row hlh).mpr
  intro i j hli hij hjh hfall
  by_contra! rise
  have step (k : ℕ) (hk : lo≤k) (hl : k<hi) :
      ∃ x ∈ Ioo (site k) (site (k+1)), d x=(C*(row (k+1):ℝ)-C*(row k:ℝ))/(site (k+1)-site k) := by
    obtain ⟨x,hx,H⟩ := exists_hasDerivAt_eq_slope g d (mono (Nat.lt_succ_self k))
      ((continuous_iff_continuousAt.mpr (fun y => (hg y).continuousAt)).continuousOn) (fun y _ => hg y)
    exact ⟨x,hx,by rw [H,samples _ ⟨by omega,by omega⟩,samples _ ⟨hk,hl.le⟩]⟩
  obtain ⟨x,hx,H⟩ := step i hli (by omega)
  obtain ⟨y,hy,J⟩ := step j (by omega) hjh
  have neg : d x<0 := by
    rw [H]
    exact div_neg_of_neg_of_pos (sub_neg.mpr (mul_lt_mul_of_pos_left (by exact_mod_cast hfall) hc))
      (sub_pos.mpr (mono (Nat.lt_succ_self i)))
  have pos : 0<d y := by
    rw [J]
    exact div_pos (sub_pos.mpr (mul_lt_mul_of_pos_left (by exact_mod_cast rise) hc))
      (sub_pos.mpr (mono (Nat.lt_succ_self j)))
  have xy := hx.2.trans_le (mono.monotone (show i+1≤j by omega))
  have xy' := xy.trans hy.1
  have ax : a<x := by
    by_contra! h; exact neg.not_ge (left x ⟨(mono.monotone hli).trans hx.1.le,h⟩)
  have yb : y<b := by
    by_contra! h; exact pos.not_ge (right y ⟨h,hy.2.le.trans (mono.monotone (by omega))⟩)
  obtain ⟨z,hz,H⟩ := exists_hasDerivAt_eq_slope d dd xy'
    ((continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn) (fun t _ => hd t)
  have nonpos := middle z ⟨(ax.trans hz.1).le,(hz.2.trans yb).le⟩
  rw [H] at nonpos
  exact (div_pos (sub_pos.mpr (neg.trans pos)) (sub_pos.mpr xy')).not_ge nonpos

noncomputable def corankSite (n δ k : ℕ) : ℝ :=
  ((k:ℝ)+(3*n+2*δ+1:ℕ)/2)/cellScale (n+δ)

theorem unimodal_of_rank_integral_signs {n δ lo hi : ℕ} (hs : δ≤1) (hn : 0<n+δ)
    (hlh : lo≤hi) (hhi : hi≤n*(n+δ)) {a b : ℝ}
    (left : ∀ x ∈ Icc (corankSite n δ lo) a, 0≤rankIntegralOrder n δ 1 x)
    (middle : ∀ x ∈ Icc a b, rankIntegralOrder n δ 2 x≤0)
    (right : ∀ x ∈ Icc b (corankSite n δ hi), rankIntegralOrder n δ 1 x≤0) :
    UnimodalOn (fun k => rankCount (2*n+δ) (n*(n+δ)-k)) lo hi := by
  let D := n*(n+δ)
  have mono : StrictMono (corankSite n δ) := by
    intro i j hij; unfold corankSite
    exact div_lt_div_of_pos_right (add_lt_add_of_lt_of_le (by exact_mod_cast hij) le_rfl) (cellScale_pos hn)
  have mass : 0<(massFactor n δ:ℝ) := by exact_mod_cast massFactor_pos n δ
  apply sample_sign_criterion hlh _ _ mono (fun x => rankIntegral_derivative n δ 0 hs x)
    (fun x => rankIntegral_derivative n δ 1 hs x)
    (C:=π*cellScale (n+δ)/(2*(massFactor n δ:ℝ))) (by have := cellScale_pos hn; positivity) _ left middle right
  intro k hk
  have le : k≤D := hk.2.trans hhi
  have site : scaledSite n δ (D-k)=corankSite n δ k := by
    unfold scaledSite corankSite halfAreaSite
    rw [show n*(n+δ)-(D-k)=k by dsimp only [D] at *; omega]
    push_cast
    ring
  rw [rankIntegralOrder_zero,← site]
  exact rankIntegral_site hs hn (Nat.sub_le ..)

end CentralUnimodality.Witness
