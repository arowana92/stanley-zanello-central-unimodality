module

public import CentralUnimodality.RationalRetainedCost
public import CentralUnimodality.CompactPhaseIntegral
public import CentralUnimodality.CellResidualEstimate
public import CentralUnimodality.CertifiedFirstCorrection

/-! Evaluate the conditional inverse with the cost from the bin of
each actual return time. The endpoint is assigned to the current bin,
including either choice of bin at a shared boundary. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit Real Set Witness

set_option maxRecDepth 12000

noncomputable def timeCosts (i N : ℕ) (u : ℝ) (j : ℕ) := (qCost (cappedBin i ((j:ℝ)*(u/N))):ℝ)

private theorem endpoint_bin {i : ℕ} {u : ℝ} (hu : u∈halfInterval i) : cappedBin i u=i := by
  unfold cappedBin
  have up : 0≤2*u := by have lo := hu.1; change (i:ℝ)/2≤u at lo; linarith only [lo,Nat.cast_nonneg (α:=ℝ) i]
  apply min_eq_left
  apply (Nat.le_floor_iff up).mpr
  have lo := hu.1; change (i:ℝ)/2≤u at lo; linarith

theorem cell_conditioned_cost {N i : ℕ} (hn : 300000≤N) {u : ℝ} (hu : u∈halfInterval i) :
    conditionedCost N (timeCosts i N u)≤2*sqrt N*((qCost i:ℝ)+(qEarly i:ℝ))+(qLate i:ℝ) := by
  have pos (k : ℕ) : 0≤(qCost k:ℝ) := by unfold qCost; push_cast; positivity
  have np : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have endpt : timeCosts i N u N=(qCost i:ℝ) := by
    rw [timeCosts,show (N:ℝ)*(u/N)=u by field_simp,endpoint_bin hu]
  have early (k : ℕ) (lo : 19*i/20≤k) (hi : k≤ i) : (qCost k:ℝ)≤(qEarly i:ℝ) :=
    (Rat.cast_le (K:=ℝ)).mpr (qCost_early lo hi)
  by_cases iz : i=0
  · subst i
    have cap (j : ℕ) (_ : j≤N) : timeCosts 0 N u j≤(qCost 0:ℝ) := by simp [timeCosts,cappedBin]
    have h := conditioned_zero_bin (by omega : 0<N) (timeCosts 0 N u) (by rw [endpt]; exact pos _) cap
    apply h.trans
    have e := mul_le_mul_of_nonneg_left (early 0 (by decide) le_rfl) (sqrt_nonneg (N:ℝ))
    have l : (qLate 0:ℝ)=0 := by simp [qLate]
    rw [l]; linarith only [e]
  · have ei := early i (by omega) le_rfl
    have h := conditioned_half_bin hn (Nat.pos_of_ne_zero iz) hu (timeCosts i N u) _ pos
      (by rw [endpt]; exact pos _) endpt.le (fun _ _ => le_rfl) ((pos i).trans ei) early
    exact h.trans (add_le_add (le_refl _) (late_price hn (Nat.pos_of_ne_zero iz)))

theorem cell_amplitude_cost {n δ i : ℕ} (hs : δ≤1) (hn : 300000≤n+δ) (hi : i<288)
    (tests : ∀ k<288, cellMaxTest k=true) {ξ : ℝ} (hξ : |ξ|≤1728)
    (hu : |ξ|^(2/3:ℝ)∈halfInterval i) :
    let N := n+δ
    let u := |ξ|^(2/3:ℝ)
    let τ := u/(N:ℝ)
    |signedAmplitude n δ (ξ/cellScale N)-spectralTrial ξ|≤
      (1+|ξ|/2)*(15/10^16)+(36/10^14)*u+4*sqrt N*τ*(3/10^12)+
      τ^2*conditionedCost N (timeCosts i N u)+τ*|correctedValue (1-δ) u| := by
  let N := n+δ
  let u := |ξ|^(2/3:ℝ)
  let τ := u/(N:ℝ)
  have sc := retained_scaling hn hξ
  have t0 : 0≤τ := sc.2.1
  have nr : (300000:ℝ)≤N := by exact_mod_cast hn
  have np : (N:ℝ)≠0 := by linarith
  have step : τ≤(maxStep:ℝ) := by
    unfold maxStep; push_cast; exact div_le_div₀ (by norm_num) sc.1.2 (by norm_num) nr
  apply corrected_amplitude_of_costs hs hn hξ (timeCosts i N u) (fun v hv => certified_first_correction (by omega) hv)
  intro j hj
  have jr : (j:ℝ)≤N := by exact_mod_cast hj
  have small : (j:ℝ)*τ≤u := by
    have top : (N:ℝ)*τ=u := by dsimp only [τ]; field_simp
    exact (mul_le_mul_of_nonneg_right jr t0).trans_eq top
  let k := cappedBin i ((j:ℝ)*τ)
  have ki : k≤ i := min_le_left ..
  have co : (j:ℝ)*τ∈halfInterval k := by
    apply mem_capped_bin (mul_nonneg (Nat.cast_nonneg _) t0)
    have top : u≤((i:ℝ)+1)/2 := by exact_mod_cast hu.2
    linarith only [small,top]
  have parity : 1-δ≤1 := Nat.sub_le ..
  have angle : |ξ/cellScale N/2| *(2*j+(1-δ:ℕ))≤9/8 := by
    apply le_trans _ sc.2.2.2
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have s : ((1-δ:ℕ):ℝ)≤1 := by exact_mod_cast parity
    linarith only [s,jr]
  have kl : k<288 := by omega
  have h := residual_of_cell_max parity kl (tests k kl) t0 step sc.2.2.1 angle rfl co
  simpa only [timeCosts,qCost,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using h

end CentralUnimodality.PolynomialTrial
