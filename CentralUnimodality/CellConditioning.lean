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

noncomputable def timeDiscount (i N : ℕ) (u : ℝ) (v : ℕ) : ℝ :=
  (returnDiscount i (cappedBin i ((v:ℝ)*(u/N))):ℝ)

noncomputable def pricedTimeCost (i N : ℕ) (u : ℝ) (v : ℕ) :=
  timeDiscount i N u v*timeCosts i N u v

theorem cell_conditioned_cost {N i : ℕ} (hn : 150000≤N) {u : ℝ} (hu : u∈halfInterval i) :
    conditionedCost N (pricedTimeCost i N u)≤2*sqrt N*((qCost i:ℝ)+(qEarly i:ℝ))+(qLate i:ℝ) := by
  have pos (k : ℕ) : 0≤(qCost k:ℝ) := by unfold qCost; push_cast; positivity
  have dpos (k : ℕ) : 0≤(discountedCost i k:ℝ) := by exact_mod_cast discountedCost_nonneg i k
  have np : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have endpt : pricedTimeCost i N u N=(qCost i:ℝ) := by
    simp [pricedTimeCost,timeCosts,timeDiscount,show (N:ℝ)*(u/N)=u by field_simp,endpoint_bin hu]
  have early (k : ℕ) (lo : 19*i/20≤k) (hi : k≤ i) : (discountedCost i k:ℝ)≤(qEarly i:ℝ) := by
    exact_mod_cast (discountedCost_le i k).trans (qCost_early lo hi)
  have equal (j : ℕ) : pricedTimeCost i N u j=(discountedCost i (cappedBin i ((j:ℝ)*(u/N))):ℝ) := by
    simp only [pricedTimeCost,timeCosts,timeDiscount,discountedCost,Rat.cast_mul]
  have self : discountedCost i i=qCost i := by simp [discountedCost]
  by_cases iz : i=0
  · subst i
    have cap (j : ℕ) (_ : j≤N) : pricedTimeCost 0 N u j≤(qCost 0:ℝ) := by
      simp [equal,cappedBin,discountedCost]
    have h := conditioned_zero_bin (by omega : 0<N) (pricedTimeCost 0 N u) (by rw [endpt]; exact pos _) cap
    apply h.trans
    have e := mul_le_mul_of_nonneg_left (early 0 (by decide) le_rfl) (sqrt_nonneg (N:ℝ))
    rw [self] at e
    have l : (qLate 0:ℝ)=0 := by simp [qLate]
    rw [l]; linarith only [e]
  · have ei := early i (by omega) le_rfl
    have h := conditioned_half_bin (N:=N) (by omega) (Nat.pos_of_ne_zero iz) hu (pricedTimeCost i N u) _ dpos
      (by rw [endpt]; exact pos _) (by rw [endpt,self]) (fun _ _ => (equal _).le) ((dpos i).trans ei) early
    rw [self] at h
    exact h.trans (add_le_add (le_refl _) (late_price hn (Nat.pos_of_ne_zero iz)))

theorem cell_amplitude_cost {n δ i : ℕ} (hs : δ≤1) (hn : 150000≤n+δ) (hi : i<228)
    (tests : ∀ k<288, cellMaxTest k=true) {ξ : ℝ} (hξ : |ξ|≤1728)
    (hu : |ξ|^(2/3:ℝ)∈halfInterval i) :
    let N := n+δ
    let u := |ξ|^(2/3:ℝ)
    let τ := u/(N:ℝ)
    |signedAmplitude n δ (ξ/cellScale N)-spectralTrial ξ|≤
      (1+|ξ|/2)*(15/10^16)+(36/10^14)*u+4*sqrt N*τ*(3/10^12)+
      τ^2*conditionedCost N (pricedTimeCost i N u)+τ*|correctedValue (1-δ) u| := by
  let N := n+δ
  let u := |ξ|^(2/3:ℝ)
  let τ := u/(N:ℝ)
  have n0 : 0<N := by dsimp only [N]; omega
  have sc := peak_frequency_scale n0 hξ
  have t0 : 0≤τ := div_nonneg sc.1.1 (Nat.cast_nonneg _)
  have localTime : u≤114 := by
    have top : u≤((i:ℝ)+1)/2 := by exact_mod_cast hu.2
    have small : (i:ℝ)≤227 := by exact_mod_cast (by omega : i≤227)
    linarith only [top,small]
  have nr : (150000:ℝ)≤N := by exact_mod_cast hn
  have np : (N:ℝ)≠0 := by linarith
  have step : τ≤(maxStep:ℝ) := by
    exact (div_le_div₀ (by norm_num : (0:ℝ)≤114) localTime (by norm_num : (0:ℝ)<150000) nr).trans (by norm_num [maxStep])
  have endpt : timeDiscount i N u N=1 := by
    have bin : cappedBin i u=i := endpoint_bin hu
    simp [timeDiscount,show (N:ℝ)*(u/N)=u by field_simp,bin]
  have unit (v : ℕ) (_ : v≤N) : timeDiscount i N u v≤1 := by
    unfold timeDiscount
    exact_mod_cast (discount_bounds i _).2
  have symbol (j : ℕ) (hj : j≤N) : ‖returnSymbol (ξ/cellScale N/2) j‖≤returnMass j*timeDiscount i N u (N-j) := by
    apply return_symbol_discount n0 hj hu _ sc.2
    exact step.trans (by norm_num [maxStep])
  apply corrected_amplitude_of_weighted_costs hs n0 hξ (timeCosts i N u) (timeDiscount i N u) endpt unit symbol
    (fun v hv => certified_first_correction (by omega) hv)
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
    apply le_trans _ (peak_local_angle hn localTime)
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have s : ((1-δ:ℕ):ℝ)≤1 := by exact_mod_cast parity
    linarith only [s,jr]
  have kl : k<288 := by omega
  have h := residual_of_cell_max parity kl (tests k kl) t0 step sc.2 angle rfl co
  simpa only [timeCosts,qCost,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using h

end CentralUnimodality.PolynomialTrial
