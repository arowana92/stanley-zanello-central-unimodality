module

public import CentralUnimodality.CellConditioning
public import CentralUnimodality.RetainedBinIntegration

/-! Remove the size variable from the retained amplitude and its
two weighted integrals. The worst-case square-root factors occur at
half-length 300,000 after multiplication by the appropriate mesh size. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit Real Set Witness

set_option maxRecDepth 12000

private theorem top_time (i : ℕ) : (topTime i:ℝ)=((i:ℝ)+1)/2 := by simp [topTime]

private theorem top_frequency (i : ℕ) : frequencyEdge (i+1)≤(topFrequency i:ℝ) := by
  have h := (root_brackets (x:=topTime i) (by unfold topTime; positivity)).2
  rw [topFrequency,Rat.cast_mul,top_time]
  unfold frequencyEdge; push_cast
  rw [top_time] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

private theorem retained_endpoint : frequencyEdge 288=1728 := by
  norm_num [frequencyEdge,show sqrt (144:ℝ)=12 by rw [show (144:ℝ)=12^2 by norm_num,Real.sqrt_sq (by norm_num)]]

theorem uniform_cell_amplitude {n δ i : ℕ} (hs : δ≤1) (hn : 300000≤n+δ) (hi : i<288)
    (tests : ∀ k<288, cellMaxTest k=true) {ξ : ℝ} (cell : ξ∈Icc (frequencyEdge i) (frequencyEdge (i+1))) :
    |signedAmplitude n δ (ξ/cellScale (n+δ))-spectralTrial ξ|≤(frequencyAllowance i:ℝ) := by
  let N := n+δ
  let u := |ξ|^(2/3:ℝ)
  let τ := u/(N:ℝ)
  let H : ℝ := (topTime i:ℝ)
  let t := H/300000
  let s : ℝ := (rootHigh 300000:ℝ)
  let C : ℝ := (qCost i:ℝ)
  let E : ℝ := (qEarly i:ℝ)
  let L : ℝ := (qLate i:ℝ)
  have nn : 0≤ξ := (show 0≤frequencyEdge i by unfold frequencyEdge; positivity).trans cell.1
  have band : |ξ|≤1728 := by
    rw [abs_of_nonneg nn,← retained_endpoint]
    exact cell.2.trans (frequency_edge_mono (by omega))
  have hu : u∈halfInterval i := frequency_cell_time cell
  have u0 : 0≤u := rpow_nonneg (abs_nonneg _) _
  have uh : u≤H := by dsimp only [H]; rw [top_time]; exact_mod_cast hu.2
  have xh : |ξ|≤(topFrequency i:ℝ) := by rw [abs_of_nonneg nn]; exact cell.2.trans (top_frequency i)
  have h := cell_amplitude_cost hs hn hi tests band hu
  have inv := cell_conditioned_cost hn hu
  have ⟨step,first,second⟩ := scaled_steps hn u0 uh
  have t0 : 0≤τ := div_nonneg u0 (Nat.cast_nonneg _)
  have ce : 0≤2*(C+E) := by dsimp [C,E,qCost,qEarly]; push_cast; positivity
  have l0 : 0≤L := by dsimp only [L]; exact_mod_cast qLate_nonneg i
  have ecost : τ^2*conditionedCost N (timeCosts i N u)≤t^2*(2*s*(C+E)+L) := by
    calc
      _≤τ^2*(2*sqrt N*(C+E)+L) := mul_le_mul_of_nonneg_left inv (sq_nonneg _)
      _=2*(C+E)*(sqrt N*τ^2)+L*τ^2 := by ring
      _≤2*(C+E)*(s*t^2)+L*t^2 := add_le_add (mul_le_mul_of_nonneg_left second ce)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ t0 step 2) l0)
      _=_ := by ring
  let g : ℝ := (correctionJetNum i 0:ℝ)/(4*10^30)
  have g0 : 0≤g := by dsimp [g]; positivity
  have gj : |correctedValue (1-δ) u|≤g := by
    simpa only [iteratedDeriv_zero] using (certified_correction_jet (by omega : 1-δ≤1) hi (by decide : 0<3) hu)
  have product := mul_le_mul step gj (abs_nonneg _) (u0.trans uh |> fun y => div_nonneg y (by norm_num : (0:ℝ)≤300000))
  apply h.trans
  have price : (frequencyAllowance i:ℝ)=
      (1+(topFrequency i:ℝ)/2)*(15/10^16)+(36/10^14)*H+4*s*t*(3/10^12)+t^2*(2*s*(C+E)+L)+t*g := by
    simp only [frequencyAllowance,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast]
    dsimp only [H,t,s,C,E,L,g]; ring
  rw [price]
  change (1+|ξ|/2)*(15/10^16)+(36/10^14)*u+4*sqrt N*τ*(3/10^12)+τ^2*conditionedCost N (timeCosts i N u)+
    τ*|correctedValue (1-δ) u|≤_
  change sqrt N*τ≤s*t at first
  change τ*|correctedValue (1-δ) u|≤t*g at product
  linarith only [xh,uh,first,ecost,product]

theorem retained_charge_bound {n δ : ℕ} (hs : δ≤1) (hn : 300000≤n+δ) (tests : ∀ k<288, cellMaxTest k=true)
    (r : ℕ) : retainedError n δ r≤((∑ i ∈ Finset.range 288, frequencyCharge i r:ℚ):ℝ) := by
  apply (retained_error_from_bins hs (fun i => (frequencyAllowance i:ℝ)) (fun i _ => by exact_mod_cast frequencyAllowance_nonneg i)
    (fun _ hi _ hx => uniform_cell_amplitude hs hn hi tests hx)).trans
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  have time := (root_brackets (x:=topTime i) (by unfold topTime; positivity)).2
  rw [top_time] at time
  have freq := top_frequency i
  have f0 : 0≤frequencyEdge (i+1) := by unfold frequencyEdge; positivity
  have a0 : 0≤(frequencyAllowance i:ℝ) := by exact_mod_cast frequencyAllowance_nonneg i
  have p := pow_le_pow_left₀ f0 freq r
  have round := (Rat.cast_le (K:=ℝ)).mpr (round_upper (3/4*rootHigh (topTime i)*(topFrequency i)^r*frequencyAllowance i))
  unfold frequencyCharge; apply le_trans _ round
  push_cast
  have rt := (sqrt_nonneg _).trans time
  gcongr

end CentralUnimodality.PolynomialTrial
