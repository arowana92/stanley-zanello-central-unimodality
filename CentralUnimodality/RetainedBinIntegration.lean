module

public import CentralUnimodality.CorrectedTimeBins
public import CentralUnimodality.ModerateSpatialTransfer

/-! Exact lengths of the retained frequency cells. A pointwise amplitude
allowance on each closed cell bounds the two weighted integrals. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Set Real Witness ReturnSplit intervalIntegral

noncomputable def frequencyEdge (i : ℕ) := ((i:ℝ)/2)*sqrt ((i:ℝ)/2)

theorem frequency_edge_mono : Monotone frequencyEdge := by
  intro i j hij
  have le : (i:ℝ)/2≤(j:ℝ)/2 := div_le_div_of_nonneg_right (by exact_mod_cast hij) (by norm_num)
  exact mul_le_mul le (sqrt_le_sqrt le) (sqrt_nonneg _) (by positivity)

theorem frequency_cell_width (i : ℕ) :
    frequencyEdge (i+1)-frequencyEdge i≤(3/4)*sqrt (((i:ℝ)+1)/2) := by
  let x := (i:ℝ)/2
  let y := ((i:ℝ)+1)/2
  let a := sqrt x
  let b := sqrt y
  have x0 : 0≤x := by dsimp only [x]; positivity
  have y0 : 0≤y := by dsimp only [y]; positivity
  have a0 : 0≤a := sqrt_nonneg _
  have b0 : 0≤b := sqrt_nonneg _
  have ab : a≤b := sqrt_le_sqrt (by dsimp only [x,y]; linarith)
  have ax : a^2=x := sq_sqrt x0
  have by' : b^2=y := sq_sqrt y0
  have wid : y-x=1/2 := by dsimp only [x,y]; ring
  have eq : frequencyEdge (i+1)-frequencyEdge i=(b-a)*(b^2+b*a+a^2) := by
    unfold frequencyEdge; push_cast
    change y*b-x*a=_
    rw [← ax,← by']; ring
  have slope : b^2+b*a+a^2≤(b+a)*(3/2*b) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ab) (show 0≤b+2*a by linarith)]
  rw [eq]
  apply (mul_le_mul_of_nonneg_left slope (sub_nonneg.mpr ab)).trans_eq
  change _=(3/4)*b
  have gap : (b-a)*(b+a)=1/2 := by nlinarith only [ax,by',wid]
  rw [← mul_assoc,gap]; ring

theorem frequency_cell_time {i : ℕ} {ξ : ℝ} (h : ξ∈Icc (frequencyEdge i) (frequencyEdge (i+1))) :
    |ξ|^(2/3:ℝ)∈halfInterval i := by
  have epos (k : ℕ) : 0≤frequencyEdge k := by unfold frequencyEdge; positivity
  have square (k : ℕ) : (frequencyEdge k)^2=((k:ℝ)/2)^3 := by
    rw [frequencyEdge,mul_pow,sq_sqrt (by positivity)]; ring
  have ξ0 := (epos i).trans h.1
  have cube : (|ξ|^(2/3:ℝ))^3=ξ^2 := by
    rw [← rpow_natCast _ 3,← rpow_mul (abs_nonneg ξ)]; norm_num
  constructor
  · apply le_of_pow_le_pow_left₀ (n:=3) (by decide) (rpow_nonneg (abs_nonneg _) _)
    rw [cube,← square]
    exact pow_le_pow_left₀ (epos i) h.1 _
  · apply le_of_pow_le_pow_left₀ (n:=3) (by decide) (show 0≤((i+1:ℕ):ℝ)/2 by positivity)
    rw [cube,← square]
    exact pow_le_pow_left₀ ξ0 h.2 _

theorem retained_error_from_bins {n δ r : ℕ} (hs : δ≤1) (E : ℕ → ℝ) (nn : ∀ i<288, 0≤E i)
    (errors : ∀ i<288, ∀ ξ∈Icc (frequencyEdge i) (frequencyEdge (i+1)),
      |signedAmplitude n δ (ξ/cellScale (n+δ))-spectralTrial ξ|≤E i) :
    retainedError n δ r≤∑ i ∈ Finset.range 288,
      (3/4)*sqrt (((i:ℝ)+1)/2)*(frequencyEdge (i+1))^r*E i := by
  let f := fun ξ : ℝ => |signedAmplitude n δ (ξ/cellScale (n+δ))-spectralTrial ξ| *ξ^r
  have cf : Continuous f := ((amplitude_continuous _ _ hs).sub spectralTrial_continuous).abs.mul (continuous_id.pow r)
  have sum := sum_integral_adjacent_intervals (a:=frequencyEdge) (n:=288) (μ:=MeasureTheory.volume)
    (fun _ _ => cf.intervalIntegrable ..)
  change (∫ ξ in (0:ℝ)..1728, f ξ)≤_
  rw [show (0:ℝ)=frequencyEdge 0 by norm_num [frequencyEdge],show (1728:ℝ)=frequencyEdge 288 by norm_num [frequencyEdge,show sqrt (144:ℝ)=12 by rw [show (144:ℝ)=12^2 by norm_num,Real.sqrt_sq (by norm_num)]],← sum]
  apply Finset.sum_le_sum
  intro i hi
  have lt := Finset.mem_range.mp hi
  have w := frequency_cell_width i
  let U := E i*frequencyEdge (i+1)^r
  have up : 0≤U := mul_nonneg (nn i lt) (pow_nonneg (by unfold frequencyEdge; positivity) r)
  have le := frequency_edge_mono (Nat.le_succ i)
  have integral : (∫ ξ in frequencyEdge i..frequencyEdge (i+1), f ξ)≤∫ _ in frequencyEdge i..frequencyEdge (i+1), U := by
    apply integral_mono_on le (cf.intervalIntegrable ..) (continuous_const.intervalIntegrable ..)
    intro x hx
    have x0 : 0≤x := (show 0≤frequencyEdge i by unfold frequencyEdge; positivity).trans hx.1
    exact mul_le_mul (errors i lt x hx) (pow_le_pow_left₀ x0 hx.2 r) (pow_nonneg x0 _) (nn i lt)
  apply integral.trans
  rw [integral_const,smul_eq_mul]
  exact (mul_le_mul_of_nonneg_right w up).trans_eq (by dsimp only [U]; ring)

end CentralUnimodality.PolynomialTrial
