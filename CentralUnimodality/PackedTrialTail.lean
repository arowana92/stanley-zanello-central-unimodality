module

public import CentralUnimodality.TrialTailData
public import CentralUnimodality.LargePolynomialAmplitude

/-! Bound the trial on the high-frequency interval by the verified projective certificates. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 10000
set_option exponentiation.threshold 8192

private theorem tail_interval (l h : ℤ) (hl : 0≤l) (hlh : l<h) (hh : h≤256) (test : tailPair l h=true)
    {v : ℝ} (hv : v∈Set.Icc (l:ℝ) (h:ℝ)) : |value candidate v|≤1/10^14 := by
  unfold tailPair at test
  obtain ⟨p,n⟩ := Bool.and_eq_true_iff.mp test
  have size : l.natAbs+h.natAbs≤512 := by
    have L : (l.natAbs:ℤ)=l := by rw [Int.natCast_natAbs,abs_of_nonneg hl]
    have H : (h.natAbs:ℤ)=h := by rw [Int.natCast_natAbs,abs_of_nonneg (hl.trans hlh.le)]
    omega
  have side (m : ℤ) (hm : m.natAbs=10^14)
      (ok : packedDigitsTest 6144 422 m (-(2^120)) (homogeneousPack 6145 l h 256 trialPower)=true) :
      ((-(2^120):ℤ):ℝ)≤m*(realDense trialPower).eval (v/256) := by
    apply projective_bound l h 256 m (-(2^120)) trialPower hlh (by decide)
    · apply rowTest_of_packed (B:=512) size (by decide) tail_capacity.1 _ ok
      simpa only [hm,Int.natAbs_neg,Int.natAbs_pow,show (2:ℤ).natAbs=2 by rfl] using tail_capacity.2
    · exact ⟨div_le_div_of_nonneg_right hv.1 (by norm_num),div_le_div_of_nonneg_right hv.2 (by norm_num)⟩
  have low := side _ (show (10^14:ℤ).natAbs=10^14 by decide) p
  have high := side _ (show (-(10^14):ℤ).natAbs=10^14 by decide) n
  rw [candidate,normalized_input 1536 _ input_pack_bounds.2.2.1]
  change |(realDense trialPower).eval (v/256)/2^120|≤_
  norm_num at low high
  apply abs_le.mpr; constructor <;> linarith only [low,high]

theorem trial_tail {v : ℝ} (hv : v∈Set.Icc (64:ℝ) 256) : |value candidate v|≤1/10^14 := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8⟩ := tail_checks
  have lo := hv.1
  have hi := hv.2
  by_cases h0 : v≤88
  · apply tail_interval 64 88 (by decide) (by decide) (by decide) c0
    constructor <;> norm_num <;> linarith
  by_cases h1 : v≤112
  · apply tail_interval 88 112 (by decide) (by decide) (by decide) c1
    constructor <;> norm_num <;> linarith
  by_cases h2 : v≤160
  · apply tail_interval 112 160 (by decide) (by decide) (by decide) c2
    constructor <;> norm_num <;> linarith
  by_cases h3 : v≤184
  · apply tail_interval 160 184 (by decide) (by decide) (by decide) c3
    constructor <;> norm_num <;> linarith
  by_cases h4 : v≤208
  · apply tail_interval 184 208 (by decide) (by decide) (by decide) c4
    constructor <;> norm_num <;> linarith
  by_cases h5 : v≤232
  · apply tail_interval 208 232 (by decide) (by decide) (by decide) c5
    constructor <;> norm_num <;> linarith
  by_cases h6 : v≤244
  · apply tail_interval 232 244 (by decide) (by decide) (by decide) c6
    constructor <;> norm_num <;> linarith
  by_cases h7 : v≤250
  · apply tail_interval 244 250 (by decide) (by decide) (by decide) c7
    constructor <;> norm_num <;> linarith
  apply tail_interval 250 256 (by decide) (by decide) (by decide) c8
  constructor <;> norm_num <;> linarith

end CentralUnimodality.PolynomialTrial
