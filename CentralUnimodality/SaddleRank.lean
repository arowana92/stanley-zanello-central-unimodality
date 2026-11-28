module

public import CentralUnimodality.JointTilt
public import CentralUnimodality.EndpointTransforms

/-! Existence and range of the real label tilt that exactly centers a
prescribed staircase rank in the right-flank calculation. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Set

private theorem down_sign (u : ℝ) : exp (-u)/(2*cosh u) = (1-tanh u)/2 := by
  rw [tanh_eq_sinh_div_cosh,← cosh_sub_sinh]
  field_simp [(cosh_pos _).ne']

theorem meanRank_expectation (c : ℝ) (m : ℕ) :
    (∑ w ∈ words m, signMass c (c*m) w * (wordParts w).sum) = meanRank c m := by
  induction m with
  | zero => simp [words,wordParts,meanRank]
  | succ m ih =>
    rw [sum_cons_words,meanRank,Finset.sum_range_succ]
    let u := c*((m:ℝ)+1)
    have huv : u-c=c*m := by dsimp [u]; ring
    let p := exp (-u)/(2*cosh u)
    let q := exp u/(2*cosh u)
    have hpq : q+p = 1 := by dsimp [q,p]; rw [← add_div,cosh_eq]; field_simp
    have hpos (w : List Bool) : signMass c (c*(m+1:ℕ)) (false::w) = q*signMass c (c*m) w := by
      change _ = exp u/(2*cosh u)*_
      simp only [signMass,Nat.cast_succ,step,Int.cast_one,mul_one]
      rw [← show u=c*((m:ℝ)+1) from rfl,huv]
    have hneg (w : List Bool) : signMass c (c*(m+1:ℕ)) (true::w) = p*signMass c (c*m) w := by
      simp only [signMass,Nat.cast_succ,step,Int.cast_neg,Int.cast_one,mul_neg,mul_one]
      rw [← show u=c*((m:ℝ)+1) from rfl,huv]
    have ht (w) (hw : w ∈ words m) : (wordParts (true::w)).sum = (wordParts w).sum+(m+1) := by
      simp [wordParts,mem_words.mp hw]
    simp only [hpos,hneg,show ∀ w, wordParts (false::w) = wordParts w from fun _ => rfl]
    rw [Finset.sum_congr rfl (fun w hw => congrArg (fun i : ℕ => p*signMass c (c*m) w*(i:ℝ)) (ht w hw))]
    simp only [Nat.cast_add,Nat.cast_one,mul_add,mul_assoc,← Finset.mul_sum,Finset.sum_add_distrib,
      ← Finset.sum_mul,signMass_total,one_mul,ih]
    simp only [← mul_add c]
    change _ = meanRank c m+((m:ℝ)+1)*(1-tanh u)/2
    have hp : p = (1-tanh u)/2 := down_sign u
    linear_combination (meanRank c m)*hpq + ((m:ℝ)+1)*hp

theorem meanRank_continuous (m : ℕ) : Continuous (fun c => meanRank c m) := by
  unfold meanRank
  apply continuous_finsetSum
  intro i _
  have h : Continuous tanh := by
    simp only [funext tanh_eq_sinh_div_cosh]
    exact continuous_sinh.div continuous_cosh (fun x => (cosh_pos x).ne')
  fun_prop

theorem meanRank_zero (m : ℕ) : meanRank 0 m = (m:ℝ)*(m+1)/4 := by
  rw [meanRank,reverse_labels m (fun r => r*(1-tanh (0*r))/2)]
  simp only [zero_mul,tanh_zero,sub_zero,mul_one,div_eq_mul_inv,← Finset.sum_mul,sum_prefixLabels,prefixLabels]
  ring

theorem meanRank_displacement {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    c*(1-(c*m)^2/3)*labelSquares m/2 ≤ meanRank 0 m-meanRank c m ∧
    meanRank 0 m-meanRank c m ≤ c*labelSquares m/2 := by
  have series (v : ℝ) :
      meanRank v m = ∑ i ∈ Finset.range m, ((m:ℝ)-i)*(1-tanh (v*(m-i)))/2 :=
    reverse_labels m (fun r => r*(1-tanh (v*r))/2)
  have hterm {r : ℝ} (hr : 0 ≤ r) (hm : r ≤ m) :
      c*(1-(c*m)^2/3)*r^2/2 ≤ r*tanh (c*r)/2 ∧ r*tanh (c*r)/2 ≤ c*r^2/2 := by
    have hl := tanh_cubic_lower (mul_nonneg hc hr)
    have hs := pow_le_pow_left₀ (mul_nonneg hc hr) (mul_le_mul_of_nonneg_left hm hc) 2
    have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg hc hr)
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_left hl hr,mul_le_mul_of_nonneg_left hh hr]
    · nlinarith only [mul_le_mul_of_nonneg_left (tanh_le_linear (mul_nonneg hc hr)) hr]
  have hsum : meanRank 0 m-meanRank c m =
      ∑ i ∈ Finset.range m, ((m:ℝ)-i)*tanh (c*(m-i))/2 := by
    rw [series,series,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [zero_mul,tanh_zero]; ring
  have he (i : ℕ) (hi : i ∈ Finset.range m) := hterm (sub_nonneg.mpr
    (show (i:ℝ) ≤ m by exact_mod_cast (Finset.mem_range.mp hi).le)) (sub_le_self _ (Nat.cast_nonneg i))
  have hlo := Finset.sum_le_sum (fun i hi => (he i hi).1)
  have hhi := Finset.sum_le_sum (fun i hi => (he i hi).2)
  rw [hsum]
  simpa only [div_eq_mul_inv,← Finset.sum_mul,← Finset.mul_sum,sum_labelSquares] using And.intro hlo hhi

theorem degree_offset (m : ℕ) : 0 ≤ meanRank 0 m-staircaseDegree m ∧
    meanRank 0 m-staircaseDegree m ≤ ((m:ℝ)+1)/4 := by
  rw [meanRank_zero,staircaseDegree]
  let n := m/2
  rcases (show m = 2*n ∨ m = 2*n+1 by dsimp [n]; omega) with h|h
  · have h₁ : (m+1)/2 = n := by omega
    rw [h₁,← show n = m/2 from rfl]
    have he : (m:ℝ) = 2*n := by exact_mod_cast h
    push_cast
    constructor <;> rw [he] <;> nlinarith only [Nat.cast_nonneg (α := ℝ) n]
  · have h₁ : (m+1)/2 = n+1 := by omega
    rw [h₁,← show n = m/2 from rfl]
    have he : (m:ℝ) = 2*n+1 := by exact_mod_cast h
    push_cast
    constructor <;> rw [he] <;> nlinarith only [Nat.cast_nonneg (α := ℝ) n]

/-- In the right-flank window there exists an independent rank tilt with
mean exactly j. Its scaled parameter γ=2cs satisfies the numerical bounds
used by the first-hit and free-suffix estimates. -/
theorem saddle_rank {m j : ℕ} (hm : 4096 ≤ m) (hj : j ≤ staircaseDegree m)
    (hk : (staircaseDegree m:ℝ)-j ≤ 2*((m:ℝ)*√m)) :
    ∃ c : ℝ, 0 ≤ c ∧ meanRank c m = j ∧
      (1199/100)*((staircaseDegree m:ℝ)-j) ≤ (2*c*((m:ℝ)*√m))*((m:ℝ)*√m) ∧
      2*c*((m:ℝ)*√m) < 25 := by
  let s := (m:ℝ)*√m
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0:ℝ) < m := by linarith
  have hroot : (64:ℝ) ≤ √m := (Real.le_sqrt (by norm_num) hmp.le).mpr (by linarith)
  have hs : 0 < s := mul_pos hmp (Real.sqrt_pos.mpr hmp)
  have hss : s^2 = (m:ℝ)^3 := by dsimp [s]; rw [mul_pow,sq_sqrt hmp.le]; ring
  let c₀ := 25/(2*s)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have htop : c₀*s = 25/2 := by dsimp [c₀]; field_simp
  have hcm : (c₀*m)^2 ≤ (625:ℝ)/(4*4096) := by
    have h : (c₀*m)^2*(m:ℝ) = 625/4 := by
      have hs' : (c₀*s)^2 = (25/2:ℝ)^2 := congrArg (·^2) htop
      rw [mul_pow,hss] at hs'
      linarith only [hs']
    nlinarith only [h,mul_le_mul_of_nonneg_left hM (sq_nonneg (c₀*m))]
  have hs0 : (49/50:ℝ) ≤ 1-(c₀*m)^2/3 := by linarith only [hcm]
  have hQ : s^2/3 ≤ labelSquares m := by
    rw [hss,labelSquares]
    nlinarith only [hmp.le,sq_nonneg (m:ℝ)]
  have hD := degree_offset m
  have hsm : ((m:ℝ)+1)/4 ≤ s/128 := by
    dsimp [s]
    nlinarith only [mul_le_mul_of_nonneg_left hroot hmp.le,hM]
  have hbelow : meanRank c₀ m < j := by
    have h₁ := mul_le_mul_of_nonneg_left hs0 hc₀.le
    have h₂ := mul_le_mul h₁ hQ (by positivity : 0 ≤ s^2/3) (mul_nonneg hc₀.le (by linarith only [hs0]))
    have h₃ := (meanRank_displacement hc₀.le m).1
    change _ ≤ 2*s at hk
    have hs' := congrArg (·*s) htop
    linarith only [h₂,h₃,hD.2,hsm,hk,hs',hs]
  have hstart : (j:ℝ) ≤ meanRank 0 m := by
    have hj' : (j:ℝ) ≤ staircaseDegree m := by exact_mod_cast hj
    linarith only [hj',hD.1]
  obtain ⟨c,hc,he⟩ := intermediate_value_Icc' hc₀.le (meanRank_continuous m).continuousOn
    (show (j:ℝ) ∈ Icc (meanRank c₀ m) (meanRank 0 m) from ⟨hbelow.le,hstart⟩)
  change meanRank c m = j at he
  have hlt : c < c₀ := lt_of_le_of_ne hc.2 (by rintro rfl; linarith only [hbelow,he])
  have hcub : (1199/100:ℝ)*labelSquares m ≤ 4*s^2 := by
    have h₁ : (m:ℝ)+1 ≤ (4097/4096)*m := by linarith only [hM]
    have h₂ : 2*(m:ℝ)+1 ≤ (8193/4096)*m := by linarith only [hM]
    have h := mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ (by positivity) (by positivity)) hmp.le
    rw [hss,labelSquares]
    nlinarith only [h,mul_nonneg (sq_nonneg (m:ℝ)) hmp.le]
  have hleft := (meanRank_displacement hc.1 m).2
  rw [he] at hleft
  refine ⟨c,hc.1,he,?_,?_⟩
  · change _ ≤ 2*c*s*s
    nlinarith only [hleft,hD.1,mul_le_mul_of_nonneg_left hcub hc.1]
  · change 2*c*s < 25
    linarith only [mul_lt_mul_of_pos_right hlt hs,htop]

end CentralUnimodality.MarkedExcursion
