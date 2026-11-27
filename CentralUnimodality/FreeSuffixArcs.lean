module

public import CentralUnimodality.BernoulliArcs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! Fourier arc bounds for the actual unrestricted suffix on descending
rank labels. The variance is the variance of its integer word rank. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

noncomputable def labelVariance (c x : ℝ) := upChance (-(c*x))*upChance (c*x)

noncomputable def suffixVariance (c : ℝ) (m : ℕ) :=
  ∑ i ∈ Finset.range m, labelVariance c (i+1)*((i:ℝ)+1)^2

theorem suffixVariance_exact (c : ℝ) (m : ℕ) :
    suffixVariance c m = ∑ w ∈ words m, signMass c (c*m) w *
      (((wordParts w).sum:ℝ)-meanRank c m)^2 := by
  have h : suffixVariance c m = prefixVariance c (c*m) m m := by
    rw [suffixVariance,reverse_labels m (fun x => labelVariance c x*x^2),prefixVariance]
    apply Finset.sum_congr rfl
    intro i _
    rw [labelVariance,mul_sub]; ring
  rw [h,← prefixVariance_exact]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [centeredRank,mem_words.mp hw,prefixMean_full]
  rw [← mem_words.mp hw,prefixRank_full]

private theorem chance_bounds (u : ℝ) : 0 ≤ upChance (-u) ∧ upChance (-u) ≤ 1 := by
  have h (v : ℝ) : 0 ≤ upChance v := by unfold upChance; positivity
  exact ⟨h _,by linarith only [h u,up_total u]⟩

private theorem variance_site (u : ℝ) : upChance (-u)*(1-upChance (-u)) = upChance (-u)*upChance u := by
  rw [show 1-upChance (-u)=upChance u by linarith only [up_total u]]

private theorem product_envelope {m : ℕ} (c θ : ℝ) (f : ℕ → ℝ)
    (h : ∀ i ∈ Finset.range m, f i ≤ 2*labelVariance c (i+1)*sin (((i:ℝ)+1)*θ/2)^2) :
    ‖suffixTransform c θ m‖ ≤ exp (-(∑ i ∈ Finset.range m, f i)) := by
  rw [suffixTransform,norm_prod,← Finset.sum_neg_distrib,Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i hi => ?_)
  apply (bernoulli_modulus _ _).trans
  apply exp_le_exp.mpr
  have he := variance_site (c*(i+1))
  dsimp [labelVariance] at h
  nlinarith only [h i hi,congrArg (fun x => x*sin (((i:ℝ)+1)*θ/2)^2) he]

/-- The global error in the small arc on the x=σθ scale, before integration. -/
theorem suffix_small_error (c θ : ℝ) (m : ℕ) (D : ℝ)
    (hθ : m*|θ| ≤ 1) (hD : ∀ i ∈ Finset.range m, |1-2*upChance (-(c*(i+1)))| ≤ D) :
    let V := suffixVariance c m*θ^2
    ‖suffixTransform c θ m - (exp (-V/2):ℂ)‖ ≤
      exp (9/80-9/20*V)*V*(D*(m*|θ|)/6+(m*|θ|)^2/24) := by
  let p := fun i : ℕ => upChance (-(c*(i+1)))
  let t := fun i : ℕ => ((i:ℝ)+1)*θ
  let w := fun i => p i*(1-p i)
  let z := (m:ℝ)*|θ|
  have ht (i : ℕ) (hi : i ∈ Finset.range m) : |t i| ≤ z := by
    have hil : (i:ℝ)+1 ≤ m := by exact_mod_cast (Finset.mem_range.mp hi)
    dsimp [t,z]; rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ i+1)]
    exact mul_le_mul_of_nonneg_right hil (abs_nonneg _)
  have hv : (∑ i ∈ Finset.range m, w i*(t i)^2) = suffixVariance c m*θ^2 := by
    rw [suffixVariance,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [w,p,t,labelVariance,variance_site,mul_pow]; ring
  have H := product_gaussian_error (Finset.range m) p t (fun i _ => chance_bounds _) (fun i hi => (ht i hi).trans hθ)
  dsimp only at H ⊢
  rw [hv] at H
  apply H.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  rw [← hv,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have h₁ := ht i hi
  have h₂ := pow_le_pow_left₀ (abs_nonneg _) h₁ 2
  have h₃ := mul_le_mul (hD i hi) h₁ (abs_nonneg _) (le_trans (abs_nonneg _) (hD i hi))
  apply (show w i*(|1-2*p i| * |t i|^3/6+|t i|^4/24) =
      w i*(t i)^2*(|1-2*p i| * |t i|/6+|t i|^2/24) by
    have e := sq_abs (t i)
    linear_combination (w i*(|1-2*p i| * |t i|/6+|t i|^2/24))*e).trans_le
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (chance_bounds _).1
    (sub_nonneg.mpr (chance_bounds _).2)) (sq_nonneg _))
  dsimp only [p] at *
  linarith only [h₂,h₃]

private theorem sine_chord_one {x : ℝ} (hx : 0 ≤ x) (h₁ : x ≤ 1) : (161/192)*x ≤ sin x := by
  have hs : 23/48 ≤ sin (1/2) := by linarith only [sin_gt_sub_cube (by norm_num : (0:ℝ)<1/2)]
  have hc : 7/8 ≤ cos (1/2) := by linarith only [one_sub_sq_div_two_le_cos (x := 1/2)]
  have hsin : 161/192 ≤ sin 1 := by
    rw [show (1:ℝ)=2*(1/2) by norm_num,sin_two_mul]
    nlinarith only [mul_le_mul hs hc (by norm_num) (by linarith only [hs] : 0 ≤ sin (1/2))]
  have H := strictConcaveOn_sin_Icc.concaveOn.2 ⟨le_rfl,pi_pos.le⟩
    ⟨(by norm_num : (0:ℝ) ≤ 1),(by linarith only [pi_gt_d2] : (1:ℝ) ≤ π)⟩ (sub_nonneg.mpr h₁) hx
    (show 1-x+x=1 by ring)
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add,sin_zero] at H
  nlinarith only [H,mul_le_mul_of_nonneg_right hsin hx]

/-- For nonnegative frequency θ with mθ ≤ 2 the exponent .35 is valid. Up
to mθ ≤ π, Jordan's inequality gives exponent 2/π². -/
theorem suffix_middle_arcs (c : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (m : ℕ) :
    (m*θ ≤ 2 → ‖suffixTransform c θ m‖ ≤ exp (-(7/20*suffixVariance c m*θ^2))) ∧
    (m*θ ≤ π → ‖suffixTransform c θ m‖ ≤ exp (-(2/π^2*suffixVariance c m*θ^2))) := by
  have bound (a H : ℝ) (hle : m*θ ≤ H) (hb : ∀ x, 0 ≤ x → 2*x ≤ H → a*(2*x)^2 ≤ 2*sin x^2) :
      ‖suffixTransform c θ m‖ ≤ exp (-(a*suffixVariance c m*θ^2)) := by
    unfold suffixVariance
    rw [Finset.mul_sum,Finset.sum_mul]
    apply product_envelope
    intro i hi
    have hi' : (i:ℝ)+1 ≤ m := by exact_mod_cast Finset.mem_range.mp hi
    have h := hb (((i:ℝ)+1)*θ/2) (by positivity)
      (by linarith only [mul_le_mul_of_nonneg_right hi' hθ,hle])
    have hw : 0 ≤ labelVariance c (i+1) := by unfold labelVariance upChance; positivity
    nlinarith only [mul_le_mul_of_nonneg_left h hw]
  constructor
  · intro h
    apply bound _ 2 h
    intro x hx hx'
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (161/192:ℝ)*x) (sine_chord_one hx (by linarith only [hx'])) 2
    nlinarith only [hh,sq_nonneg x]
  · intro h
    apply bound _ π h
    intro x hx hx'
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (2/π)*x) (mul_le_sin hx (by linarith only [hx'])) 2
    calc
      _ = 2*((2/π)*x)^2 := by ring
      _ ≤ _ := by linarith only [hh]

private theorem sine_sum (θ : ℝ) (m : ℕ) :
    4*sin (θ/2)*(∑ i ∈ Finset.range m, sin (((i:ℝ)+1)*θ/2)^2) =
      (2*m+1)*sin (θ/2)-sin (((m:ℝ)+1/2)*θ) := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    let x := ((m:ℝ)+1)*θ
    have H := sin_sub_sin (x+θ/2) (x-θ/2)
    rw [show ((x+θ/2)-(x-θ/2))/2=θ/2 by ring,
      show ((x+θ/2)+(x-θ/2))/2=x by ring] at H
    have hc := cos_two_mul_eq_one_sub (x/2)
    rw [show 2*(x/2)=x by ring] at hc
    rw [hc] at H
    rw [Finset.sum_range_succ,mul_add,ih]
    change _+4*sin (θ/2)*sin (x/2)^2 = _
    rw [Nat.cast_succ,show (((m:ℝ)+1)+1/2)*θ=x+θ/2 by dsimp [x]; ring,
      show ((m:ℝ)+1/2)*θ=x-θ/2 by dsimp [x]; ring]
    linarith only [H]

/-- The outer arc estimates use a lower bound p on the single-label
variances. Both exponents are uniform up to the Nyquist frequency π. -/
theorem suffix_outer_arcs (c : ℝ) {θ p : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) (m : ℕ) (hp : 0 ≤ p)
    (hw : ∀ i ∈ Finset.range m, p ≤ labelVariance c (i+1)) :
    (π ≤ m*θ → ‖suffixTransform c θ m‖ ≤ exp (-(p*m/2))) ∧
    (8*π ≤ m*θ → ‖suffixTransform c θ m‖ ≤ exp (-(15*p*m/16))) := by
  let S := ∑ i ∈ Finset.range m, sin (((i:ℝ)+1)*θ/2)^2
  have ha : ‖suffixTransform c θ m‖ ≤ exp (-(2*p*S)) := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply product_envelope
    intro i hi
    exact mul_le_mul_of_nonneg_right (by linarith only [hw i hi]) (sq_nonneg _)
  have hJ := mul_le_sin (div_nonneg hθ (by norm_num)) (div_le_div_of_nonneg_right hπ (by norm_num))
  have hsin : θ/π ≤ sin (θ/2) := by convert hJ using 1; ring
  have qpos (h : π ≤ m*θ) : 0 < sin (θ/2) := by
    have hθ' : 0 < θ := by by_contra! hz; nlinarith only [h,pi_pos,mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α:=ℝ) m) hz]
    exact (div_pos hθ' pi_pos).trans_le hsin
  have H := sine_sum θ m
  change 4*sin (θ/2)*S = _ at H
  have hb : ∀ b : ℝ, b*π ≤ m*θ → b ≤ m*sin (θ/2) := by
    intro b h
    have ht := (le_div_iff₀ pi_pos).mpr h
    have hv := mul_le_mul_of_nonneg_left hsin (Nat.cast_nonneg (α:=ℝ) m)
    rw [mul_div_assoc] at ht
    exact ht.trans hv
  constructor
  · intro h
    have h₁ := hb 1 (by simpa using h)
    have h₂ : (m:ℝ)/4 ≤ S := by
      apply le_of_mul_le_mul_left _ (qpos h)
      nlinarith only [H,h₁,sin_le_one (((m:ℝ)+1/2)*θ),(qpos h).le]
    apply ha.trans (exp_le_exp.mpr _)
    nlinarith only [mul_le_mul_of_nonneg_left h₂ hp]
  · intro h
    have h₁ := hb 8 h
    have hpos := qpos (by linarith only [h,pi_pos])
    have h₂ : 15*(m:ℝ)/32 ≤ S := by
      apply le_of_mul_le_mul_left _ hpos
      nlinarith only [H,h₁,sin_le_one (((m:ℝ)+1/2)*θ),hpos.le]
    apply ha.trans (exp_le_exp.mpr _)
    nlinarith only [mul_le_mul_of_nonneg_left h₂ hp]

theorem suffix_norm_even (c θ : ℝ) (m : ℕ) : ‖suffixTransform c (-θ) m‖ = ‖suffixTransform c θ m‖ := by
  simp only [suffixTransform,norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [bernoulli_norm_sq,bernoulli_norm_sq,mul_neg,neg_div,sin_neg,neg_sq]

/-- The numerical single-label assumptions on every unrestricted suffix of
a saddle in the range of the right-flank theorem. -/
theorem suffix_saddle_parameters {m M : ℕ} (hm : 4096 ≤ m) (hM : M ≤ m) {c : ℝ} (hc : 0 ≤ c)
    (hs : 2*c*((m:ℝ)*√m) ≤ 25) :
    (∀ i ∈ Finset.range M, |1-2*upChance (-(c*(i+1)))| ≤ 25/128 ∧
      6/25 ≤ labelVariance c (i+1)) ∧
    (2/25:ℝ)*M^3 ≤ suffixVariance c M ∧ suffixVariance c M ≤ ((M:ℝ)+1)^3/12 := by
  have hm' : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hr : (64:ℝ) ≤ √m := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by linarith only [hm'])
  have ht : c*m ≤ 25/128 := by
    nlinarith only [hs,mul_le_mul_of_nonneg_left hr (mul_nonneg hc (Nat.cast_nonneg (α:=ℝ) m))]
  have per (i : ℕ) (hi : i ∈ Finset.range M) : |1-2*upChance (-(c*(i+1)))| ≤ 25/128 ∧
      6/25 ≤ labelVariance c (i+1) ∧ labelVariance c (i+1) ≤ 1/4 := by
    let x := c*((i:ℝ)+1)
    let d := tanh x
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hd : 0 ≤ d := by dsimp [d]; rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hx) (cosh_pos _).le
    have hil : (i:ℝ)+1 ≤ m := by exact_mod_cast (Finset.mem_range.mp hi).trans_le hM
    have hu : d ≤ 25/128 := (tanh_le_linear hx).trans ((mul_le_mul_of_nonneg_left hil hc).trans ht)
    have hd' : 1-2*upChance (-x)=d := by linarith only [up_total x,up_drift x]
    have hv : labelVariance c (i+1) = (1-d^2)/4 := by
      change upChance (-x)*upChance x = _
      rw [show upChance (-x)=(1-d)/2 by linarith only [hd'],
        show upChance x=(1+d)/2 by linarith only [up_total x,up_drift x]]
      ring
    change |1-2*upChance (-x)| ≤ _ ∧ _
    rw [hd',abs_of_nonneg hd,hv]
    refine ⟨hu,?_,?_⟩
    · nlinarith only [pow_le_pow_left₀ hd hu 2]
    · linarith only [sq_nonneg d]
  refine ⟨fun i hi => ⟨(per i hi).1,(per i hi).2.1⟩,?_⟩
  have hid : (∑ i ∈ Finset.range M, ((i:ℝ)+1)^2) = labelSquares M := by
    rw [reverse_labels M (fun x => x^2),sum_labelSquares]
  have hl := Finset.sum_le_sum (s := Finset.range M) fun i hi => mul_le_mul_of_nonneg_right (per i hi).2.1 (sq_nonneg ((i:ℝ)+1))
  have hh := Finset.sum_le_sum (s := Finset.range M) fun i hi => mul_le_mul_of_nonneg_right (per i hi).2.2 (sq_nonneg ((i:ℝ)+1))
  rw [← Finset.mul_sum,hid] at hl hh
  change _ ≤ suffixVariance c M at hl
  change suffixVariance c M ≤ _ at hh
  unfold labelSquares at hl hh
  constructor <;> nlinarith only [hl,hh,sq_nonneg (M:ℝ),Nat.cast_nonneg (α:=ℝ) M]

end CentralUnimodality.MarkedExcursion
