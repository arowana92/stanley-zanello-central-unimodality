module

public import CentralUnimodality.PairedFourier
public import CentralUnimodality.DyadicRotation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! A paired prefix that ends at the first quadrant already makes every
later free and bridge Fourier input small. -/
@[expose] public section

namespace CentralUnimodality

private theorem cos_gaussian_quarter {y : ℝ} (hy : 0 ≤ y) (hπ : y ≤ Real.pi/4) :
    Real.cos y ≤ Real.exp (-(y^2/2)) := by
  let g (x : ℝ) := Real.log (Real.cos x)+x^2/2
  have deriv (x : ℝ) (hx : x ∈ Set.Icc 0 (Real.pi/4)) :
      HasDerivAt g (x-Real.tan x) x := by
    have hpos := Real.cos_pos_of_mem_Ioo (x := x) ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,Real.pi_pos]⟩
    have h := ((Real.hasDerivAt_cos x).log hpos.ne').add ((hasDerivAt_pow 2 x).div_const 2)
    convert h using 1
    simp [Real.tan_eq_sin_div_cos]
    ring
  have hm : AntitoneOn g (Set.Icc 0 (Real.pi/4)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ..)
      (fun x hx => (deriv x hx).continuousAt.continuousWithinAt)
      (fun x hx => (deriv x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    have hp := (interior_subset hx : x ∈ Set.Icc 0 (Real.pi/4))
    rw [(deriv x hp).deriv]
    exact sub_nonpos.mpr (Real.le_tan hp.1 (by linarith [hp.2,Real.pi_pos]))
  have hh := hm (by exact ⟨le_rfl,by linarith [Real.pi_pos]⟩ : (0:ℝ) ∈ Set.Icc 0 (Real.pi/4)) ⟨hy,hπ⟩ hy
  simp [g] at hh
  have hpos := Real.cos_pos_of_mem_Ioo (x := y) ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr (by linarith)

private theorem pair_gaussian {x : ℝ} (hx : 0 ≤ x) (hπ : x ≤ Real.pi/2) :
    (1+|Real.cos x|)/2 ≤ Real.exp (-(x^2/4)) := by
  rw [abs_of_nonneg (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hπ)]
  have hh := cos_gaussian_quarter (y := x/2) (by linarith) (by linarith)
  have hc : 0 ≤ Real.cos (x/2) := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  calc (1+Real.cos x)/2 = Real.cos (x/2)^2 := by
         have h := Real.cos_two_mul (x/2)
         rw [show 2*(x/2)=x by ring] at h
         linarith
       _ ≤ Real.exp (-((x/2)^2/2))^2 := pow_le_pow_left₀ hc hh 2
       _ = _ := by rw [sq,← Real.exp_add]; congr 1; ring

theorem pair_prefix_gaussian {ω : ℝ} (hω : 0 ≤ ω) (l : ℕ)
    (hπ : ω*(2*l+1) ≤ Real.pi/2) :
    pairFactor ω l ≤ Real.exp (-(ω^2*(4*(l:ℝ)^3-l)/12)) := by
  induction l with
  | zero => simp [pairFactor]
  | succ l ih =>
    have hm := mul_le_mul_of_nonneg_left (show 2*(l:ℝ)+1 ≤ 2*(l+1)+1 by linarith) hω
    push_cast at hπ
    have h₁ := ih (hm.trans hπ)
    have h₂ := pair_gaussian (show 0 ≤ ω*(2*l+1) by positivity) (hm.trans hπ)
    rw [pairFactor,Finset.prod_range_succ]
    apply (mul_le_mul h₁ h₂ (by positivity) (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring

theorem quadrant_input_tail {ω : ℝ} (hω : 0 ≤ ω) {l n : ℕ} (hl : 200 ≤ l)
    (hlo : ω*(2*l+1) ≤ Real.pi/2) (hhi : Real.pi/2 ≤ ω*(2*l+3)) (hn : 2*l ≤ n) :
    ‖PowerSeries.coeff n (fairSeries (areaCharacter ω) words)‖ ≤ 1/(2:ℝ)^57 ∧
    ‖PowerSeries.coeff n (fairSeries (areaCharacter ω) bridges)‖ ≤ 1/(2:ℝ)^57 := by
  have hL : (200:ℝ) ≤ l := by exact_mod_cast hl
  have hx : (1.57:ℝ) ≤ ω*(2*l+3) := by linarith [Real.pi_gt_d2]
  have hs := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 1.57) (by positivity)).mpr hx
  have hp : (49/50:ℝ)*(2*l+3)^2 ≤ 4*(l:ℝ)^2-1 := by
    nlinarith only [hL,mul_nonneg (sub_nonneg.mpr hL) (Nat.cast_nonneg (α := ℝ) l)]
  have h₁ := mul_le_mul_of_nonneg_right hs (show 0 ≤ (49/50:ℝ)*l by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hp (show 0 ≤ ω^2*l by positivity)
  have he : 40 ≤ ω^2*(4*(l:ℝ)^3-l)/12 := by nlinarith only [h₁,h₂,hL]
  have hpow : (2:ℝ)^57 ≤ Real.exp 40 := by
    have h0 : (2.7:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) h0 40
    rw [← Real.exp_nat_mul] at hh
    exact (by norm_num : (2:ℝ)^57 ≤ 2.7^40).trans (by simpa only [Nat.cast_ofNat,mul_one] using hh)
  have hb : pairFactor ω l ≤ 1/(2:ℝ)^57 := calc
    _ ≤ _ := pair_prefix_gaussian hω l hlo
    _ ≤ Real.exp (-40) := Real.exp_le_exp.mpr (neg_le_neg he)
    _ ≤ _ := by rw [Real.exp_neg,one_div]; exact inv_anti₀ (by positivity) hpow
  have h := fair_inputs_after_pairs ω hn
  exact ⟨h.1.trans hb,h.2.trans hb⟩

namespace SmallGrid

/-- The actual integer cutoff for a positive retained mode. -/
def quadrantCut (k f : ℕ) := (2^k/f-1)/2

theorem retained_quadrant_cut {k f A : ℕ} (hA : 2049 ≤ A) (hf : 0 < f)
    (hperiod : 5*(Nat.sqrt ((2*A)^3)+1) ≤ 2^(k+1))
    (hstop : f ≤ (204800*2^(k+1)+628*Nat.sqrt ((2*A)^3)-1)/(628*Nat.sqrt ((2*A)^3))) :
    200 ≤ quadrantCut k f ∧ (2*quadrantCut k f+1)*f ≤ 2^k ∧ 2^k ≤ (2*quadrantCut k f+3)*f := by
  let S := Nat.sqrt ((2*A)^3)
  let Q := 2^(k+1)
  have hscale : 262144 ≤ S := by
    apply Nat.le_sqrt'.mpr
    exact (by decide : 262144^2 ≤ (2*2049)^3).trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hA) 3)
  change 5*(S+1) ≤ Q at hperiod
  change f ≤ (204800*Q+628*S-1)/(628*S) at hstop
  have hnum := (Nat.mul_le_mul_right (628*S) hstop).trans (Nat.div_mul_le_self _ _)
  have hn : f*(628*S) ≤ 204800*Q+628*S := hnum.trans (Nat.sub_le ..)
  have hSQ : 262144*Q ≤ S*Q := Nat.mul_le_mul_right Q hscale
  have hprod : (802*f)*(628*S) ≤ Q*(628*S) := by nlinarith only [hn,hSQ,hperiod]
  have hmax : 802*f ≤ Q := Nat.le_of_mul_le_mul_right hprod (by omega)
  have h401 : 401*f ≤ 2^k := by dsimp [Q] at hmax; rw [pow_succ] at hmax; omega
  let r := 2^k/f
  have hr : 401 ≤ r := (Nat.le_div_iff_mul_le hf).mpr h401
  have h₁ : 2*quadrantCut k f+1 ≤ r := by change 2*((r-1)/2)+1 ≤ r; omega
  have h₂ : r+1 ≤ 2*quadrantCut k f+3 := by change r+1 ≤ 2*((r-1)/2)+3; omega
  refine ⟨by change 200 ≤ (r-1)/2; omega,(Nat.mul_le_mul_right f h₁).trans (Nat.div_mul_le_self ..),?_⟩
  exact (by simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ (2^k) hf).le : 2^k ≤ (r+1)*f).trans
    (Nat.mul_le_mul_right f h₂)

theorem grid_quadrant_tail {k f l n : ℕ} (hl : 200 ≤ l) (hlo : (2*l+1)*f ≤ 2^k)
    (hhi : 2^k ≤ (2*l+3)*f) (hn : 2*l ≤ n) :
    ‖PowerSeries.coeff n (fairSeries (areaCharacter (frequency k f)) words)‖ ≤ 1/(2:ℝ)^57 ∧
    ‖PowerSeries.coeff n (fairSeries (areaCharacter (frequency k f)) bridges)‖ ≤ 1/(2:ℝ)^57 := by
  apply quadrant_input_tail (by unfold frequency; positivity) hl _ _ hn
  · unfold frequency
    rw [div_mul_eq_mul_div,pow_succ]
    apply (div_le_iff₀ (by positivity)).mpr
    have h : (2*(l:ℝ)+1)*f ≤ (2:ℝ)^k := by exact_mod_cast hlo
    calc (f:ℝ)*Real.pi*(2*l+1) = ((2*l+1)*f)*Real.pi := by ring
         _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right h Real.pi_pos.le]
  · unfold frequency
    rw [div_mul_eq_mul_div,pow_succ]
    apply (le_div_iff₀ (by positivity)).mpr
    have h : (2:ℝ)^k ≤ (2*(l:ℝ)+3)*f := by exact_mod_cast hhi
    calc _ = (2:ℝ)^k*Real.pi := by ring
         _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right h Real.pi_pos.le]

end SmallGrid

end CentralUnimodality
