module

public import CentralUnimodality.PinnedPrefixSplit
public import CentralUnimodality.ShortSuffixRanks
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Explicit three-block estimate for the recentered first-hit probability
in each time bin. Its product with the rank-resolved suffix bounds applies
to all three difference orders. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

private theorem middle_variance {x : ℝ} (hx : |x| ≤ 21/100) : 119/500 ≤ upChance (-x)*upChance x := by
  have h : |tanh x| ≤ |x| := by
    rcases le_total 0 x with h|h
    · have hd : 0 ≤ tanh x := by rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr h) (cosh_pos _).le
      rw [abs_of_nonneg h,abs_of_nonneg hd]; exact tanh_le_linear h
    · have h' := tanh_le_linear (neg_nonneg.mpr h)
      rw [tanh_neg] at h'
      have hd : tanh x ≤ 0 := by rw [tanh_eq_sinh_div_cosh]; exact div_nonpos_of_nonpos_of_nonneg (sinh_nonpos_iff.mpr h) (cosh_pos _).le
      rwa [abs_of_nonpos h,abs_of_nonpos hd]
  have hh := pow_le_pow_left₀ (abs_nonneg _) (h.trans hx) 2
  rw [sq_abs] at hh
  rw [show upChance (-x)=(1-tanh x)/2 by linarith only [up_drift x,up_total x],
    show upChance x=(1+tanh x)/2 by linarith only [up_drift x,up_total x]]
  nlinarith only [hh]

/-- The middle endpoint has the required site variances anywhere in the
centered prefix with cd≤.21, including the negative-parameter half. -/
theorem centered_three_blocks {c : ℝ} (hc : 0 ≤ c) (d a q b : ℕ) (hlen : a+q+b+1=2*d+1)
    (hq : 80 ≤ q) (hcap : c*d ≤ 21/100) :
    (∑ w ∈ hitWords 1 (2*d+1), signMass c (c*d) w) ≤
      live c (c*d) a 1*upChance (c*d)*live c (c*d-c) b 1 / √q := by
  have hl : (a+q+b:ℕ)=2*d := by omega
  have H := first_hit_three_blocks c (c*d) a q b (K := 1/√q) (fun z =>
    middle_displacement_bound c (c*d-c*a) hq z (by
      intro i hi
      have hil : (a:ℝ)+i ≤ 2*d := by exact_mod_cast (by omega : a+i ≤ 2*d)
      apply middle_variance (abs_le.mpr ⟨?_,?_⟩)
      · nlinarith only [mul_le_mul_of_nonneg_left hil hc,hcap]
      · nlinarith only [hcap,mul_nonneg hc (Nat.cast_nonneg (α:=ℝ) i),mul_nonneg hc (Nat.cast_nonneg (α:=ℝ) a)]))
  dsimp only at H
  rw [hlen,hl,Nat.cast_mul,Nat.cast_ofNat,show c*(2*(d:ℝ))-c*d=c*d by ring] at H
  simpa only [mul_one_div] using H

/-- Dimensionless first-hit bin factor. The parameter β bounds the maximum
prefix natural parameter times √m. The proof chooses a=floor(t/3) and
retains the compulsory first upward step of the reversed last piece. -/
theorem pinned_hit_bin {m d : ℕ} (hm : 4096 ≤ m) {c v e lam : ℝ} (hc : 0 ≤ c)
    (hlam : lam=2*c*((m:ℝ)*√m)) (hmax : lam ≤ 57) (he : e ≤ 15/16+1/4096)
    (hlo : v*m ≤ 2*(d:ℝ)+1) (hhi : 2*(d:ℝ)+1 ≤ e*m)
    (hcore : 80 ≤ (v/3-2/4096)*m) :
    let β := lam*e/4
    let z := v/3-2/4096
    let F := 2*β+(4/5)/√z
    (∑ w ∈ hitWords 1 (2*d+1), signMass c (c*d) w) ≤
      (1/2+β/128)*F^2/(√z*((m:ℝ)*√m)) := by
  let t := 2*d+1
  let a := t/3
  let b := a-1
  let q := t-2*a
  let z := v/3-2/4096
  let β := lam*e/4
  have hm' : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hr : (64:ℝ) ≤ √m := (Real.le_sqrt (by norm_num) hm0.le).mpr (by linarith only [hm'])
  have hr0 : 0 < √(m:ℝ) := by positivity
  have hlam' : 0 ≤ lam := by rw [hlam]; positivity
  have he' : 0 ≤ e := by by_contra! H; nlinarith only [mul_nonpos_of_nonpos_of_nonneg H.le hm0.le,hhi,Nat.cast_nonneg (α:=ℝ) d]
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hcd : 0 ≤ c*d := by positivity
  have hscaled : c*d*√m ≤ β := by
    have hd : 2*(d:ℝ) ≤ e*m := by linarith only [hhi]
    dsimp [β]; rw [hlam]
    nlinarith only [mul_le_mul_of_nonneg_right hd (mul_nonneg hc hr0.le)]
  have hcap : c*d ≤ 21/100 := by
    have hβ' := mul_le_mul hmax he he' (by norm_num : (0:ℝ) ≤ 57)
    dsimp only [β] at hscaled
    nlinarith only [hscaled,hβ',mul_le_mul_of_nonneg_left hr hcd]
  have ht : (t:ℝ)=2*d+1 := by dsimp [t]; push_cast; rfl
  have ha : (t:ℝ) ≤ 3*a+2 := by exact_mod_cast (by dsimp [a]; omega : t ≤ 3*a+2)
  have hz : 0 < z := by
    by_contra! H
    change 80 ≤ z*m at hcore
    linarith only [hcore,mul_nonpos_of_nonpos_of_nonneg H hm0.le]
  have hza : z*m+1 ≤ a := by dsimp only [z]; linarith only [ht,hlo,ha,hm']
  have ha' : 0 < a := by
    have h : (0:ℝ) < a := by linarith only [hza,mul_pos hz hm0]
    exact_mod_cast h
  have hb : (b:ℝ)=(a:ℝ)-1 := by dsimp [b]; rw [Nat.cast_sub (by omega)]; norm_num
  have hzb : z*m ≤ b := by linarith only [hza,hb]
  have hqa : a ≤ q := by dsimp [q,a]; omega
  have hzq : z*m ≤ q := by
    have h : (a:ℝ) ≤ q := by exact_mod_cast hqa
    linarith only [h,hza]
  have hb' : 0 < b := by have H := (mul_pos hz hm0).trans_le hzb; exact_mod_cast H
  have hq : 80 ≤ q := by exact_mod_cast (hcore.trans hzq)
  have hlen : a+q+b+1=2*d+1 := by dsimp [a,q,b,t] at *; omega
  have hroot (k : ℕ) (hk : z*m ≤ k) : √z*√m ≤ √(k:ℝ) := by
    rw [← Real.sqrt_mul hz.le]; exact Real.sqrt_le_sqrt hk
  let F := 2*β+(4/5)/√z
  have HF : 0 ≤ F := by dsimp [F]; positivity
  have hlive (k : ℕ) (hk : 0 < k) (hk' : z*m ≤ k) (u : ℝ) (hu : u ≤ c*d) :
      live c u k 1 ≤ F/√m := by
    apply (live_upper_of_cap hcd hk (fun i _ => by linarith only [hu,mul_nonneg hc (Nat.cast_nonneg (α:=ℝ) i)])).trans
    have hfrac := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4/5) (mul_pos (sqrt_pos.mpr hz) hr0) (hroot k hk')
    have hs := (le_div_iff₀ hr0).mpr hscaled
    apply (add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2)) hfrac).trans_eq
    dsimp [F]; ring
  have hprob : upChance (c*d) ≤ 1/2+β/128 := by
    have h₁ := up_drift (c*d)
    have h₂ := up_total (c*d)
    have h₃ := tanh_le_linear hcd
    nlinarith only [h₁,h₂,h₃,hscaled,mul_le_mul_of_nonneg_left hr hcd]
  have top := centered_three_blocks hc d a q b hlen hq hcap
  have hA := hlive a ha' (by linarith only [hza]) (c*d) le_rfl
  have hB := hlive b hb' hzb (c*d-c) (by linarith)
  have hQ := hroot q hzq
  apply top.trans
  apply le_trans (div_le_div_of_nonneg_right (mul_le_mul (mul_le_mul hA hprob (by unfold upChance; positivity)
    (by positivity)) hB (live_nonneg ..) (by positivity)) (sqrt_nonneg _))
  apply le_trans (div_le_div_of_nonneg_left (by positivity) (mul_pos (sqrt_pos.mpr hz) hr0) hQ)
  change F/√m*(1/2+β/128)*(F/√m)/(√z*√m) ≤ (1/2+β/128)*F^2/(√z*((m:ℝ)*√m))
  apply le_of_eq
  have he : (m:ℝ)*√m=(√(m:ℝ))^3 := by rw [pow_succ,Real.sq_sqrt hm0.le]
  rw [he]; ring

end CentralUnimodality.MarkedExcursion
