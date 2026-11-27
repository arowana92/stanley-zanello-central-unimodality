module

public import CentralUnimodality.BernoulliTaylor
public import CentralUnimodality.PrefixRankMixture
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Fourier inversion of the actual tilted suffix rank on every integer
site. The centered transform is the product of the Bernoulli factors. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory intervalIntegral

noncomputable def phase (a : ℝ) := Complex.exp ((a:ℂ)*Complex.I)

theorem phase_add (a b : ℝ) : phase (a+b)=phase a*phase b := by
  simp [phase,add_mul,Complex.exp_add]

@[simp] theorem phase_zero : phase 0=1 := by simp [phase]
@[simp] theorem phase_norm (x : ℝ) : ‖phase x‖=1 := by simp [phase,Complex.norm_exp]

noncomputable def suffixTransform (c θ : ℝ) (m : ℕ) : ℂ :=
  ∏ i ∈ Finset.range m, bernoulliFactor (upChance (-(c*(i+1)))) ((i+1)*θ)

private theorem mean_succ (c : ℝ) (m : ℕ) : meanRank c (m+1) =
    meanRank c m + (m+1)*upChance (-(c*(m+1))) := by
  rw [meanRank,Finset.sum_range_succ]
  have h (u : ℝ) : (1-tanh u)/2=upChance (-u) := by linarith only [up_total u,up_drift u]
  rw [mul_div_assoc,h]; rfl

theorem suffix_transform_words (c θ : ℝ) (m : ℕ) : suffixTransform c θ m =
    ∑ w ∈ words m, (signMass c (c*m) w:ℂ)*phase (θ*((wordParts w).sum-meanRank c m)) := by
  induction m with
  | zero => simp [suffixTransform,signMass,words,wordParts,meanRank]
  | succ m ih =>
    let r := (m:ℝ)+1
    let u := c*r
    let p := upChance (-u)
    let q := upChance u
    let F := fun w => (signMass c (c*m) w:ℂ)*phase (θ*((wordParts w).sum-meanRank c m))
    let K := fun (b : Bool) => (if b then (p:ℂ) else (q:ℂ))*phase (r*θ*((if b then 1 else 0)-p))
    have he (b : Bool) (w : List Bool) (hw : w ∈ words m) :
        (signMass c (c*(m+1:ℕ)) (b::w):ℂ)*phase (θ*((wordParts (b::w)).sum-meanRank c (m+1))) =
        K b*F w := by
      have hm : signMass c (c*(m+1:ℕ)) (b::w) = (if b then p else q)*signMass c (c*m) w := by
        have he : u-c=c*m := by dsimp [u,r]; ring
        cases b <;> simp [signMass,step,p,q,upChance,Nat.cast_succ,← show u=c*((m:ℝ)+1) from rfl,he]
      have hr : ((wordParts (b::w)).sum:ℝ)= (wordParts w).sum+(if b then r else 0) := by
        cases b <;> simp [wordParts,r,mem_words.mp hw]
      rw [hm,hr,mean_succ]
      change _*phase (θ*((wordParts w).sum+(if b then r else 0)-(meanRank c m+r*p))) = _
      have harg : θ*((wordParts w).sum+(if b then r else 0)-(meanRank c m+r*p)) =
          r*θ*((if b then 1 else 0)-p) + θ*((wordParts w).sum-meanRank c m) := by cases b <;> simp <;> ring
      rw [harg,phase_add]
      dsimp only [F,K]
      push_cast
      cases b <;> simp <;> ring
    have hK : K false+K true = bernoulliFactor p (r*θ) := by
      have hq : q=1-p := by dsimp only [q,p]; linarith only [up_total u]
      simp only [K,bernoulliFactor,phase,Bool.false_eq_true,ite_false,ite_true,zero_sub,hq]
      push_cast; ring_nf
    rw [suffixTransform,Finset.prod_range_succ,sum_cons_words]
    change suffixTransform c θ m*bernoulliFactor p (r*θ) = _
    rw [Finset.sum_congr rfl (fun w hw => he false w hw),Finset.sum_congr rfl (fun w hw => he true w hw),
      ← Finset.mul_sum,← Finset.mul_sum,← add_mul,hK,ih,mul_comm]

private theorem integral_lattice_phase (b : ℤ) :
    (∫ θ in -π..π, phase (θ*b)) = if b=0 then ((2*π:ℝ):ℂ) else 0 := by
  by_cases hb : b=0
  · simp [hb,intervalIntegral.integral_const,Complex.real_smul]; ring
  · let z := (b:ℂ)*Complex.I
    have hz : z ≠ 0 := mul_ne_zero (by exact_mod_cast hb) Complex.I_ne_zero
    have hd (θ : ℝ) : phase (θ*b) = Complex.exp (z*θ) := by simp [phase,z]; congr 1; ring
    simp_rw [hd]
    rw [integral_exp_mul_complex hz,ite_eq_right hb]
    have he := Complex.exp_int_mul_two_pi_mul_I b
    have hphase : Complex.exp (z*(π:ℂ)) = Complex.exp (z*((-π:ℝ):ℂ)) := by
      have ha : z*(π:ℂ)=z*((-π:ℝ):ℂ)+(b:ℂ)*(2*(π:ℂ)*Complex.I) := by dsimp [z]; push_cast; ring
      rw [ha,Complex.exp_add,he,mul_one]
    rw [hphase,sub_self,zero_div]

theorem suffix_rank_inversion (c : ℝ) (m : ℕ) (k : ℤ) :
    (∫ θ in -π..π, suffixTransform c θ m * phase (-θ*((k:ℝ)-meanRank c m))) =
      ((2*π:ℝ):ℂ)*(freeRankMass c m k:ℂ) := by
  simp_rw [suffix_transform_words,Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [freeRankMass,Complex.ofReal_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    let a := ((wordParts w).sum:ℤ)
    have he (θ : ℝ) : (signMass c (c*m) w:ℂ)*phase (θ*((wordParts w).sum-meanRank c m))*
        phase (-θ*((k:ℝ)-meanRank c m)) = (signMass c (c*m) w:ℂ)*phase (θ*((a-k:ℤ):ℝ)) := by
      rw [mul_assoc,← phase_add]
      congr 2; dsimp [a]; simp only [Int.cast_sub,Int.cast_natCast]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul,integral_lattice_phase]
    by_cases h : a=k
    · simp [h,show ((wordParts w).sum:ℤ)=k from h,mul_comm]
    · rw [ite_eq_right (sub_ne_zero.mpr h),ite_eq_right (show ((wordParts w).sum:ℤ) ≠ k from h)]
      simp
  · intro w _
    apply Continuous.intervalIntegrable
    dsimp [phase]
    fun_prop

end CentralUnimodality.MarkedExcursion
