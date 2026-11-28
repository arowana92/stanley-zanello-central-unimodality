module

public import CentralUnimodality.ScaledSexticInputs
public import CentralUnimodality.QuadrantTail
import CentralUnimodality.AliasTail

/-! Beyond the wide logarithmic arc a fixed initial segment already makes both
Fourier symbols negligible on the retained time interval. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real PowerSeries

private theorem square_angle {ω τ : ℝ} (hω : ω^2=τ^3/32) (j : ℕ) :
    32*(|ω| *(2*(j:ℝ)+1))^2=τ*(2*(j*τ)+τ)^2 := by
  rw [mul_pow,sq_abs,hω]
  ring

private theorem outer_parameters {ω τ : ℝ} {j N : ℕ} (hτ : 0≤τ) (hω : ω^2=τ^3/32)
    (hj : j≤N) (hN : 10000≤N) (hu : (N:ℝ)*τ≤114)
    (outside : 9/8 < |ω| *(2*j+1)) :
    28<(j:ℝ)*τ ∧ 1/2000<τ ∧ (N:ℝ)<228000 ∧ τ≤114/10000 := by
  have maxN : (10000:ℝ)≤N := by exact_mod_cast hN
  have upper : τ≤114/10000 := by linarith only [mul_le_mul_of_nonneg_right maxN hτ,hu]
  have jm : (j:ℝ)*τ≤114 := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) hτ).trans hu
  have sq := (sq_lt_sq₀ (by norm_num) (by positivity)).mpr outside
  have big : 32*(9/8:ℝ)^2<τ*(2*(j*τ)+τ)^2 := by
    rw [← square_angle hω]; linarith only [sq]
  have cap {a b : ℝ} (h₁ : (j:ℝ)*τ≤a) (h₂ : τ≤b) :
      τ*(2*(j*τ)+τ)^2≤b*(2*a+114/10000)^2 := by
    have angle : 2*(j*τ)+τ≤2*a+114/10000 := by linarith only [h₁,upper]
    apply mul_le_mul h₂ (pow_le_pow_left₀ (by positivity) angle 2) (sq_nonneg _) (hτ.trans h₂)
  have time : 28<(j:ℝ)*τ := by
    by_contra! h
    linarith only [big,cap h upper]
  have step : 1/2000<τ := by
    by_contra! h
    linarith only [big,cap jm h]
  have n0 : (0:ℝ)<N := by linarith only [maxN]
  exact ⟨time,step,by linarith only [mul_lt_mul_of_pos_left step n0,hu],upper⟩

theorem quadratic_outer_prefix {ω τ : ℝ} {j N : ℕ} (hτ : 0≤τ) (hω : ω^2=τ^3/32)
    (hj : j≤N) (hN : 10000≤N) (hu : (N:ℝ)*τ≤114) (outside : 9/8 < |ω| *(2*j+1)) :
    ∀ n≥2*j, ‖coeff n (fairSeries (areaCharacter ω) words)‖≤exp (-140) ∧
      ‖coeff n (fairSeries (areaCharacter ω) bridges)‖≤exp (-140) := by
  obtain ⟨time,step,_,upper⟩ := outer_parameters hτ hω hj hN hu outside
  have tp : 0<τ := by linarith only [step]
  let l := ⌊25/τ⌋₊
  have L : (l:ℝ)*τ≤25 := (le_div_iff₀ tp).mp (Nat.floor_le (by positivity))
  have L' : 25<((l:ℝ)+1)*τ := (div_lt_iff₀ tp).mp (Nat.lt_floor_add_one _)
  have low : 24≤(l:ℝ)*τ := by linarith only [L',upper]
  have lj : l≤j := by exact_mod_cast (le_of_mul_le_mul_right (by linarith only [L,time] :
    (l:ℝ)*τ≤j*τ) tp)
  have angle : |ω| *(2*l+1)≤π/2 := by
    have cap := pow_le_pow_left₀ (show 0≤2*((l:ℝ)*τ)+τ by positivity)
      (show 2*((l:ℝ)*τ)+τ≤50+114/10000 by linarith only [L,upper]) 2
    have up := mul_le_mul upper cap (by positivity) (by norm_num : (0:ℝ)≤114/10000)
    rw [← square_angle hω] at up
    have small : |ω| *(2*l+1)≤3/2 := (sq_le_sq₀ (by positivity) (by norm_num)).mp (by linarith only [up])
    linarith only [small,pi_gt_three]
  have cost : 140≤|ω|^2*(4*(l:ℝ)^3-l)/12 := by
    have big := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤24) low 3
    have small := mul_le_mul L (pow_le_pow_left₀ hτ upper 2) (sq_nonneg _) (by norm_num : (0:ℝ)≤25)
    rw [sq_abs,hω]
    linarith only [big,small]
  have pref := (pair_prefix_gaussian (abs_nonneg ω) l angle).trans (exp_le_exp.mpr (neg_le_neg cost))
  have even : pairFactor |ω| l=pairFactor ω l := by
    rcases le_total 0 ω with h|h
    · rw [abs_of_nonneg h]
    · simp [abs_of_nonpos h,pairFactor]
  rw [even] at pref
  intro n hn
  have h := fair_inputs_after_pairs ω (l:=l) (n:=n) (by omega)
  exact ⟨h.1.trans pref,h.2.trans pref⟩

private theorem outer_trial_error {Z : ℂ} {g A B τ : ℝ} (time : 1/2000≤τ) (step : τ≤1)
    (small : ‖Z‖≤1000*exp (-140)) (g0 : 0≤g) (gt : g≤exp (-140))
    (loA : 0≤A) (hiA : A≤10^10) (loB : 0≤B) (hiB : B≤10^12) :
    ‖Z-(g*(1-τ*A+τ^2*(A^2/2-B)):ℝ)‖≤τ^3/10^18 := by
  have ht : 0≤τ := by linarith only [time]
  have m := mul_le_mul step hiA loA (by norm_num : (0:ℝ)≤1)
  have q := mul_le_mul (pow_le_pow_left₀ ht step 2) hiB loB (by norm_num : (0:ℝ)≤1^2)
  have m' := pow_le_pow_left₀ (mul_nonneg ht loA) m 2
  have t : |1-τ*A+τ^2*(A^2/2-B)|≤10^21 := by
    rw [abs_le]
    constructor <;> linarith only [m,q,m',sq_nonneg (τ*A),mul_nonneg (sq_nonneg τ) loB,mul_nonneg ht loA]
  have trial : ‖((g*(1-τ*A+τ^2*(A^2/2-B)):ℝ):ℂ)‖≤exp (-140)*10^21 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg g0]
    exact mul_le_mul gt t (abs_nonneg _) (exp_pos _).le
  have decay : exp (-140:ℝ)≤1/10^55 := by
    have e : (2.7:ℝ)≤exp 1 := by linarith only [exp_one_gt_d9]
    have h := pow_le_pow_left₀ (by norm_num) e 140
    rw [← exp_nat_mul] at h
    rw [exp_neg,one_div]
    exact inv_anti₀ (by positivity) ((by norm_num : (10:ℝ)^55≤2.7^140).trans (by simpa only [Nat.cast_ofNat,mul_one] using h))
  calc
    _ ≤ (1000+10^21)*exp (-140) := by linarith only [norm_sub_le Z ((g*(1-τ*A+τ^2*(A^2/2-B)):ℝ):ℂ),small,trial]
    _ ≤ (1000+10^21)*(1/10^55:ℝ) := mul_le_mul_of_nonneg_left decay (by positivity)
    _ ≤ (1/2000:ℝ)^3/10^18 := by norm_num
    _ ≤ _ := div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) time 3) (by positivity)

theorem quadratic_outer_symbols {ω τ : ℝ} {j N σ : ℕ} (hs : σ≤1) (hτ : 0≤τ) (hω : ω^2=τ^3/32)
    (hj : j≤N) (hN : 10000≤N) (hu : (N:ℝ)*τ≤114) (outside : 9/8 < |ω| *(2*j+1))
    (v : ℝ) (hv : v=j*τ) :
    (let A := freeLogCorrection σ v; let B := freeSecondLog σ v
     ‖coeff (2*j+σ) (fairSeries (areaCharacter ω) words)-(freeCurve v*(1-τ*A+τ^2*(A^2/2-B)):ℝ)‖≤τ^3/10^18) ∧
    (let A := bridgeLogCorrection v; let B := bridgeSecondLog v
     ‖coeff (2*j) (fairSeries (areaCharacter ω) bridges)/(survival j:ℂ)-
       (bridgeCurve v*(1-τ*A+τ^2*(A^2/2-B)):ℝ)‖≤τ^3/10^18) := by
  obtain ⟨time,step,cap,upper⟩ := outer_parameters hτ hω hj hN hu outside
  rw [← hv] at time
  have v0 : 0≤v := by linarith only [time]
  have vcap : v≤114 := hv ▸ (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) hτ).trans hu
  have vsmall (k : ℕ) := pow_le_pow_left₀ v0 vcap k
  have vbig := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤28) time.le 3
  have st : τ≤1 := by linarith only [upper]
  have pref := quadratic_outer_prefix hτ hω hj hN hu outside
  have j0 : 0<j := by
    by_contra! z
    rw [show j=0 by omega] at hv
    norm_num [hv] at time
  have jc : (j:ℝ)≤228000 := (Nat.cast_le.mpr hj).trans cap.le
  have inv : (survival j)⁻¹≤1000 := (survival_inv_le j0).trans (by
    have rt : sqrt (j:ℝ)≤500 := (sqrt_le_iff).mpr ⟨by norm_num,by linarith only [jc]⟩
    linarith only [rt])
  have b := (pref (2*j) le_rfl).2
  have bn : ‖coeff (2*j) (fairSeries (areaCharacter ω) bridges)/(survival j:ℂ)‖≤1000*exp (-140) := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (survival_pos _),div_eq_mul_inv,mul_comm 1000]
    exact mul_le_mul b inv (inv_nonneg.mpr (survival_pos j).le) (exp_pos _).le
  have sp : (σ:ℝ)≤1 := by exact_mod_cast hs
  have fA : freeLogCorrection σ v≤10^10 := by
    unfold freeLogCorrection
    have p := mul_le_mul (show (2*σ+1:ℝ)≤3 by linarith only [sp]) (vsmall 2) (sq_nonneg _) (by norm_num)
    linarith only [p,vsmall 5]
  have fB : freeSecondLog σ v≤10^12 := by
    unfold freeSecondLog
    have p := mul_le_mul (show (2*σ+1:ℝ)≤3 by linarith only [sp]) (vsmall 4) (by positivity) (by norm_num)
    have q := mul_le_mul (show (12*σ+1:ℝ)≤13 by linarith only [sp]) vcap v0 (by norm_num)
    linarith only [p,q,vsmall 7]
  dsimp only
  constructor
  · apply outer_trial_error step.le st _ (exp_pos _).le (exp_le_exp.mpr (by linarith only [vbig]))
      (by unfold freeLogCorrection; positivity) fA (by unfold freeSecondLog; positivity) fB
    linarith only [(pref (2*j+σ) (by omega)).1,exp_pos (-140:ℝ)]
  · apply outer_trial_error step.le st bn (exp_pos _).le (exp_le_exp.mpr (by linarith only [vbig]))
      (by unfold bridgeLogCorrection; positivity) (by unfold bridgeLogCorrection; linarith only [vsmall 2,vsmall 5])
      (by unfold bridgeSecondLog; positivity) (by unfold bridgeSecondLog; linarith only [vsmall 4,vsmall 7])

noncomputable def quadraticSymbolCost (g A B C τ : ℝ) :=
  g*(C+A^3/6+A*B+τ*B^2/2)+1/10^18

noncomputable def freeQuadraticCost (σ : ℕ) (v τ : ℝ) :=
  quadraticSymbolCost (freeCurve v) (freeLogCorrection σ v) (freeSecondLog σ v) (freeThirdLogBound v τ) τ

noncomputable def bridgeQuadraticCost (v τ : ℝ) :=
  quadraticSymbolCost (bridgeCurve v) (bridgeLogCorrection v) (bridgeSecondLog v) (bridgeThirdLogBound v τ) τ

theorem retained_quadratic_symbols {ω τ : ℝ} {j N σ : ℕ} (hs : σ≤1) (hτ : 0≤τ) (hω : ω^2=τ^3/32)
    (hj : j≤N) (hN : 10000≤N) (hu : (N:ℝ)*τ≤114) (v : ℝ) (hv : v=j*τ) :
    (let A := freeLogCorrection σ v; let B := freeSecondLog σ v
     ‖coeff (2*j+σ) (fairSeries (areaCharacter ω) words)-(freeCurve v*(1-τ*A+τ^2*(A^2/2-B)):ℝ)‖≤
       τ^3*freeQuadraticCost σ v τ) ∧
    (let A := bridgeLogCorrection v; let B := bridgeSecondLog v
     ‖coeff (2*j) (fairSeries (areaCharacter ω) bridges)/(survival j:ℂ)-
       (bridgeCurve v*(1-τ*A+τ^2*(A^2/2-B)):ℝ)‖≤τ^3*bridgeQuadraticCost v τ) := by
  have v0 : 0≤v := hv ▸ mul_nonneg (Nat.cast_nonneg _) hτ
  dsimp only [freeQuadraticCost,bridgeQuadraticCost,quadraticSymbolCost]
  by_cases small : |ω| *(2*j+1)≤9/8
  · have sa : |ω| *(2*j+σ)≤9/8 := (mul_le_mul_of_nonneg_left
        (show 2*(j:ℝ)+σ≤2*j+1 by exact_mod_cast (show 2*j+σ≤2*j+1 by omega)) (abs_nonneg _)).trans small
    have ba : |ω| *(2*j)≤9/8 := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1))
      (abs_nonneg _)).trans small
    have f := free_quadratic_symbol hs hτ hω sa v hv
    have b := bridge_quadratic_symbol hτ hω ba v hv
    dsimp only at f b
    constructor <;> linarith only [f,b,pow_nonneg hτ 3]
  · obtain ⟨f,b⟩ := quadratic_outer_symbols hs hτ hω hj hN hu (lt_of_not_ge small) v hv
    dsimp only at f b
    constructor
    · apply f.trans
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hτ 3)
      unfold freeCurve freeLogCorrection freeSecondLog freeThirdLogBound
      rw [one_div (10^18:ℝ)]
      apply le_add_of_nonneg_left
      positivity
    · apply b.trans
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hτ 3)
      unfold bridgeCurve bridgeLogCorrection bridgeSecondLog bridgeThirdLogBound
      rw [one_div (10^18:ℝ)]
      apply le_add_of_nonneg_left
      positivity

end CentralUnimodality.ReturnSplit
