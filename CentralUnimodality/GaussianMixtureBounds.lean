module

public import CentralUnimodality.PrefixRankMixture
import Mathlib.Analysis.Real.Pi.Bounds

/-! Gaussian comparisons for a mixture whose squared displacement has
known mean bound. Only positivity and linearity of averaging are used. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

noncomputable def normalHeight : ℝ := 1/√(2*π)
noncomputable def bell (y : ℝ) := exp (-(y^2)/2)

private theorem normal_height_bounds : 3989/10000 ≤ normalHeight ∧ normalHeight ≤ 399/1000 := by
  have hpos : 0 < √(2*π) := by positivity
  have hu : √(2*π) ≤ 10000/3989 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [pi_lt_d4]⟩
  have hl : 1000/399 ≤ √(2*π) := Real.le_sqrt_of_sq_le (by linarith only [pi_gt_d4])
  constructor
  · apply (le_div_iff₀ hpos).mpr; linarith only [hu]
  · apply (div_le_iff₀ hpos).mpr; linarith only [hl]

private theorem normal_slope (y : ℝ) : |normalHeight*y*bell y| < 97/400 := by
  have hb : (|y| * bell y)^2 ≤ exp (-1) := by
    have h := mul_le_mul_of_nonneg_right (add_one_le_exp (y^2-1)) (exp_pos (-(y^2))).le
    rw [← exp_add,show y^2-1+ -(y^2) = -1 by ring] at h
    rw [mul_pow,sq_abs,bell,sq (exp (-(y^2)/2)),← exp_add,show -(y^2)/2+ -(y^2)/2= -(y^2) by ring]
    linarith only [h]
  have he : exp (1/2) ≥ 79/48 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2) 4
    norm_num [Finset.sum_range_succ,Nat.factorial] at h ⊢
    exact h
  have hbell : |y| * bell y ≤ 1/exp (1/2) := by
    have heq : (1/exp (1/2))^2 = exp (-1) := by
      rw [one_div,← exp_neg,sq,← exp_add]; norm_num
    rw [← heq] at hb
    exact (sq_le_sq₀ (mul_nonneg (abs_nonneg _) (exp_pos _).le) (by positivity)).mp hb
  have hbell' := hbell.trans (one_div_le_one_div_of_le (by norm_num) he)
  rw [abs_mul,abs_mul,abs_of_nonneg (show 0 ≤ normalHeight by dsimp [normalHeight]; positivity),
    abs_of_pos (show 0 < bell y from exp_pos _),mul_assoc]
  calc
    _ ≤ (399/1000)*(1/(79/48)) := mul_le_mul normal_height_bounds.2 hbell'
      (mul_nonneg (abs_nonneg _) (exp_pos _).le) (by norm_num)
    _ < _ := by norm_num

private theorem tangent_lower (B y : ℝ) : exp (-B/2)*(1+(B-y^2)/2) ≤ bell y := by
  have he := mul_le_mul_of_nonneg_left (add_one_le_exp ((B-y^2)/2)) (exp_pos (-B/2)).le
  rw [← exp_add,show -B/2+(B-y^2)/2= -(y^2)/2 by ring] at he
  simpa [bell,add_comm] using he

private theorem tangent_upper {B : ℝ} (hB : 0 ≤ B) (y : ℝ) :
    y^2*bell y ≤ B/(1+B/2)+(y^2-B)/(1+B/2)^2 := by
  have hv : 0 < 1+y^2/2 := by positivity
  have hp : 0 < 1+B/2 := by positivity
  have h : bell y ≤ 1/(1+y^2/2) := by
    rw [bell,neg_div,exp_neg,← one_div]
    exact one_div_le_one_div_of_le hv (by linarith only [add_one_le_exp (y^2/2)])
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans
  field_simp [hp.ne',hv.ne']
  nlinarith only [sq_nonneg (y^2-B)]

private theorem average_affine {ι : Type*} (F : (ι → ℝ) →ₗ[ℝ] ℝ) (hn : F 1=1)
    (a b : ℝ) (x : ι → ℝ) : F (fun i => a+b*x i) = a+b*F x := by
  rw [show (fun i => a+b*x i) = a • (1:ι → ℝ)+b • x by funext i; simp]
  rw [map_add,map_smul,map_smul,hn]; simp

theorem gaussian_average {ι : Type*} (F : (ι → ℝ) →ₗ[ℝ] ℝ) (hf : Monotone F) (hn : F 1=1)
    (y : ι → ℝ) {B : ℝ} (hb : 0 ≤ B) (hY : F (fun i => (y i)^2) ≤ B) :
    exp (-B/2) ≤ F (fun i => bell (y i)) ∧
    F (fun i => (y i)^2*bell (y i)) ≤ B/(1+B/2) := by
  have hp : 0 < 1+B/2 := by positivity
  constructor
  · have h := hf (show (fun i => exp (-B/2)*(1+B/2) + (-(exp (-B/2))/2)*(y i)^2) ≤
        fun i => bell (y i) by
      intro i; convert tangent_lower B (y i) using 1; ring)
    rw [average_affine F hn _ _ (fun i => (y i)^2)] at h
    linarith only [h,mul_le_mul_of_nonneg_left hY (exp_pos (-B/2)).le]
  · have h := hf (show (fun i => (y i)^2*bell (y i)) ≤ fun i =>
        (B/(1+B/2)-B/(1+B/2)^2)+(1/(1+B/2)^2)*(y i)^2 by
      intro i; convert tangent_upper hb (y i) using 1; ring)
    rw [average_affine F hn _ _ (fun i => (y i)^2)] at h
    apply h.trans
    calc
      _ ≤ B/(1+B/2)-B/(1+B/2)^2+1/(1+B/2)^2*B := by gcongr
      _ = _ := by ring

/-- Transfer three pointwise suffix estimates to a mixture. The functions
g₀,g₁,g₂ already include the powers σ,σ²,σ³ respectively. -/
theorem gaussian_difference_bounds {ι : Type*} (F : (ι → ℝ) →ₗ[ℝ] ℝ) (hf : Monotone F) (hn : F 1=1)
    (y g₀ g₁ g₂ : ι → ℝ) {B : ℝ} (hb : 0 ≤ B) (hY : F (fun i => (y i)^2) ≤ B)
    (h₀ : ∀ i, |g₀ i-normalHeight*bell (y i)| ≤ 5/1000)
    (h₁ : ∀ i, |g₁ i+normalHeight*y i*bell (y i)| ≤ 7/1000)
    (h₂ : ∀ i, |g₂ i-normalHeight*((y i)^2-1)*bell (y i)| ≤ 10/1000) :
    3989/10000*exp (-B/2)-5/1000 ≤ F g₀ ∧ |F g₁| < 1/4 ∧
      F g₂ ≤ normalHeight*(B/(1+B/2)-exp (-B/2))+10/1000 := by
  obtain ⟨hlo,hhi⟩ := gaussian_average F hf hn y hb hY
  have hN : 0 ≤ normalHeight := by dsimp [normalHeight]; positivity
  constructor
  · have h := hf (show (fun i => -(5/1000)+normalHeight*bell (y i)) ≤ g₀ by
      intro i; linarith only [(abs_le.mp (h₀ i)).1])
    rw [average_affine F hn _ _ (fun i => bell (y i))] at h
    linarith only [h,mul_le_mul_of_nonneg_left hlo hN,
      mul_le_mul_of_nonneg_right normal_height_bounds.1 (exp_pos (-B/2)).le]
  constructor
  · have h (i) : |g₁ i| ≤ 499/2000 := by
      have H := abs_lt.mp (normal_slope (y i))
      have G := abs_le.mp (h₁ i)
      rw [abs_le]; constructor <;> linarith only [H.1,H.2,G.1,G.2]
    have hlo' := hf (show (-(499/2000:ℝ)) • (1:ι → ℝ) ≤ g₁ from fun i => by simpa using (abs_le.mp (h i)).1)
    have hhi' := hf (show g₁ ≤ (499/2000:ℝ) • (1:ι → ℝ) from fun i => by simpa using (abs_le.mp (h i)).2)
    rw [map_smul,hn,smul_eq_mul,mul_one] at hlo' hhi'
    exact lt_of_le_of_lt (abs_le.mpr ⟨hlo',hhi'⟩) (by norm_num)
  · let a := fun i => (y i)^2*bell (y i)
    let b := fun i => bell (y i)
    have h := hf (show g₂ ≤ (10/1000:ℝ) • (1:ι → ℝ) + normalHeight • (a-b) by
      intro i
      change g₂ i ≤ 10/1000*1+normalHeight*((y i)^2*bell (y i)-bell (y i))
      linarith only [(abs_le.mp (h₂ i)).2])
    rw [map_add,map_smul,map_smul,map_sub,hn] at h
    change F g₂ ≤ 10/1000*1+normalHeight*(F a-F b) at h
    exact h.trans (by dsimp only [a,b]; linarith only [mul_le_mul_of_nonneg_left (sub_le_sub hhi hlo) hN])

end CentralUnimodality.MarkedExcursion
