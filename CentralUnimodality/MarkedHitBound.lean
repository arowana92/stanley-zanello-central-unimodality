module

public import CentralUnimodality.MarkedAreaIntegral
public import CentralUnimodality.CenteredCosh
public import CentralUnimodality.SurvivalBounds

/-! Individual first-hit mass under a centered linear tilt. All path
lengths and nonnegative slopes are included; c = λ/(2s) in the application. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion

open Real

/-- The fair first-hit prefactor has this exact expression for every d. -/
theorem fair_hit_survival (d : ℕ) :
    ((hitWords 1 (2*d+1)).card:ℝ)/(2:ℝ)^(2*d+1) = survival d/(2*(d+1)) := by
  have hh := first_hit_count 0 (2*d) d (by omega)
  simp only [zero_add,one_mul] at hh
  have h := Nat.choose_mul_succ_eq (2*d) d
  rw [show 2*d+1-d = d+1 by omega,← hh] at h
  have hc : (d+1)*(hitWords 1 (2*d+1)).card = d.centralBinom := by
    apply Nat.mul_left_cancel (n := 2*d+1) (by omega)
    change _ = (2*d+1)*(2*d).choose d
    nlinarith only [h]
  have he : ((d:ℝ)+1)*(hitWords 1 (2*d+1)).card = d.centralBinom := by exact_mod_cast hc
  rw [survival,← he,pow_succ,pow_mul,show (2:ℝ)^2=4 by norm_num]
  field_simp

private theorem fair_anchor : (25:ℝ)*(2*64+1)*(survival 64)^2 < 16 := by
  rw [survival,Nat.centralBinom,Nat.choose_eq_factorial_div_factorial (by decide)]
  norm_num1

theorem survival_scaled_lt (d : ℕ) : survival d * √(2*d) < 4/5 := by
  have mono : Monotone (fun j : ℕ => (2*(j:ℝ))*(survival j)^2) := by
    apply monotone_nat_of_le_succ
    intro j
    rw [survival_succ,Nat.cast_succ]
    field_simp
    nlinarith only [sq_nonneg (survival j),mul_nonneg (sq_nonneg (survival j)) (Nat.cast_nonneg (α := ℝ) j)]
  have anti : Antitone (fun j : ℕ => (2*(j:ℝ)+1)*(survival j)^2) := by
    apply antitone_nat_of_succ_le
    intro j
    rw [survival_succ,Nat.cast_succ]
    field_simp
    nlinarith only [sq_nonneg (survival j),mul_nonneg (sq_nonneg (survival j)) (Nat.cast_nonneg (α := ℝ) j)]
  have bound : 25*(2*(d:ℝ))*(survival d)^2 < 16 := by
    rcases le_total d 64 with hd|hd
    · have h := mono hd
      norm_num only [Nat.cast_ofNat] at h
      nlinarith only [h,fair_anchor,sq_nonneg (survival 64)]
    · have h := anti hd
      norm_num only [Nat.cast_ofNat] at h
      nlinarith only [h,fair_anchor,sq_nonneg (survival d)]
  apply (sq_lt_sq₀ (mul_nonneg (survival_pos _).le (sqrt_nonneg _)) (by norm_num)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity)]
  linarith only [bound]

theorem fair_hit_upper {d : ℕ} (hd : 0 < d) :
    ((hitWords 1 (2*d+1)).card:ℝ)/(2:ℝ)^(2*d+1) <
      (4/5)/(2*d*√(2*d)) := by
  rw [fair_hit_survival]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have h := mul_lt_mul_of_pos_left (survival_scaled_lt d) (by positivity : 0 < 2*(d:ℝ))
  linarith only [h]

/-- The same independent sign law used in the walk bound, with no
conditional input about the marked path, the area, or the normalizer. -/
theorem tilted_hit_gaussian (d : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    let t := 2*(d:ℝ)+1
    let y := c*t*√((d:ℝ)+1)
    let L := c^2*d*(d+1)*t/6*(1-(c*d)^2/6)
    (∑ w ∈ hitWords 1 (2*d+1), signMass c (c*d) w) ≤
      (survival d/(2*(d+1))) * exp (c*d+y^2/4-L) * (1+y/2*(√π+min (√π) y)) := by
  let t := 2*(d:ℝ)+1
  let y := c*t*√((d:ℝ)+1)
  let L := c^2*d*(d+1)*t/6*(1-(c*d)^2/6)
  let B := 1+y/2*(√π+min (√π) y)
  let A := ∑ w ∈ hitWords 1 (2*d+1), signMass c (c*d) w
  have ht : t ≠ 0 := by dsimp [t]; positivity
  have harea := area_exp_gaussian d (c := c*t) (mul_nonneg hc (by dsimp [t]; positivity))
  have hex (w : List Bool) : c*t*(walkArea w:ℝ)/(2*d+1) = c*walkArea w := by
    change _ / t = _; field_simp
  simp only [hex] at harea
  have hnum := mul_le_mul_of_nonneg_left harea (exp_pos (c*d)).le
  rw [← hit_mass_identity,← card_first_hits] at hnum
  have hpos : 0 ≤ A := Finset.sum_nonneg (fun _ _ => (signMass_pos ..).le)
  have hden := mul_le_mul_of_nonneg_left (centered_cosh_lower c d) (by positivity : 0 ≤ (2:ℝ)^(2*d+1))
  have h := (mul_le_mul_of_nonneg_left hden hpos).trans hnum
  change A * (_ * exp L) ≤ exp (c*d) * ((hitWords 1 (2*d+1)).card * (exp (y^2/4)*B)) at h
  change A ≤ _ * exp (c*d+y^2/4-L)*B
  rw [← fair_hit_survival,exp_sub,exp_add]
  apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^(2*d+1)*exp L)).mpr h |>.trans_eq
  ring

end CentralUnimodality.MarkedExcursion
