module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.LinearCombination

/-! Integer enclosures for the exact cosines on power-of-two grids. -/
@[expose] public section

namespace CentralUnimodality.DyadicAngle

def root (d a : ℕ) := Nat.sqrt (d*a/2)

private theorem root_bounds (d a : ℕ) :
    2*(root d a : ℝ)^2 ≤ d*(a:ℝ) ∧ d*(a:ℝ) < 2*((root d a:ℝ)+1)^2 := by
  have h := Nat.sqrt_le' (d*a/2)
  have h' := Nat.lt_succ_sqrt' (d*a/2)
  change (root d a)^2 ≤ d*a/2 at h
  change d*a/2 < (root d a+1)^2 at h'
  constructor
  · exact_mod_cast (by omega : 2*(root d a)^2 ≤ d*a)
  · exact_mod_cast (by omega : d*a < 2*(root d a+1)^2)

def lowerRoot (d a : ℕ) := min d (root d a)
def upperRoot (d a : ℕ) := min d (root d a+1)

private theorem half_bounds {d a b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hπ : x ≤ Real.pi)
    (ha : (a:ℝ) ≤ d*(1+Real.cos x)) (hb : d*(1+Real.cos x) ≤ (b:ℝ)) :
    (lowerRoot d a:ℝ) ≤ d*Real.cos (x/2) ∧ d*Real.cos (x/2) ≤ (upperRoot d b:ℝ) := by
  let y : ℝ := d*Real.cos (x/2)
  have hcos := Real.cos_nonneg_of_mem_Icc (x := x/2) ⟨by linarith [Real.pi_pos],by linarith⟩
  have hy : 0 ≤ y := mul_nonneg (by positivity) hcos
  have htop : y ≤ d := by simpa [y] using mul_le_mul_of_nonneg_left (Real.cos_le_one (x/2)) (Nat.cast_nonneg (α := ℝ) d)
  have ht : 2*y^2 = (d:ℝ)*(d*(1+Real.cos x)) := by
    rw [show x = 2*(x/2) by ring,Real.cos_two_mul]
    dsimp [y]
    ring
  have hlo : (root d a:ℝ) ≤ y := by
    have hl := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg (α := ℝ) d)
    have hh := (root_bounds d a).1
    nlinarith [sq_nonneg ((root d a:ℝ)-y)]
  have hhi : y ≤ (root d b:ℝ)+1 := by
    have hl := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) d)
    have hh := (root_bounds d b).2
    nlinarith [sq_nonneg (y-((root d b:ℝ)+1))]
  constructor
  · exact (by exact_mod_cast min_le_right d (root d a) : (lowerRoot d a:ℝ) ≤ root d a).trans hlo
  · simpa [upperRoot] using le_min htop hhi

/-- Enclose d(1+cos(tπ/2^k)) by two integers for 0 ≤ t ≤ 2^k. -/
def bounds (d : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0,t => if t=0 then (2*d,2*d) else (0,0)
  | k+1,t =>
    let q := 2^k
    let s := if t ≤ q then t else 2*q-t
    let v := bounds d k s
    let lo := lowerRoot d v.1
    let hi := upperRoot d v.2
    if t ≤ q then (d+lo,d+hi) else (d-hi,d-lo)

private noncomputable def angle (k t : ℕ) := (t:ℝ)*Real.pi/(2:ℝ)^k

private theorem angle_half (k t : ℕ) : angle (k+1) t = angle k t/2 := by
  simp [angle,pow_succ,div_div]

private theorem angle_range {k t : ℕ} (h : t ≤ 2^k) : 0 ≤ angle k t ∧ angle k t ≤ Real.pi := by
  constructor
  · unfold angle
    positivity
  · apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^k)).mpr
    rw [mul_comm Real.pi]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) Real.pi_pos.le

theorem bounds_sound (d k t : ℕ) (ht : t ≤ 2^k) :
    ((bounds d k t).1:ℝ) ≤ d*(1+Real.cos ((t:ℝ)*Real.pi/2^k)) ∧
    d*(1+Real.cos ((t:ℝ)*Real.pi/2^k)) ≤ ((bounds d k t).2:ℝ) := by
  change ((bounds d k t).1:ℝ) ≤ d*(1+Real.cos (angle k t)) ∧
    d*(1+Real.cos (angle k t)) ≤ ((bounds d k t).2:ℝ)
  induction k generalizing t with
  | zero =>
    rcases (by simpa using ht : t ≤ 1) |> Nat.le_one_iff_eq_zero_or_eq_one.mp with rfl|rfl <;>
      norm_num [bounds,angle,mul_comm]
  | succ k ih =>
    rw [pow_succ] at ht
    by_cases h : t ≤ 2^k
    · have hr := angle_range h
      have hi := ih t h
      have hh := half_bounds hr.1 hr.2 hi.1 hi.2
      simpa only [bounds,ite_eq_left h,angle_half,Nat.cast_add,mul_add,mul_one,add_le_add_iff_left] using hh
    · let s := 2*2^k-t
      have hs : s ≤ 2^k := by dsimp [s]; omega
      have hr := angle_range hs
      have hi := ih s hs
      have hh := half_bounds hr.1 hr.2 hi.1 hi.2
      have he : angle (k+1) t = Real.pi-angle k s/2 := by
        have hts : (t:ℝ)+(s:ℝ) = 2*(2:ℝ)^k := by exact_mod_cast (show t+s = 2*2^k by dsimp [s]; omega)
        dsimp [angle]
        rw [pow_succ]
        field_simp
        linear_combination hts
      have hl : lowerRoot d (bounds d k s).1 ≤ d := min_le_left ..
      have hu : upperRoot d (bounds d k s).2 ≤ d := min_le_left ..
      simp only [bounds,ite_eq_right h,he,Real.cos_pi_sub,mul_add,mul_one,mul_neg]
      rw [Nat.cast_sub hu,Nat.cast_sub hl]
      constructor <;> linarith only [hh.1,hh.2]

/-- The first quadrant needs only the positive square root. The angle is
tπ/2^(k+1), where t runs from 0 to 2^k inclusive. -/
def cosine (d k t : ℕ) : ℕ × ℕ :=
  let a := bounds d k t
  (lowerRoot d a.1,upperRoot d a.2)

def sine (d k t : ℕ) : ℕ × ℕ := cosine d k (2^k-t)

theorem cosine_sound (d k t : ℕ) (ht : t ≤ 2^k) :
    ((cosine d k t).1:ℝ) ≤ d*Real.cos ((t:ℝ)*Real.pi/2^(k+1)) ∧
    d*Real.cos ((t:ℝ)*Real.pi/2^(k+1)) ≤ ((cosine d k t).2:ℝ) := by
  have h := bounds_sound d k t ht
  have hr := angle_range ht
  have hh := half_bounds hr.1 hr.2 h.1 h.2
  simpa only [cosine,angle,pow_succ,div_div] using hh

theorem sine_sound (d k t : ℕ) (ht : t ≤ 2^k) :
    ((sine d k t).1:ℝ) ≤ d*Real.sin ((t:ℝ)*Real.pi/2^(k+1)) ∧
    d*Real.sin ((t:ℝ)*Real.pi/2^(k+1)) ≤ ((sine d k t).2:ℝ) := by
  have h := cosine_sound d k (2^k-t) (Nat.sub_le ..)
  have he : ((2^k-t:ℕ):ℝ)*Real.pi/2^(k+1) = Real.pi/2-(t:ℝ)*Real.pi/2^(k+1) := by
    rw [Nat.cast_sub ht,Nat.cast_pow,Nat.cast_ofNat,pow_succ]
    field_simp
  simpa only [sine,he,Real.cos_pi_div_two_sub] using h

end CentralUnimodality.DyadicAngle
