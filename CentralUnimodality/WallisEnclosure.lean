module

public import CentralUnimodality.SurvivalBounds
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-! Enclose the common odd-moment scalar using two positive trial functions
and a single exactly evaluable size. Cross-comparison of the two monotone
ratios avoids taking a limit or estimating π. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def wallisFactor (n : ℕ) : ℝ :=
  1 / (survival n * Real.sqrt (2*n))

theorem wallisFactor_pos {n : ℕ} (hn : 0 < n) : 0 < wallisFactor n := by
  unfold wallisFactor
  exact one_div_pos.mpr (mul_pos (survival_pos n) (Real.sqrt_pos.mpr (by positivity)))

theorem wallisFactor_sq {n : ℕ} (hn : 0 < n) :
    wallisFactor n ^ 2 = 1 / (2*n*(survival n)^2) := by
  rw [wallisFactor, div_pow, one_pow, mul_pow, Real.sq_sqrt (by positivity), mul_comm]

theorem wallisFactor_ratio {n : ℕ} (hn : 0 < n) :
    (1+(n:ℝ)⁻¹)*wallisFactor n^2 = (1+(n:ℝ)⁻¹/2)^2*wallisFactor (n+1)^2 := by
  rw [wallisFactor_sq hn, wallisFactor_sq (by omega), survival_succ, Nat.cast_succ]
  have hs := (survival_pos n).ne'
  have hn' : (n:ℝ) ≠ 0 := by positivity
  field_simp

private theorem ratio_step {a b s t u v : ℝ} (ha : 0 < a)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 < u) (hv : 0 < v)
    (hw : a*s^2 = b*t^2) (hp : a*u^2 ≤ b*v^2) : t/v ≤ s/u := by
  apply (div_le_div_iff₀ hv hu).mpr
  have hsq : a*(t*u)^2 ≤ a*(s*v)^2 := calc
    _ = a*u^2*t^2 := by ring
    _ ≤ b*v^2*t^2 := mul_le_mul_of_nonneg_right hp (sq_nonneg _)
    _ = a*(s*v)^2 := by linear_combination -v^2*hw
  exact (sq_le_sq₀ (mul_nonneg ht hu.le) (mul_nonneg hs hv.le)).mp ((mul_le_mul_iff_right₀ ha).mp hsq)

private theorem increasing_from {f : ℕ → ℝ} {N a b : ℕ} (ha : N ≤ a) (hab : a ≤ b)
    (h : ∀ n ≥ N, f n ≤ f (n+1)) : f a ≤ f b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact ih.trans (h n (ha.trans hn))

/-- The ratio tests are finite polynomial sign problems once L and U are
polynomial functions of 1/n. The anchor k may be on either side of n. -/
theorem wallis_anchor_enclosure {N : ℕ} (hN : 0 < N) (L U : ℕ → ℝ)
    (hp : ∀ n ≥ N, 0 < L n ∧ L n ≤ U n)
    (hL : ∀ n ≥ N, (1+(n:ℝ)⁻¹)*(L n)^2 ≤ (1+(n:ℝ)⁻¹/2)^2*(L (n+1))^2)
    (hU : ∀ n ≥ N, (1+(n:ℝ)⁻¹/2)^2*(U (n+1))^2 ≤ (1+(n:ℝ)⁻¹)*(U n)^2)
    {n k : ℕ} (hn : N ≤ n) (hk : N ≤ k) :
    L n * (wallisFactor k / U k) ≤ wallisFactor n ∧
      wallisFactor n ≤ U n * (wallisFactor k / L k) := by
  let lo (t : ℕ) := wallisFactor t / U t
  let hi (t : ℕ) := wallisFactor t / L t
  have hUpos (t : ℕ) (ht : N ≤ t) : 0 < U t := (hp t ht).1.trans_le (hp t ht).2
  have hmono (t : ℕ) (ht : N ≤ t) : lo t ≤ lo (t+1) := by
    have hw := wallisFactor_ratio (hN.trans_le ht)
    exact ratio_step (by positivity) (wallisFactor_pos (by omega)).le (wallisFactor_pos (by omega)).le
      (hUpos (t+1) (by omega)) (hUpos t ht) hw.symm (hU t ht)
  have hanti (t : ℕ) (ht : N ≤ t) : -hi t ≤ -hi (t+1) := by
    apply neg_le_neg
    exact ratio_step (by positivity) (wallisFactor_pos (by omega)).le (wallisFactor_pos (by omega)).le
      (hp t ht).1 (hp (t+1) (by omega)).1 (wallisFactor_ratio (hN.trans_le ht)) (hL t ht)
  have hedge (t : ℕ) (ht : N ≤ t) : lo t ≤ hi t :=
    div_le_div_of_nonneg_left (wallisFactor_pos (hN.trans_le ht)).le (hp t ht).1 (hp t ht).2
  have cross (a b : ℕ) (ha : N ≤ a) (hb : N ≤ b) : lo a ≤ hi b := by
    rcases le_total a b with hab | hba
    · exact (increasing_from ha hab hmono).trans (hedge b hb)
    · exact (hedge a ha).trans (neg_le_neg_iff.mp (increasing_from hb hba hanti))
  constructor
  · rw [mul_comm]
    exact (le_div_iff₀ (hp n hn).1).mp (cross k n hk hn)
  · rw [mul_comm]
    exact (div_le_iff₀ (hUpos n hn)).mp (cross n k hn hk)

end CentralUnimodality
