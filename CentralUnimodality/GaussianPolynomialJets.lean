module

public import CentralUnimodality.GaussianCellEnvelope
public import CentralUnimodality.CorrectedLocalDerivatives

/-! For an integer polynomial `P`, differentiating
`P(v) exp(-v³/b)` replaces the numerator by `b P' - 3v² P`
and multiplies the denominator by `b`. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial Real Set

def gaussianDifference (b : ℕ) (p : List ℤ) := linearRows b (-3) (powerDerivative p) (0::0::p)

noncomputable def gaussianPolynomial (b : ℕ) (p : List ℤ) (v : ℝ) :=
  (realDense p).eval v*exp (-(v^3/b))

private theorem gaussian_diff (b : ℕ) (p : List ℤ) (v : ℝ) :
    (realDense (gaussianDifference b p)).eval v=b*(realDense p).derivative.eval v-3*v^2*(realDense p).eval v := by
  simp only [gaussianDifference,dense_linear_eval,powerDerivative_real,Int.cast_natCast,Int.cast_neg,Int.cast_ofNat]
  have zero (a : List ℤ) : (realDense (0::a)).eval v=v*(realDense a).eval v := by simp [realDense,densePoly]
  rw [zero,zero]; ring

private theorem gaussianPolynomial_deriv {b : ℕ} (hb : 0<b) (p : List ℤ) (v : ℝ) :
    HasDerivAt (gaussianPolynomial b p) (gaussianPolynomial b (gaussianDifference b p) v/b) v := by
  have d := ((realDense p).hasDerivAt v).mul (((hasDerivAt_pow 3 v).div_const (b:ℝ)).neg.exp)
  convert d using 1
  · rfl
  · have br : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
    simp only [gaussianPolynomial,gaussian_diff,Pi.neg_apply,Nat.cast_ofNat]
    field_simp; ring

theorem gaussian_polynomial_jet {b : ℕ} (hb : 0<b) (p : List ℤ) (D : ℝ) (r : ℕ) :
    iteratedDeriv r (fun t => D*gaussianPolynomial b p t)=
      fun v => D/(b:ℝ)^r*gaussianPolynomial b ((gaussianDifference b)^[r] p) v := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ,ih,Function.iterate_succ_apply']
    funext v
    have d := (gaussianPolynomial_deriv hb ((gaussianDifference b)^[r] p) v).const_mul (D/(b:ℝ)^r)
    rw [d.deriv,pow_succ]; ring

def gaussianSum (b l h : ℚ) (j : ℕ) : List ℤ → ℚ
  | [] => 0
  | c::p => (if c=0 then 0 else (c.natAbs:ℚ)*gaussianEnvelope b l h j)+gaussianSum b l h (j+1) p

private theorem gaussian_sum_abs {b l h : ℚ} (hb : 0<b) (hl : 0≤l) {v : ℝ} (hv : v∈Icc (l:ℝ) (h:ℝ))
    (p : List ℤ) (j : ℕ) : |(realDense p).eval v*gaussianTerm (b:ℝ) j v|≤(gaussianSum b l h j p:ℝ) := by
  have vp : 0≤v := (Rat.cast_nonneg.mpr hl).trans hv.1
  induction p generalizing j with
  | nil => simp [realDense,densePoly,gaussianSum]
  | cons c p ih =>
    have id : (realDense (c::p)).eval v*gaussianTerm (b:ℝ) j v=
        (c:ℝ)*gaussianTerm (b:ℝ) j v+(realDense p).eval v*gaussianTerm (b:ℝ) (j+1) v := by
      simp [realDense,densePoly,gaussianTerm,pow_succ]; ring
    rw [id]
    apply (abs_add_le ..).trans
    rw [gaussianSum,Rat.cast_add]
    apply add_le_add _ (ih _)
    by_cases zero : c=0
    · simp [zero]
    · have pos : 0≤gaussianTerm (b:ℝ) j v := mul_nonneg (pow_nonneg vp j) (exp_nonneg _)
      have ma : (c.natAbs:ℝ)=|(c:ℝ)| := by simp
      simp only [zero,ite_false,Rat.cast_mul,Rat.cast_natCast,abs_mul,ma,abs_of_nonneg pos]
      exact mul_le_mul_of_nonneg_left (gaussianEnvelope_sound hb hl hv j) (abs_nonneg _)

theorem gaussian_value_bound {b : ℕ} (hb : 0<b) {l h : ℚ} (hl : 0≤l) {v : ℝ}
    (hv : v∈Icc (l:ℝ) (h:ℝ)) (p : List ℤ) :
    |gaussianPolynomial b p v|≤(gaussianSum b l h 0 p:ℝ) := by
  simpa [gaussianPolynomial,gaussianTerm] using gaussian_sum_abs (b:=(b:ℚ)) (by exact_mod_cast hb) hl hv p 0

def gaussianUnits (b : ℕ) (l h : ℚ) (p : List ℤ) (d : ℕ) : ℕ := ⌈10^30*gaussianSum b l h 0 p/d⌉₊

theorem gaussian_units_bound {b d : ℕ} (hb : 0<b) (hd : 0<d) {l h : ℚ} (hl : 0≤l) {v : ℝ}
    (hv : v∈Icc (l:ℝ) (h:ℝ)) (p : List ℤ) :
    |gaussianPolynomial b p v|/d≤(gaussianUnits b l h p d:ℝ)/10^30 := by
  have dn : (0:ℝ)≤d := by exact_mod_cast hd.le
  apply (div_le_div_of_nonneg_right (gaussian_value_bound hb hl hv p) dn).trans
  apply (le_div_iff₀ (by positivity)).mpr
  have h := (Rat.cast_le (K:=ℝ)).mpr (Nat.le_ceil (10^30*gaussianSum b l h 0 p/d))
  unfold gaussianUnits
  push_cast at h
  convert h using 1; ring

end CentralUnimodality.PolynomialTrial
