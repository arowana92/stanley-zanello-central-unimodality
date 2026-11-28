module

public import CentralUnimodality.CubicGaussianMaximum

/-! Rational bounds on each Gaussian monomial over a closed interval.
A bisection in the interior case produces a rational upper cube root. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real Set

def cubeBisect (x : ℚ) : ℕ → ℚ → ℚ → ℚ
  | 0, _, h => h
  | d+1, l, h =>
    let m := (l+h)/2
    if m^3<x then cubeBisect x d m h else cubeBisect x d l m

private theorem cube_bisect_upper (x : ℚ) (d : ℕ) {l h : ℚ} (lo : 0≤l) (hi : l≤h) (cap : x≤h^3) :
    0≤cubeBisect x d l h ∧ x≤(cubeBisect x d l h)^3 := by
  induction d generalizing l h with
  | zero => exact ⟨lo.trans hi,cap⟩
  | succ d ih =>
    by_cases hm : ((l+h)/2)^3<x
    · simpa [cubeBisect,hm] using ih (l:=(l+h)/2) (by linarith) (by linarith) cap
    · simpa [cubeBisect,hm] using ih lo (show l≤(l+h)/2 by linarith) (le_of_not_gt hm)

def cubeUpper (x : ℚ) := cubeBisect x 60 0 (max 1 x)

theorem cube_upper (x : ℚ) : 0≤cubeUpper x ∧ x≤(cubeUpper x)^3 := by
  have one : (1:ℚ)≤max 1 x := le_max_left ..
  apply cube_bisect_upper _ _ (by norm_num) (by linarith)
  apply (le_max_right 1 x).trans
  simpa only [pow_one] using pow_le_pow_right₀ one (by decide : 1≤3)

def gaussianEnvelope (b l h : ℚ) (j : ℕ) : ℚ :=
  if (j:ℚ)*b≤3*l^3 then l^j*scaledNegExp (l^3/b)
  else if 3*h^3≤(j:ℚ)*b then h^j*scaledNegExp (h^3/b)
  else (cubeUpper (b*j/(3*2.71)))^j

private theorem endpoint_gaussian {b l : ℚ} (bp : 0<b) (lp : 0≤l) (j : ℕ) :
    gaussianTerm (b:ℝ) j (l:ℝ)≤((l^j*scaledNegExp (l^3/b):ℚ):ℝ) := by
  have e := scaledNegExp_sound (div_nonneg (pow_nonneg lp 3) bp.le)
  push_cast at e ⊢
  exact mul_le_mul_of_nonneg_left e (pow_nonneg (by exact_mod_cast lp) j)

theorem gaussianEnvelope_sound {b l h : ℚ} (bp : 0<b) (lp : 0≤l) {v : ℝ}
    (hv : v∈Icc (l:ℝ) (h:ℝ)) (j : ℕ) :
    gaussianTerm (b:ℝ) j v≤(gaussianEnvelope b l h j:ℝ) := by
  have br : 0<(b:ℝ) := by exact_mod_cast bp
  have lr : 0≤(l:ℝ) := by exact_mod_cast lp
  have vr := lr.trans hv.1
  have hr : 0≤h := by exact_mod_cast vr.trans hv.2
  unfold gaussianEnvelope
  split
  · next test =>
      apply (gaussian_left br lr hv.1 _).trans (endpoint_gaussian bp lp j)
      exact_mod_cast test
  · next left =>
      split
      · next test =>
          apply (gaussian_right br vr hv.2 _).trans (endpoint_gaussian bp hr j)
          exact_mod_cast test
      · have pos : 0<j := by
          by_contra! hz
          have h0 : j=0 := by omega
          simp only [h0,Nat.cast_zero,zero_mul,not_le] at left
          linarith only [left,pow_nonneg lp 3]
        let root := cubeUpper (b*j/(3*2.71))
        have u := cube_upper (b*j/(3*2.71))
        have root0 : 0≤(root:ℝ) := by exact_mod_cast u.1
        have root3 : (b:ℝ)*j/(3*2.71)≤(root:ℝ)^3 := by
          simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_ofScientific,Rat.cast_pow,root] using
            (Rat.cast_le (K:=ℝ)).mpr u.2
        change gaussianTerm (b:ℝ) j v≤((root^j:ℚ):ℝ)
        rw [Rat.cast_pow]
        apply (pow_le_pow_iff_left₀ (mul_nonneg (pow_nonneg vr j) (exp_nonneg _)) (pow_nonneg root0 j) (by decide : 3≠0)).mp
        apply (gaussian_global_cube br vr pos).trans
        rw [← pow_mul,show j*3=3*j by omega,pow_mul]
        exact pow_le_pow_left₀ (by positivity) root3 j

end CentralUnimodality.PolynomialTrial
