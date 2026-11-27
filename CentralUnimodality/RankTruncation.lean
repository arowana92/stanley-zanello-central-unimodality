module

public import CentralUnimodality.TruncatedInversion
public import CentralUnimodality.GridAliasReserve
public import Mathlib.Algebra.BigOperators.Field

/-! The retained discrete inverse approximates differences of the true
strict-partition rank probabilities, with both types of error included. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def rankProbability (n δ j : ℕ) : ℂ :=
  (rankCount (2*n+δ) j:ℂ)/((2*n+δ).choose n:ℂ)

theorem full_reconstruction {n δ Q j : ℕ} (hδ : δ ≤ 1) (hQ : 0 < Q) (hj : j ≤ n*(n+δ)) :
    gridReconstruction n δ Q (Finset.range Q) j = (periodicCount n δ Q j:ℂ)/((2*n+δ).choose n:ℂ) := by
  let m := 2*n+δ
  have hg (t : ℕ) : gridFrequency Q t/2 = halfGrid Q t := by dsimp [gridFrequency,halfGrid]; ring
  have h := inverse_periodicCount n δ hδ hQ hj
  have hs := ballot_survival m
  have hmid : m/2 = n := by dsimp [m]; omega
  rw [hmid] at hs
  have hs' : (survival ((m+1)/2):ℂ) = (m.choose n:ℂ)/2^m := by
    simpa using congrArg (fun x : ℝ => (x:ℂ)) hs.symm
  simp only [gridReconstruction,siteFourierTerm,hg,← Finset.sum_div]
  rw [siteInverse] at h
  change _ = (2:ℂ)⁻¹^(m+1)*(periodicCount n δ Q j:ℂ) at h
  let Z := ∑ t ∈ Finset.range Q, areaCharacter (halfGrid Q t) (-signedAreaAtRank n δ j) *
    PowerSeries.coeff (m+1) (fairSeries (areaCharacter (halfGrid Q t)) strictWords)
  calc
    _ = (2/(survival ((m+1)/2):ℂ))*(Z/(Q:ℂ)) := by dsimp [Z,m]; ring
    _ = _ := by rw [h,hs',pow_succ,inv_pow]; field_simp; rfl

private theorem site_error {n δ Q j r : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ)
    (hmax : n+δ ≤ 300000) (hr : r ≤ 2) (hj : j ≤ n*(n+δ))
    (hQ : 5*Witness.cellScale (n+δ) ≤ Q)
    (hx : ((n*(n+δ)-j:ℕ):ℝ)+(3*n+2*δ+1)/2 ≤ 0.63*Witness.cellScale (n+δ)) :
    ‖gridReconstruction n δ Q (Finset.range Q) j-rankProbability n δ j‖ ≤
      (1/10^12)/(2*Witness.cellScale (n+δ))^(r+1) := by
  let S := Witness.cellScale (n+δ)
  have hS : 0 < S := Witness.cellScale_pos (by omega)
  have hq : 0 < (Q:ℝ) := lt_of_lt_of_le (by positivity : 0 < 5*S) hQ
  have hcut : 2*(n*(n+δ)-j)+(3*n+2*δ+1) < Q := by
    change _ ≤ 0.63*S at hx
    change 5*S ≤ _ at hQ
    exact_mod_cast (show 2*((n*(n+δ)-j:ℕ):ℝ)+(3*n+2*δ+1) < Q by linarith only [hx,hQ,hS])
  have hle := (periodicCount_bounds hj hcut).1
  have hnon : 0 ≤ (periodicCount n δ Q j:ℝ)-(rankCount (2*n+δ) j:ℝ) := sub_nonneg.mpr (by exact_mod_cast hle)
  rw [full_reconstruction hδ (by exact_mod_cast hq) hj,rankProbability,← sub_div,norm_div]
  rw [← Complex.ofReal_natCast,← Complex.ofReal_natCast,← Complex.ofReal_sub,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hnon,Complex.norm_natCast]
  apply (le_div_iff₀ (by positivity : 0 < (2*S)^(r+1))).mpr
  rw [mul_comm]
  exact (grid_alias_reserve hδ hn hmax hr hj hQ hx).le

private theorem local_difference_error (F G : ℕ → ℂ) (j r : ℕ) (e : ℝ)
    (h : ∀ u ≤ r, ‖F (j+u)-G (j+u)‖ ≤ e) :
    ‖(fwdDiff 1)^[r] F j-(fwdDiff 1)^[r] G j‖ ≤ 2^r*e := by
  induction r generalizing j with
  | zero => simpa using h 0 (by decide)
  | succ r ih =>
    have h₀ := ih j (fun u hu => h u (by omega))
    have h₁ := ih (j+1) (fun u hu => by simpa [Nat.add_assoc,Nat.add_comm 1 u] using h (u+1) (by omega))
    simp only [Function.iterate_succ_apply',fwdDiff]
    rw [show ∀ a b c d : ℂ, a-b-(c-d) = (a-c)-(b-d) by intros; ring]
    apply (norm_sub_le ..).trans
    rw [pow_succ]
    linarith only [h₁,h₀]

private theorem alias_difference {n δ Q j r : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ)
    (hmax : n+δ ≤ 300000) (hr : r ≤ 2) (hj : j+r ≤ n*(n+δ))
    (hQ : 5*Witness.cellScale (n+δ) ≤ Q)
    (hx : ((n*(n+δ)-j:ℕ):ℝ)+(3*n+2*δ+1)/2 ≤ 0.63*Witness.cellScale (n+δ)) :
    Witness.cellScale (n+δ)^(r+1) *
      ‖(fwdDiff 1)^[r] (gridReconstruction n δ Q (Finset.range Q)) j -
        (fwdDiff 1)^[r] (rankProbability n δ) j‖ ≤ 1/10^12 := by
  let S := Witness.cellScale (n+δ)
  have hS : 0 < S := Witness.cellScale_pos (by omega)
  apply (mul_le_mul_of_nonneg_left (local_difference_error _ _ j r ((1/10^12)/(2*S)^(r+1)) ?_) (by positivity)).trans
  · change S^(r+1)*(2^r*((1/10^12)/(2*S)^(r+1))) ≤ _
    calc
      _ = (1/10^12:ℝ)/2 := by rw [mul_pow,pow_succ (2:ℝ)]; field_simp
      _ ≤ _ := by norm_num
  · intro u hu
    apply site_error hδ hn hmax hr (by omega) hQ
    have he : n*(n+δ)-(j+u) ≤ n*(n+δ)-j := Nat.sub_le_sub_left (by omega) _
    have hc : ((n*(n+δ)-(j+u):ℕ):ℝ) ≤ ((n*(n+δ)-j:ℕ):ℝ) := by exact_mod_cast he
    linarith only [hc,hx]

/-- The error budgets from the finite-window proof, for both orders at
once. The unaliased target is the conditional rank count of the staircase. -/
theorem rank_truncation_two_orders {n δ Q J j : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ)
    (hmax : n+δ ≤ 300000) (hj : j+2 ≤ n*(n+δ))
    (hQ : 5*Witness.cellScale (n+δ) ≤ Q)
    (hJ : 2048 ≤ (2*Real.pi*Witness.cellScale (n+δ)/Q)*J)
    (hx : ((n*(n+δ)-j:ℕ):ℝ)+(3*n+2*δ+1)/2 ≤ 0.63*Witness.cellScale (n+δ)) :
    let P := rankProbability n δ
    let T := gridReconstruction n δ Q (retainedModes Q J)
    let S := Witness.cellScale (n+δ)
    S^2*‖fwdDiff 1 P j-fwdDiff 1 T j‖ ≤ 0.00026 ∧
    S^3*‖(fwdDiff 1)^[2] P j-(fwdDiff 1)^[2] T j‖ ≤ 0.95 := by
  let F := gridReconstruction n δ Q (Finset.range Q)
  let T := gridReconstruction n δ Q (retainedModes Q J)
  let P := rankProbability n δ
  let S := Witness.cellScale (n+δ)
  have hS : 0 < S := Witness.cellScale_pos (by omega)
  have h (r : ℕ) (hr : r ≤ 2) (e : ℝ) (hT : S^(r+1)*‖(fwdDiff 1)^[r] F j-(fwdDiff 1)^[r] T j‖ ≤ e) :
      S^(r+1)*‖(fwdDiff 1)^[r] P j-(fwdDiff 1)^[r] T j‖ ≤ 1/10^12+e := by
    have hA := alias_difference hδ hn hmax hr (by omega : j+r ≤ _) hQ hx
    have ht := norm_sub_le_norm_sub_add_norm_sub ((fwdDiff 1)^[r] P j) ((fwdDiff 1)^[r] F j) ((fwdDiff 1)^[r] T j)
    rw [norm_sub_rev _ ((fwdDiff 1)^[r] F j)] at ht
    apply (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ S^(r+1))).trans
    rw [mul_add]
    exact add_le_add hA hT
  have hc := truncation_two_orders hδ hn hQ hJ j
  exact ⟨(h 1 (by decide) _ hc.1).trans (by norm_num),(h 2 (by decide) _ hc.2).trans (by norm_num)⟩

end CentralUnimodality
