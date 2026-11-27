module

public import CentralUnimodality.SaddleRank
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Early first hits and paths that survive a cut and hit later, under the
same change of rank parameter used in strict-partition first differences. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- The rank-normalizer ratio at a test rank j, including its exponential shift. -/
noncomputable def rankChange (c z j : ℝ) (m : ℕ) :=
  (rankNormalizer (c+z) m/rankNormalizer c m)*exp (2*z*j)

theorem rankChange_pos (c z j : ℝ) (m : ℕ) : 0 < rankChange c z j m :=
  mul_pos (div_pos (rankNormalizer_pos ..) (rankNormalizer_pos ..)) (exp_pos _)

/-- Removing a constant height slope from a single word. This preserves any
additional endpoint or survival restriction when summing weights. -/
theorem prefix_height_shift (c u b : ℝ) {t : ℕ} {w : List Bool} (hw : w ∈ words t) : signMass c u w*exp (-b*displacement w) =
    (coshProduct c (u-b) t/coshProduct c u t)*signMass c (u-b) w := by
  have h₁ := signMass_density c u w
  have h₂ := signMass_density c (u-b) w
  rw [mem_words.mp hw] at h₁ h₂
  have he : exp ((u-c*t)*displacement w+c*walkArea w)*exp (-b*displacement w) =
      exp ((u-b-c*t)*displacement w+c*walkArea w) := by rw [← exp_add]; congr 1; ring
  rw [← h₁,← h₂] at he
  apply (mul_right_cancel₀ (mul_pos (by positivity : (0:ℝ) < 2^t) (coshProduct_pos c u t)).ne')
  calc
    _ = (signMass c u w * (2^t*coshProduct c u t))*exp (-b*displacement w) := by ring
    _ = _ := he
    _ = _ := by field_simp [(coshProduct_pos c u t).ne']

/-- Exact exponential moment of the endpoint of a tilted independent prefix. -/
theorem height_laplace (c u b : ℝ) (t : ℕ) :
    (∑ w ∈ words t, signMass c u w*exp (-b*displacement w)) =
      coshProduct c (u-b) t/coshProduct c u t := by
  rw [Finset.sum_congr rfl (fun _ hw => prefix_height_shift c u b hw),← Finset.mul_sum,signMass_total,mul_one]

/-- The normalization on a hit at time 2d+1, with E[rank] = j. -/
theorem first_hit_change_bound {m d : ℕ} (ht : 2*d+1 ≤ m) {c z : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) :
    rankChange c z (meanRank c m) m *
      (∑ w ∈ (words m).filter (fun w => w.take (2*d+1) ∈ hitWords 1 (2*d+1)),
        signMass (c+z) ((c+z)*m) w) ≤
      exp (z^2*labelSquares m/2-(2*(d:ℝ)+1)*((m:ℝ)-d)^2*(c+z)*(c*(1-2*(c*m)^2/3)+z)/2) *
        ∑ w ∈ hitWords 1 (2*d+1), signMass (c+z) ((c+z)*d) w := by
  let b := (c+z)*((m:ℝ)-d)
  have hb : 0 ≤ b := mul_nonneg (add_nonneg hc hz) (sub_nonneg.mpr (by exact_mod_cast (show d ≤ m by omega)))
  rw [mass_prefix (c+z) _ ht (hitWords 1 (2*d+1)) (Finset.filter_subset ..),
    recenter_first_hit (c+z) ((c+z)*m) ((c+z)*d)]
  change _ ≤ _ * _
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => (signMass_pos ..).le))
  apply le_trans _ (centered_joint_cost ht hc hz)
  have hr : (c+z)*m-b = (c+z)*d := by dsimp [b]; ring
  have hg : exp ((c+z)*d-(c+z)*m) ≤ 1 := exp_le_one_iff.mpr (by dsimp [b] at hb; linarith only [hb])
  change rankChange _ _ _ _ * _ ≤ rankChange _ _ _ _ * (coshProduct (c+z) ((c+z)*m-b) _/_)
  rw [hr]
  apply mul_le_mul_of_nonneg_left _ (rankChange_pos ..).le
  apply div_le_div_of_nonneg_right _ (coshProduct_pos ..).le
  exact (mul_le_mul_of_nonneg_right hg (coshProduct_pos ..).le).trans_eq (one_mul _)

private theorem biased_laplace {u b : ℝ} (hu : 0 ≤ u) (hb : 0 ≤ b) :
    exp u/(2*cosh u)*exp (-b) + exp (-u)/(2*cosh u)*exp b ≤ exp (b^2/2) := by
  have he : exp u/(2*cosh u)*exp (-b) + exp (-u)/(2*cosh u)*exp b = cosh (u-b)/cosh u := by
    rw [cosh_eq (u-b),show -(u-b) = -u+b by ring,exp_add,exp_sub,exp_neg b]
    field_simp [(cosh_pos _).ne']
  rw [he,← log_le_iff_le_exp (div_pos (cosh_pos _) (cosh_pos _)),log_div (cosh_pos _).ne' (cosh_pos _).ne']
  have h := log_cosh_shift u (-b)
  have hpos : 0 ≤ tanh u := by rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hu) (cosh_pos _).le
  rw [← sub_eq_add_neg] at h
  nlinarith only [h,mul_nonneg hb hpos]

/-- Probability of crossing below zero in the remaining n steps from height h. -/
noncomputable def ruin (c : ℝ) (n h : ℕ) :=
  ∑ w ∈ words n, if BallotFrom h w then 0 else signMass c (c*n) w

/-- Finite-horizon bound for ruin from height h under the actual nonnegative
rank drifts. The exponential factor includes the last step to height -1. -/
theorem suffix_ruin {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) (n h : ℕ) :
    ruin c n h ≤ exp (-b*(h+1)+n*b^2/2) := by
  induction n generalizing h with
  | zero => simp [ruin,words,BallotFrom,(exp_pos _).le]
  | succ n ih =>
    let u := c*((n:ℝ)+1)
    let q := exp u/(2*cosh u)
    let p := exp (-u)/(2*cosh u)
    have hq : 0 ≤ q := (div_pos (exp_pos _) (mul_pos (by norm_num) (cosh_pos _))).le
    have hp : 0 ≤ p := (div_pos (exp_pos _) (mul_pos (by norm_num) (cosh_pos _))).le
    have hu : u-c=c*n := by dsimp [u]; ring
    have step (a : Bool) (w : List Bool) :
        signMass c (c*(n+1:ℕ)) (a::w) = (if a then p else q)*signMass c (c*n) w := by
      cases a <;> simp [signMass,Nat.cast_succ,← show u = c*((n:ℝ)+1) from rfl,hu,p,q,CentralUnimodality.step]
    have he : ruin c (n+1) h = q*ruin c n (h+1) + p*(if h=0 then 1 else ruin c n (h-1)) := by
      rw [ruin,sum_cons_words]
      simp only [step,Bool.false_eq_true,ite_false,ite_true,BallotFrom]
      congr 1
      · rw [ruin,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        split <;> simp_all
      · by_cases hh : h=0
        · simp [hh,← Finset.mul_sum,signMass_total]
        · simp only [show 0<h by omega,true_and,ite_eq_right hh,ruin,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          split <;> simp_all
    rw [he]
    let x := -b*((h:ℝ)+1)+(n:ℝ)*b^2/2
    have D : (if h=0 then (1:ℝ) else ruin c n (h-1)) ≤ exp (x+b) := by
      by_cases hh : h=0
      · simp only [ite_eq_left hh]
        apply one_le_exp
        dsimp [x]; rw [hh,Nat.cast_zero]
        nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg b)]
      · rw [ite_eq_right hh]
        apply (ih (h-1)).trans_eq
        congr 1; dsimp [x]; rw [Nat.cast_sub (by omega : 1 ≤ h),Nat.cast_one]; ring
    have U : ruin c n (h+1) ≤ exp (x-b) := by
      apply (ih (h+1)).trans_eq
      congr 1; dsimp [x]; push_cast; ring
    apply (add_le_add (mul_le_mul_of_nonneg_left U hq) (mul_le_mul_of_nonneg_left D hp)).trans
    have cost := mul_le_mul_of_nonneg_left (biased_laplace (u := u) (by dsimp [u]; positivity) hb) (exp_pos x).le
    rw [show -b*((h:ℝ)+1)+(n+1:ℕ)*b^2/2 = x+b^2/2 by dsimp [x]; push_cast; ring,
      show x-b=x+-b by ring, exp_add x (-b), exp_add x b, exp_add x (b^2/2)]
    dsimp only [p,q]
    linarith only [cost]

/-- Surviving through step t and crossing below zero strictly later. -/
noncomputable def lateHitMass (v : ℝ) (m t : ℕ) :=
  ∑ w ∈ (words m).filter (fun w => w.take t ∈ ballots t),
    if BallotFrom 0 w then 0 else signMass v (v*m) w

private theorem ballot_append_from {v : List Bool} (hv : BallotFrom 0 v) (w : List Bool) :
    BallotFrom 0 (v++w) ↔ BallotFrom (displacement v).toNat w := by
  have h := (ballot_iff_heights 0 v).mp hv
  simp only [ballot_iff_heights,Nat.cast_zero,heights_append,zero_add,List.forall_mem_append,
    Int.toNat_of_nonneg (ballot_endpoint_nonneg hv)] at h ⊢
  exact and_iff_right h

private theorem late_prefix_bound {m t : ℕ} (ht : t ≤ m) {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) :
    lateHitMass v m t ≤ (coshProduct v (v*m-b) t / coshProduct v (v*m) t) *
      exp ((m-t:ℕ)*b^2/2) := by
  let N := exp ((m-t:ℕ)*b^2/2)
  let weight := fun w => signMass v (v*m) w * exp (-b*displacement w)
  rw [lateHitMass,prefix_sum ht (ballots t) (Finset.filter_subset ..)]
  calc
    _ ≤ ∑ a ∈ ballots t, weight a * N := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨hlen,hball⟩ := mem_ballots.mp ha
      have harg : v*m-v*a.length = v*(m-t:ℕ) := by rw [hlen,Nat.cast_sub ht]; ring
      have he : (∑ w ∈ words (m-t), if BallotFrom 0 (a++w) then 0 else signMass v (v*m) (a++w)) =
          signMass v (v*m) a * ruin v (m-t) (displacement a).toNat := by
        rw [ruin,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        simp only [ballot_append_from hball,append_mass,harg,mul_ite,mul_zero]
      rw [he]
      dsimp only [weight]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (signMass_pos ..).le
      apply (suffix_ruin hv hb (m-t) (displacement a).toNat).trans
      rw [← exp_add]
      apply exp_le_exp.mpr
      rw [← Int.cast_natCast,Int.toNat_of_nonneg (ballot_endpoint_nonneg hball)]
      linarith
    _ ≤ ∑ w ∈ words t, weight w * N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
      intro w _ _
      exact mul_nonneg (mul_nonneg (signMass_pos ..).le (exp_pos _).le) (exp_pos _).le
    _ = _ := by rw [← Finset.sum_mul]; dsimp only [weight,N]; rw [height_laplace]

/-- Late-hit estimate for the actual ballot event under the simultaneous rank tilt.
The test height slope b may be rounded down to a rational grid. -/
theorem late_hit_change_bound {m t : ℕ} (hm : 0 < m) (ht : t ≤ m) {c z b : ℝ}
    (hc : 0 ≤ c) (hz : 0 ≤ z) (hb : 0 ≤ b)
    (hcut : b*m ≤ (tanh (c*m)/m+z)*prefixLabels m t) :
    rankChange c z (meanRank c m) m * lateHitMass (c+z) m t ≤
      exp (z^2*labelSquares m/2-m*b^2/2) := by
  have h := mul_le_mul_of_nonneg_left (late_prefix_bound ht (add_nonneg hc hz) hb)
    (rankChange_pos c z (meanRank c m) m).le
  rw [← mul_assoc] at h
  apply h.trans
  change jointCost c z b m t * _ ≤ _
  apply (mul_le_mul_of_nonneg_right (joint_cost_bound hm ht hc hb z) (exp_pos _).le).trans
  rw [← exp_add,Nat.cast_sub ht,exp_le_exp]
  nlinarith only [mul_le_mul_of_nonneg_left hcut hb]

end CentralUnimodality.MarkedExcursion
