module

public import CentralUnimodality.TiltedPrefixSurvival
import CentralUnimodality.EndpointTransforms

/-! A centered square martingale on the actual descending rank labels.
Stopping at the first negative vertex charges at most the unrestricted
prefix variance at each discarded hit. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- The rank contributed by a prefix with successive labels r,r-1,... . -/
def prefixRank (r : ℝ) : List Bool → ℝ
  | [] => 0
  | b::w => (if b then r else 0) + prefixRank (r-1) w

theorem prefixRank_full (w : List Bool) : prefixRank w.length w = (wordParts w).sum := by
  induction w with
  | nil => simp [prefixRank,wordParts]
  | cons b w ih => cases b <;> simp [prefixRank,wordParts,ih,add_comm]

theorem prefixRank_append (r : ℝ) (v w : List Bool) :
    prefixRank r (v++w) = prefixRank r v+prefixRank (r-v.length) w := by
  induction v generalizing r with
  | nil => simp [prefixRank]
  | cons b v ih =>
    simp only [List.cons_append,prefixRank,ih,List.length_cons,Nat.cast_succ]
    rw [show r-1-v.length=r-(v.length+1) by ring,add_assoc]

private theorem prefixRank_snoc (r : ℝ) (w : List Bool) (b : Bool) :
    prefixRank r (w++[b]) = prefixRank r w + (if b then r-w.length else 0) := by
  induction w generalizing r with
  | nil => simp [prefixRank]
  | cons v w ih =>
    simp only [List.cons_append,prefixRank,ih,List.length_cons,Nat.cast_succ]
    rw [show r-1-w.length=r-(w.length+1) by ring,add_assoc]

noncomputable def prefixMean (c u r : ℝ) (t : ℕ) :=
  ∑ i ∈ Finset.range t, (r-i)*upChance (-(u-c*i))

noncomputable def prefixVariance (c u r : ℝ) (t : ℕ) :=
  ∑ i ∈ Finset.range t, (r-i)^2 * upChance (u-c*i) * upChance (-(u-c*i))

/-- The centered rank of this word uses the unrestricted mean. -/
noncomputable def centeredRank (c u r : ℝ) (w : List Bool) := prefixRank r w-prefixMean c u r w.length

private theorem centered_snoc (c u r : ℝ) (w : List Bool) (b : Bool) :
    centeredRank c u r (w++[b]) = centeredRank c u r w +
      (r-w.length)*((if b then 1 else 0)-upChance (-(u-c*w.length))) := by
  simp only [centeredRank,prefixRank_snoc,List.length_append,List.length_singleton,prefixMean,Finset.sum_range_succ]
  cases b <;> simp <;> ring

private theorem mass_snoc (c u : ℝ) (w : List Bool) (b : Bool) : signMass c u (w++[b]) =
    signMass c u w * (if b then upChance (-(u-c*w.length)) else upChance (u-c*w.length)) := by
  cases b
  · simp [append_mass,signMass,step,upChance]
  · simp only [append_mass,signMass,step,Int.cast_neg,Int.cast_one,mul_neg,mul_one,ite_true,upChance,cosh_neg]

/-- The centered square minus its unrestricted variance, weighted by the
word probability. Its sum over the two children is its value at the parent. -/
private noncomputable def squareMass (c u r : ℝ) (w : List Bool) :=
  signMass c u w*((centeredRank c u r w)^2-prefixVariance c u r w.length)

private theorem square_children (c u r : ℝ) (w : List Bool) :
    squareMass c u r (w++[false])+squareMass c u r (w++[true]) = squareMass c u r w := by
  let p := upChance (-(u-c*w.length))
  let q := upChance (u-c*w.length)
  let z := centeredRank c u r w
  let v := prefixVariance c u r w.length
  let M := signMass c u w
  let b := r-w.length
  have hp : q=1-p := by dsimp [p,q]; linarith only [up_total (u-c*w.length)]
  have hvar : prefixVariance c u r (w.length+1) = v+b^2*q*p := by
    rw [prefixVariance,Finset.sum_range_succ]; rfl
  simp only [squareMass,mass_snoc,centered_snoc,List.length_append,List.length_singleton,hvar,Bool.false_eq_true,
    ite_false,ite_true,zero_sub]
  change M*q*((z+b*(-p))^2-(v+b^2*q*p))+M*p*((z+b*(1-p))^2-(v+b^2*q*p)) = M*(z^2-v)
  rw [hp]; ring

private theorem sum_children (F : List Bool → ℝ) (h : ∀ w, F (w++[false])+F (w++[true])=F w)
    (t : ℕ) : ∑ w ∈ words t, F w = F [] := by
  induction t with
  | zero => simp [words]
  | succ t ih => rw [sum_snoc_words,← Finset.sum_add_distrib]; simpa only [h] using ih

theorem prefixMean_exact (c u r : ℝ) (L : ℕ) :
    ∑ w ∈ words L, signMass c u w * prefixRank r w = prefixMean c u r L := by
  let F := fun w => signMass c u w * centeredRank c u r w
  have h (w) : F (w++[false])+F (w++[true])=F w := by
    dsimp only [F]
    rw [mass_snoc,mass_snoc,centered_snoc,centered_snoc]
    simp only [Bool.false_eq_true,ite_false,ite_true,zero_sub]
    rw [show upChance (u-c*w.length)=1-upChance (-(u-c*w.length)) by linarith only [up_total (u-c*w.length)]]
    ring
  have he := sum_children F h L
  have hz : F []=0 := by simp [F,centeredRank,prefixRank,prefixMean]
  have heq (w) (hw : w ∈ words L) : F w=signMass c u w*prefixRank r w - signMass c u w*prefixMean c u r L := by
    simp [F,centeredRank,mem_words.mp hw,mul_sub]
  rw [hz,Finset.sum_congr rfl heq,Finset.sum_sub_distrib,← Finset.sum_mul,signMass_total,one_mul] at he
  exact sub_eq_zero.mp he

theorem prefixVariance_exact (c u r : ℝ) (L : ℕ) :
    ∑ w ∈ words L, signMass c u w*(centeredRank c u r w)^2 = prefixVariance c u r L := by
  have h := sum_children (squareMass c u r) (square_children c u r) L
  have he (w) (hw : w ∈ words L) : squareMass c u r w =
      signMass c u w*(centeredRank c u r w)^2 - signMass c u w*prefixVariance c u r L := by
    rw [squareMass,mem_words.mp hw,mul_sub]
  rw [Finset.sum_congr rfl he,Finset.sum_sub_distrib,← Finset.sum_mul,signMass_total,one_mul] at h
  have hz : squareMass c u r []=0 := by simp [squareMass,centeredRank,prefixRank,prefixMean,prefixVariance]
  exact sub_eq_zero.mp (h.trans hz)

private theorem stopped_square (c u r : ℝ) (L : ℕ) :
    (∑ w ∈ ballots L, squareMass c u r w) +
      (∑ t ∈ Finset.range L, ∑ w ∈ hitWords 1 (t+1), squareMass c u r w) = 0 := by
  induction L with
  | zero => rw [show ballots 0 = {[]} from rfl]; simp [squareMass,centeredRank,prefixMean,prefixRank,prefixVariance]
  | succ L ih =>
    have h := split_live_hit L (squareMass c u r)
    simp_rw [square_children] at h
    rw [Finset.sum_range_succ]
    linarith only [h,ih]

/-- The unnormalized conditional second moment loses at most the variance
at the stopping time for each first-hit word. -/
theorem stopped_variance_bound (c u r : ℝ) (L : ℕ) :
    (∑ w ∈ ballots L, signMass c u w*(centeredRank c u r w)^2) ≤
      live c u L 1 * prefixVariance c u r L +
      ∑ t ∈ Finset.range L, prefixVariance c u r (t+1) * (∑ w ∈ hitWords 1 (t+1), signMass c u w) := by
  have h := stopped_square c u r L
  have he : (∑ w ∈ ballots L, squareMass c u r w) =
      (∑ w ∈ ballots L, signMass c u w*(centeredRank c u r w)^2) - live c u L 1 * prefixVariance c u r L := by
    rw [live_ballots,Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    rw [squareMass,(mem_ballots.mp hw).1,mul_sub]
  have hh (t : ℕ) : -(prefixVariance c u r (t+1) * ∑ w ∈ hitWords 1 (t+1), signMass c u w) ≤
      ∑ w ∈ hitWords 1 (t+1), squareMass c u r w := by
    rw [Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro w hw
    have hl := mem_words.mp (Finset.mem_filter.mp hw).1
    rw [squareMass,hl]
    nlinarith only [mul_nonneg (signMass_pos c u w).le (sq_nonneg (centeredRank c u r w))]
  have H := Finset.sum_le_sum (s := Finset.range L) (fun t _ => hh t)
  rw [Finset.sum_neg_distrib] at H
  linarith only [he,h,H]

theorem prefixVariance_le {m t : ℕ} (ht : t ≤ m) (c u : ℝ) :
    prefixVariance c u m t ≤ t*(m:ℝ)^2/4 := by
  calc
    _ ≤ ∑ _i ∈ Finset.range t, ((m:ℝ)^2/4) := by
      apply Finset.sum_le_sum
      intro i hi
      have hil : (i:ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.mp hi).le.trans ht
      let p := upChance (u-c*i)
      let q := upChance (-(u-c*i))
      have he : p+q=1 := up_total _
      have hpq : p*q ≤ 1/4 := by nlinarith only [sq_nonneg (p-q),congrArg (fun x : ℝ => x^2) he]
      have hb : ((m:ℝ)-i)^2 ≤ (m:ℝ)^2 :=
        pow_le_pow_left₀ (sub_nonneg.mpr hil) (by simp) 2
      change ((m:ℝ)-i)^2 * p*q ≤ _
      nlinarith only [hb,mul_le_mul_of_nonneg_left hpq (sq_nonneg ((m:ℝ)-i))]
    _ = _ := by simp; ring

theorem prefix_second_moment {m L : ℕ} (hL : L ≤ m) {c u v : ℝ} (hc : 0 ≤ c) (hu : 0 < tanh u)
    (hv : ∀ i < L, v ≤ u-c*i) :
    (∑ w ∈ ballots L, signMass c u w*(centeredRank c u m w)^2) ≤
      (m:ℝ)^2/4*(live c u L 1*L + (L*(exp (-2*v)-exp (-2*u))+exp (-2*u)/tanh u)) := by
  let A := (m:ℝ)^2/4
  let H := fun t => ∑ w ∈ hitWords 1 (t+1), signMass c u w
  have h₁ := mul_le_mul_of_nonneg_left (prefixVariance_le hL c u) (live_nonneg c u L 1)
  have h₂ (t) (ht : t ∈ Finset.range L) : prefixVariance c u m (t+1)*H t ≤ A*((t+1)*H t) := by
    have ht' : t+1 ≤ m := (Finset.mem_range.mp ht).trans_le hL
    have h := mul_le_mul_of_nonneg_right (prefixVariance_le ht' c u)
      (show 0 ≤ H t from Finset.sum_nonneg (fun _ _ => (signMass_pos ..).le))
    push_cast at h
    dsimp [A]; linarith only [h]
  have hsum := Finset.sum_le_sum h₂
  rw [← Finset.mul_sum] at hsum
  have hhit := mul_le_mul_of_nonneg_left (hit_time_first_moment hc hu L hv) (show 0 ≤ A by positivity)
  dsimp only [A,H] at hsum hhit
  linarith only [stopped_variance_bound c u m L,h₁,hsum,hhit]

end CentralUnimodality.MarkedExcursion
