module

public import CentralUnimodality.MarkedHitBound

/-! Connect tilted ballot and first-hit masses to the literal rank counts.
Here c is half the coefficient of the rank in the Boltzmann factor. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion

open Real

noncomputable def rankNormalizer (c : ℝ) (m : ℕ) :=
  ∏ i ∈ Finset.range m, (1+exp (-2*c*(i+1)))

theorem rankNormalizer_pos (c : ℝ) (m : ℕ) : 0 < rankNormalizer c m :=
  Finset.prod_pos (fun _ _ => by positivity)

private theorem one_step (x : ℝ) (b : Bool) :
    exp (x*step b)/(2*cosh x) * (1+exp (-2*x)) = if b then exp (-2*x) else 1 := by
  have h : exp x * exp (-2*x) = exp (-x) := by rw [← exp_add]; congr 1; ring
  have hn : 2*cosh x = exp x*(1+exp (-2*x)) := by rw [cosh_eq,mul_add,h]; ring
  rw [hn]
  cases b <;> simp only [step,Int.cast_neg,Int.cast_one,mul_one,mul_neg,ite_false,ite_true,Bool.false_eq_true]
  · field_simp
  · rw [← h]; field_simp

theorem signMass_rank (c : ℝ) (w : List Bool) :
    signMass c (c*w.length) w * rankNormalizer c w.length = exp (-2*c*(wordParts w).sum) := by
  induction w with
  | nil => simp [signMass,rankNormalizer,wordParts]
  | cons b w ih =>
    rw [signMass,List.length_cons,Nat.cast_succ,show c*(w.length+1)-c = c*w.length by ring]
    rw [rankNormalizer,Finset.prod_range_succ]
    let x := c*(w.length+1)
    change (exp (x*step b)/(2*cosh x)*signMass c (c*w.length) w) *
      (rankNormalizer c w.length*(1+exp (-2*c*(w.length+1)))) = _
    have he : -2*c*((w.length:ℝ)+1) = -2*x := by dsimp [x]; ring
    rw [he,mul_mul_mul_comm,show exp (x*step b)/(2*cosh x) * rankNormalizer c w.length *
        (signMass c (c*w.length) w * (1+exp (-2*x))) =
        (exp (x*step b)/(2*cosh x)*(1+exp (-2*x))) *
        (signMass c (c*w.length) w*rankNormalizer c w.length) by ring,one_step,ih]
    cases b with
    | false => simp [wordParts]
    | true =>
      simp only [ite_true,wordParts,List.sum_append,List.sum_singleton,Nat.cast_add,Nat.cast_one]
      rw [← exp_add]; congr 1; dsimp [x]; ring

/-- Probability of rank j jointly with a specified set of length-m walks.
The set may impose survival or an additional condition on first-hit time. -/
noncomputable def rankEvent (c : ℝ) (m j : ℕ) (A : Finset (List Bool)) : ℝ :=
  ∑ w ∈ A.filter (fun w => (wordParts w).sum = j), signMass c (c*m) w

theorem rankEvent_exact (c : ℝ) {m : ℕ} (j : ℕ) (A : Finset (List Bool)) (hA : A ⊆ words m) :
    rankEvent c m j A * rankNormalizer c m =
      (A.filter (fun w => (wordParts w).sum = j)).card * exp (-2*c*j) := by
  rw [rankEvent,Finset.sum_mul,← nsmul_eq_mul,← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro w hw
  obtain ⟨ha,hr⟩ := Finset.mem_filter.mp hw
  simpa only [mem_words.mp (hA ha),hr] using signMass_rank c w

theorem ballot_rank_mass (c : ℝ) (m j : ℕ) :
    rankEvent c m j (ballots m) * rankNormalizer c m = rankCount m j * exp (-2*c*j) := by
  rw [rankEvent_exact c j (ballots m) (Finset.filter_subset ..),rankCount_eq_card]
  congr 2
  apply Finset.card_bij' (fun w _ => wordParts w) (fun l _ => wordOfParts m l)
  · intro w hw
    obtain ⟨hw,hs⟩ := Finset.mem_filter.mp hw
    obtain ⟨hl,hb⟩ := mem_ballots.mp hw
    exact Finset.mem_filter.mpr ⟨mem_allPartitions.mpr (by simpa [hl] using (ballot_iff_fits 0 w).mp hb),hs⟩
  · intro l hl
    obtain ⟨hl,hs⟩ := Finset.mem_filter.mp hl
    have hf := mem_allPartitions.mp hl
    exact Finset.mem_filter.mpr ⟨mem_ballots.mpr ((ballotEquiv m).symm ⟨l,hf⟩).property,
      by rwa [wordParts_wordOfParts hf]⟩
  · intro w hw
    rw [← (mem_ballots.mp (Finset.mem_filter.mp hw).1).1,wordOfParts_wordParts]
  · intro l hl
    exact wordParts_wordOfParts (mem_allPartitions.mp (Finset.mem_filter.mp hl).1)

/-- The first-difference sign tested on the tilted probabilities is
equivalent to strict growth of the original integer staircase ranks. -/
theorem rank_step_iff (c : ℝ) (m j : ℕ) : rankCount m j < rankCount m (j+1) ↔
    exp (-2*c)*rankEvent c m j (ballots m) < rankEvent c m (j+1) (ballots m) := by
  rw [← mul_lt_mul_iff_left₀ (rankNormalizer_pos c m),mul_assoc,ballot_rank_mass,ballot_rank_mass]
  have h : -2*c*((j+1:ℕ):ℝ) = -2*c+-2*c*j := by push_cast; ring
  rw [h,exp_add,← mul_assoc,mul_comm (exp (-2*c)) _,mul_assoc]
  rw [mul_lt_mul_iff_left₀ (mul_pos (exp_pos _) (exp_pos _)),Nat.cast_lt]

/-- Change of rank tilt on an arbitrary fixed event, before taking first
or second differences at neighboring ranks. -/
theorem change_rank_tilt (c v : ℝ) {m : ℕ} (j : ℕ) (A : Finset (List Bool)) (hA : A ⊆ words m) :
    rankEvent c m j A =
      (rankNormalizer v m/rankNormalizer c m) * exp (2*(v-c)*j) * rankEvent v m j A := by
  apply mul_right_cancel₀ (rankNormalizer_pos c m).ne'
  rw [rankEvent_exact c j A hA]
  have he := rankEvent_exact v j A hA
  have hx : exp (-2*c*j) = exp (2*(v-c)*j)*exp (-2*v*j) := by
    rw [← exp_add]; congr 1; ring
  rw [hx,← mul_left_comm,← he]
  field_simp [(rankNormalizer_pos c m).ne']

private theorem coshProduct_pos (c u : ℝ) (t : ℕ) : 0 < coshProduct c u t :=
  Finset.prod_pos (fun _ _ => cosh_pos _)

/-- Removing a constant from every prefix parameter on a hit contributes
one exponential factor because every first-hit path ends at height -1. -/
theorem recenter_first_hit (c u v : ℝ) (t : ℕ) :
    (∑ w ∈ hitWords 1 t, signMass c u w) =
      (exp (v-u)*coshProduct c v t/coshProduct c u t) *
        ∑ w ∈ hitWords 1 t, signMass c v w := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  obtain ⟨hw,_,hz,_⟩ := Finset.mem_filter.mp hw
  have hl := mem_words.mp hw
  have hd : displacement w = -1 := by change (1:ℤ)+displacement w = 0 at hz; omega
  have h₁ := signMass_density c u w
  have h₂ := signMass_density c v w
  rw [hl,hd] at h₁ h₂
  have he : exp ((u-c*t)*((-1:ℤ):ℝ)+c*walkArea w) =
      exp (v-u)*exp ((v-c*t)*((-1:ℤ):ℝ)+c*walkArea w) := by
    rw [← exp_add]; congr 1; push_cast; ring
  rw [he,← h₂] at h₁
  apply (mul_right_cancel₀ (show (2:ℝ)^t*coshProduct c u t ≠ 0 from
    (mul_pos (by positivity) (coshProduct_pos ..)).ne'))
  rw [h₁]; field_simp [(coshProduct_pos c u t).ne']

private theorem append_mass (c u : ℝ) (v w : List Bool) :
    signMass c u (v++w) = signMass c u v * signMass c (u-c*v.length) w := by
  induction v generalizing u with
  | nil => simp [signMass]
  | cons b v ih =>
    simp only [List.cons_append,signMass,List.length_cons,Nat.cast_add,Nat.cast_one,ih,mul_assoc]
    rw [show u-c*(v.length+1) = u-c-c*v.length by ring]

/-- Summing over the independent suffix recovers the probability of the
prefix event under the same tilted law. -/
theorem mass_prefix (c u : ℝ) {m t : ℕ} (ht : t ≤ m) (A : Finset (List Bool)) (hA : A ⊆ words t) :
    (∑ w ∈ (words m).filter (fun w => w.take t ∈ A), signMass c u w) = ∑ v ∈ A, signMass c u v := by
  let pairs := A ×ˢ words (m-t)
  let join := fun p : List Bool × List Bool => p.1++p.2
  have parts (p : List Bool × List Bool) (hp : p ∈ pairs) :
      (join p).take t = p.1 ∧ (join p).drop t = p.2 := by
    have h := mem_words.mp (hA (Finset.mem_product.mp hp).1)
    simp [join,← h]
  have he : (words m).filter (fun w => w.take t ∈ A) = pairs.image join := by
    ext w
    constructor
    · intro hw
      obtain ⟨hw,ha⟩ := Finset.mem_filter.mp hw
      have hl := mem_words.mp hw
      exact Finset.mem_image.mpr ⟨(w.take t,w.drop t),Finset.mem_product.mpr
        ⟨ha,mem_words.mpr (by simp [hl])⟩,List.take_append_drop ..⟩
    · intro hw
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
      have hl := mem_words.mp (hA ha)
      have hr := mem_words.mp hb
      exact Finset.mem_filter.mpr ⟨mem_words.mpr (by simp [join,hl,hr]; omega),(parts p hp).1 ▸ ha⟩
  have inj : Set.InjOn join (pairs : Set _) := by
    intro p hp q hq hj
    exact Prod.ext ((parts p hp).1.symm.trans ((congrArg (List.take t) hj).trans (parts q hq).1))
      ((parts p hp).2.symm.trans ((congrArg (List.drop t) hj).trans (parts q hq).2))
  rw [he,Finset.sum_image inj,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro v _
  simp only [join,append_mass,← Finset.mul_sum,signMass_total,mul_one]

/-- The individual first-hit estimate in a full length-m rank tilt.
Its left-hand side sums the probabilities of the actual words that first
hit the forbidden height at time 2d+1. -/
theorem rank_prefix_hit_bound (m d : ℕ) (ht : 2*d+1 ≤ m) {c : ℝ} (hc : 0 ≤ c) :
    let t := 2*d+1
    let y := c*(2*(d:ℝ)+1)*√((d:ℝ)+1)
    let L := c^2*d*(d+1)*(2*d+1)/6*(1-(c*d)^2/6)
    (∑ w ∈ (words m).filter (fun w => w.take t ∈ hitWords 1 t), signMass c (c*m) w) ≤
      (exp (c*d-c*m)*coshProduct c (c*d) t/coshProduct c (c*m) t) *
      ((survival d/(2*(d+1))) * exp (c*d+y^2/4-L) * (1+y/2*(√π+min (√π) y))) := by
  dsimp only
  rw [mass_prefix c (c*m) ht (hitWords 1 (2*d+1)) (Finset.filter_subset ..),recenter_first_hit c (c*m) (c*d)]
  exact mul_le_mul_of_nonneg_left (tilted_hit_gaussian d hc)
    (div_nonneg (mul_nonneg (exp_pos _).le (coshProduct_pos ..).le) (coshProduct_pos ..).le)

end CentralUnimodality.MarkedExcursion
