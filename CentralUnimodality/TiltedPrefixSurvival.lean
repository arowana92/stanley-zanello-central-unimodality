module

public import CentralUnimodality.RankTilt
import CentralUnimodality.EndpointTransforms

/-! Survival of a tilted prefix, and the first moment lost at the ballot
boundary. All comparisons are finite-horizon identities on words. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

noncomputable def upChance (u : ℝ) := exp u/(2*cosh u)

private theorem up_pos (u : ℝ) : 0 < upChance u := div_pos (exp_pos _) (mul_pos (by norm_num) (cosh_pos _))

theorem up_total (u : ℝ) : upChance u+upChance (-u)=1 := by
  simp only [upChance,cosh_eq]; field_simp; ring

theorem up_ratio (u : ℝ) : upChance (-u) = upChance u * exp (-2*u) := by
  rw [upChance,upChance,cosh_neg,div_mul_eq_mul_div,← exp_add]
  congr 2; ring

private theorem up_mono : Monotone upChance := by
  have h (u : ℝ) : upChance u = 1/(1+exp (-2*u)) := by
    have H := up_total u
    rw [up_ratio] at H
    apply (eq_div_iff (by positivity)).mpr; linarith only [H]
  intro x y hxy
  rw [h,h]
  exact one_div_le_one_div_of_le (by positivity) (by linarith only [exp_le_exp.mpr (show -2*y ≤ -2*x by linarith)])

theorem up_drift (u : ℝ) : upChance u - upChance (-u) = tanh u := by
  rw [upChance,upChance,cosh_neg,← sub_div,tanh_eq,cosh_eq]; ring_nf

/-- Survival through t signs, starting a steps above the absorbing height. -/
noncomputable def live (c u : ℝ) (t : ℕ) : ℕ → ℝ
  | 0 => 0
  | h+1 => ∑ w ∈ words t, if BallotFrom h w then signMass c u w else 0

@[simp] theorem live_dead (c u : ℝ) (t : ℕ) : live c u t 0 = 0 := rfl
@[simp] theorem live_initial (c u : ℝ) (h : ℕ) : live c u 0 (h+1) = 1 := by
  simp [live,words,BallotFrom,signMass]

theorem live_nonneg (c u : ℝ) (t a : ℕ) : 0 ≤ live c u t a := by
  cases a with
  | zero => rfl
  | succ h => apply Finset.sum_nonneg; intro w _; split <;> first | exact le_rfl | exact (signMass_pos ..).le

private theorem ballot_start_mono (w : List Bool) {a b : ℕ} (hab : a ≤ b) : BallotFrom a w → BallotFrom b w := by
  induction w generalizing a b with
  | nil => simp [BallotFrom]
  | cons v w ih =>
    cases v with
    | false => exact ih (by omega : a+1 ≤ b+1)
    | true => rintro ⟨ha,hw⟩; exact ⟨by omega,ih (by omega) hw⟩

theorem live_start_mono (c u : ℝ) (t : ℕ) : Monotone (live c u t) := by
  intro a b hab
  cases a with
  | zero => exact live_nonneg ..
  | succ a =>
    cases b with
    | zero => omega
    | succ b =>
      apply Finset.sum_le_sum
      intro w _
      have hm := ballot_start_mono w (Nat.le_of_succ_le_succ hab)
      split_ifs with ha hb hb <;> first | exact le_rfl | exact False.elim (hb (hm ha)) | exact (signMass_pos ..).le

theorem live_step (c u : ℝ) (t h : ℕ) :
    live c u (t+1) (h+1) = upChance u*live c (u-c) t (h+2) + upChance (-u)*live c (u-c) t h := by
  rw [live,sum_cons_words]
  congr 1
  · rw [live,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [BallotFrom,signMass,step,Int.cast_one,mul_one]
    split <;> simp [upChance]
  · cases h with
    | zero => simp [BallotFrom]
    | succ h =>
      rw [live,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      simp only [BallotFrom,Nat.zero_lt_succ,true_and,Nat.add_one_sub_one,signMass,step,
        Int.cast_neg,Int.cast_one,mul_neg,mul_one]
      split <;> simp [upChance]

/-- Increasing the natural parameter at every step increases survival. -/
theorem live_parameters (c u c' u' : ℝ) (t a : ℕ)
    (hh : ∀ i < t, u-c*i ≤ u'-c'*i) : live c u t a ≤ live c' u' t a := by
  induction t generalizing u u' a with
  | zero => cases a <;> simp
  | succ t ih =>
    cases a with
    | zero => simp
    | succ h =>
      have hle : u ≤ u' := by simpa using hh 0 (Nat.zero_lt_succ _)
      have htail (i : ℕ) (hi : i<t) : (u-c)-c*i ≤ (u'-c')-c'*i := by
        have H := hh (i+1) (Nat.succ_lt_succ hi)
        push_cast at H; linarith only [H]
      rw [live_step,live_step]
      apply (add_le_add (mul_le_mul_of_nonneg_left (ih _ _ (h+2) htail) (up_pos u).le)
        (mul_le_mul_of_nonneg_left (ih _ _ h htail) (up_pos (-u)).le)).trans
      have hm := live_start_mono c' (u'-c') t (show h ≤ h+2 by omega)
      have hd := mul_nonneg (sub_nonneg.mpr (up_mono hle)) (sub_nonneg.mpr hm)
      rw [show upChance (-u)=1-upChance u by linarith only [up_total u],
        show upChance (-u')=1-upChance u' by linarith only [up_total u']]
      linarith only [hd]

/-- Exact change from positive to negative homogeneous drift at the first
hit. On a first hit the displacement equals minus the starting distance. -/
theorem homogeneous_live (u : ℝ) (t a : ℕ) :
    live 0 u t a = 1-(exp (-2*u))^a+(exp (-2*u))^a*live 0 (-u) t a := by
  induction t generalizing a with
  | zero => cases a <;> simp
  | succ t ih =>
    cases a with
    | zero => simp
    | succ h =>
      simp only [live_step,sub_zero,neg_neg,ih (h+2),ih h,pow_succ]
      have he := up_ratio u
      have ht := up_total u
      linear_combination (1-(exp (-2*u))^h * exp (-2*u))*ht +
        ((exp (-2*u))^h * (exp (-2*u)-1 + live 0 (-u) t h -
          exp (-2*u)*live 0 (-u) t (h+2)))*he

/-- Under negative homogeneous drift, the mean of the first hitting time
truncated at any L is at most the initial distance divided by the drift. -/
theorem negative_drift_lifetime (u : ℝ) (L a : ℕ) :
    tanh u * ∑ t ∈ Finset.range L, live 0 (-u) t a ≤ a := by
  induction L generalizing a with
  | zero => simp
  | succ L ih =>
    cases a with
    | zero => simp
    | succ h =>
      rw [Finset.sum_range_succ']
      simp only [live_step,sub_zero,neg_neg,live_initial,Finset.sum_add_distrib,← Finset.mul_sum]
      have h₁ := mul_le_mul_of_nonneg_left (ih (h+2)) (up_pos (-u)).le
      have h₂ := mul_le_mul_of_nonneg_left (ih h) (up_pos u).le
      push_cast at h₁ h₂ ⊢
      have ht := up_total u
      have hd := up_drift u
      linear_combination h₁ + h₂ + (h+1:ℝ)*ht - hd

theorem live_lower (c u v : ℝ) (L a : ℕ) (hv : ∀ i < L, v ≤ u-c*i) :
    1-(exp (-2*v))^a ≤ live c u L a := by
  have h := live_parameters 0 v c u L a (by simpa using hv)
  rw [homogeneous_live] at h
  linarith only [h,mul_nonneg (pow_nonneg (exp_pos (-2*v)).le a) (live_nonneg 0 (-v) L a)]

/-- The sum of the excess survival over the final survival is the first
moment of the hits that have occurred by step L. -/
theorem prefix_lifetime_bound {c u v : ℝ} (hc : 0 ≤ c) (hu : 0 < tanh u) (L : ℕ)
    (hv : ∀ i < L, v ≤ u-c*i) :
    ∑ t ∈ Finset.range L, (live c u t 1-live c u L 1) ≤
      L*(exp (-2*v)-exp (-2*u)) + exp (-2*u)/tanh u := by
  have hL := live_lower c u v L 1 hv
  simp only [pow_one] at hL
  have h (t : ℕ) : live c u t 1 ≤ live 0 u t 1 :=
    live_parameters c u 0 u t 1 (fun i _ => by simp; positivity)
  calc
    _ ≤ ∑ t ∈ Finset.range L, ((exp (-2*v)-exp (-2*u))+exp (-2*u)*live 0 (-u) t 1) := by
      apply Finset.sum_le_sum
      intro t _
      have ht := h t
      rw [homogeneous_live] at ht
      simp only [pow_one] at ht
      linarith only [ht,hL]
    _ = L*(exp (-2*v)-exp (-2*u))+exp (-2*u)*∑ t ∈ Finset.range L, live 0 (-u) t 1 := by
      simp [Finset.sum_add_distrib,← Finset.mul_sum]; ring
    _ ≤ _ := by
      apply add_le_add_right
      rw [div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
      apply (le_div_iff₀ hu).mpr
      simpa [mul_comm] using negative_drift_lifetime u L 1

/-- The probability used in the denominator of the prefix variance bound. -/
theorem live_ballots (c u : ℝ) (t : ℕ) :
    live c u t 1 = ∑ w ∈ ballots t, signMass c u w := by
  simp [live,ballots,Finset.sum_filter]

private theorem ballot_snoc_iff (w : List Bool) (b : Bool) :
    BallotFrom 0 (w++[b]) ↔ BallotFrom 0 w ∧ 0 ≤ displacement (w++[b]) := by
  simp [ballot_iff_heights,heights_append,heights,displacement_snoc]
  exact ⟨fun h => ⟨fun y hy => h y (Or.inl hy),h _ (Or.inr rfl)⟩,
    fun ⟨h₁,h₂⟩ y hy => hy.elim (h₁ y) (fun he => he ▸ h₂)⟩

private theorem prefix_partition {w : List Bool} {t : ℕ} (hw : w ∈ words (t+1)) :
    (w.take t ∈ ballots t ↔ BallotFrom 0 w ∨ FirstHitPath 1 w) ∧
    ¬(BallotFrom 0 w ∧ FirstHitPath 1 w) := by
  induction w using List.reverseRecOn with
  | nil => simp [mem_words] at hw
  | append_singleton w b _ =>
    have hlen : w.length=t := by simpa [mem_words] using hw
    have ht : (w++[b]).take t=w := by rw [← hlen,List.take_left]
    have hf : FirstHitPath 1 (w++[b]) ↔ 1+displacement (w++[b])=0 ∧ BallotFrom 0 w := by
      simp [FirstHitPath,positive_one_iff]
    rw [ht,ballot_snoc_iff,hf,mem_ballots,displacement_snoc]
    by_cases hb : BallotFrom 0 w
    · have he : 0 ≤ displacement w := by simpa using ballot_endpoint_nonneg hb
      cases b <;> simp [hlen,hb,step] <;> omega
    · simp [hb]

/-- Extend each surviving prefix by both signs. Exactly one of survival
and a first hit accounts for each extended word. -/
theorem split_live_hit (t : ℕ) (F : List Bool → ℝ) :
    (∑ w ∈ ballots (t+1), F w) + (∑ w ∈ hitWords 1 (t+1), F w) =
      ∑ v ∈ ballots t, (F (v++[false]) + F (v++[true])) := by
  have h : (∑ w ∈ ballots (t+1), F w) + (∑ w ∈ hitWords 1 (t+1), F w) =
      ∑ w ∈ words (t+1), if w.take t ∈ ballots t then F w else 0 := by
    simp only [ballots,hitWords,Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hp,hd⟩ := prefix_partition hw
    change _ = if w.take t ∈ ballots t then F w else 0
    by_cases hb : BallotFrom 0 w <;> by_cases hh : FirstHitPath 1 w <;> simp_all
  rw [h,sum_snoc_words,← Finset.sum_add_distrib,ballots,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  have he := mem_words.mp hw
  by_cases hb : BallotFrom 0 w <;> simp [← he,mem_words,hb]

theorem prefix_first_hit (c u : ℝ) (t : ℕ) :
    live c u t 1 - live c u (t+1) 1 = ∑ w ∈ hitWords 1 (t+1), signMass c u w := by
  have h := mass_prefix c u (m := t+1) (t := t) (by omega) (ballots t) (Finset.filter_subset ..)
  rw [← live_ballots] at h
  rw [← h,hitWords,live,Finset.sum_filter,Finset.sum_filter,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  obtain ⟨hp,hd⟩ := prefix_partition hw
  by_cases hb : BallotFrom 0 w <;> by_cases hh : FirstHitPath 1 w <;> simp_all

private theorem partial_summation (F : ℕ → ℝ) (L : ℕ) :
    ∑ t ∈ Finset.range L, (t+1:ℝ)*(F t-F (t+1)) =
      ∑ t ∈ Finset.range L, (F t-F L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_range_succ]
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    ring

theorem hit_time_first_moment {c u v : ℝ} (hc : 0 ≤ c) (hu : 0 < tanh u) (L : ℕ)
    (hv : ∀ i < L, v ≤ u-c*i) :
    ∑ t ∈ Finset.range L, (t+1:ℝ)*(∑ w ∈ hitWords 1 (t+1), signMass c u w) ≤
      L*(exp (-2*v)-exp (-2*u)) + exp (-2*u)/tanh u := by
  simp_rw [← prefix_first_hit]
  rw [partial_summation]
  exact prefix_lifetime_bound hc hu L hv

end CentralUnimodality.MarkedExcursion
