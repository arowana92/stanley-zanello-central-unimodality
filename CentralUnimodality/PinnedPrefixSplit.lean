module

public import CentralUnimodality.OuterPrefixSurvival
public import CentralUnimodality.PinnedMiddleMass
import CentralUnimodality.DyckRecurrence

/-! Split a first-hit word before its last step into two outer surviving
pieces and an independent middle piece with a prescribed displacement. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- Reversing time and negating signs preserves the slope and reflects its intercept. -/
theorem signMass_reverse (c u : ℝ) (w : List Bool) :
    signMass c u (reverseWalk w) = signMass c (c*((w.length:ℝ)-1)-u) w := by
  induction w generalizing u with
  | nil => simp [signMass,reverseWalk]
  | cons b w ih =>
    rw [reverseWalk_cons,append_mass,ih,reverseWalk_length]
    simp only [signMass,step_flip,List.length_cons,Nat.cast_succ,mul_one]
    rw [show c*((w.length:ℝ)+1-1)-u=c*w.length-u by ring,
      show c*((w.length:ℝ)-1)-u=c*w.length-u-c by ring,
      show u-c*w.length=-(c*w.length-u) by ring,cosh_neg]
    push_cast; ring_nf

private theorem reversed_ballot_mass (c u : ℝ) (b : ℕ) :
    (∑ w ∈ words b, if BallotFrom 0 (reverseWalk w) then signMass c u w else 0) =
      live c (c*((b:ℝ)-1)-u) b 1 := by
  rw [live_ballots,ballots,Finset.sum_filter]
  apply Finset.sum_bij' (fun w _ => reverseWalk w) (fun w _ => reverseWalk w)
  · intro w hw; simpa [mem_words] using hw
  · intro w hw; simpa [mem_words] using hw
  · intro w _; simp
  · intro w _; simp
  · intro w hw
    rw [signMass_reverse,mem_words.mp hw,show c*((b:ℝ)-1)-(c*(b-1)-u)=u by ring]

private theorem front_ballot {p q : List Bool} (h : BallotFrom 0 (p++q)) : BallotFrom 0 p := by
  rw [ballot_iff_heights,heights_append] at h
  exact (ballot_iff_heights 0 p).mpr (fun z hz => h z (List.mem_append_left _ hz))

private theorem bridge_pieces (p q s : List Bool) {b : Bool} (h : FirstHitPath 1 (((p++q)++s)++[b])) :
    b=true ∧ BallotFrom 0 p ∧ BallotFrom 0 (reverseWalk s) ∧ displacement q= -displacement p-displacement s := by
  let w := (p++q)++s
  have hf : BallotFrom 0 w := (positive_one_iff w).mp (by simpa [w] using h.2.2)
  have hend := h.2.1
  change (1:ℤ)+displacement (w++[b])=0 at hend
  rw [displacement_snoc] at hend
  have hpos := ballot_endpoint_nonneg hf
  have hb : b=true := by cases b <;> simp_all [step]; omega
  have hw : displacement w=0 := by rw [hb] at hend; simp [step] at hend; omega
  have hr := (positive_reverse 1 w).2 ((positive_one_iff _).mpr hf)
  rw [hw,add_zero,positive_one_iff] at hr
  have happ : reverseWalk w=reverseWalk s++reverseWalk (p++q) := by simp [w,reverseWalk]
  rw [happ] at hr
  refine ⟨hb,front_ballot (front_ballot hf),front_ballot hr,?_⟩
  simp only [w,displacement_append] at hw; omega

/-- The first-hit mass is bounded by the product of the outer survival
probabilities, the reversed mandatory up-step, and the middle endpoint bound. -/
theorem first_hit_three_blocks (c u : ℝ) (a q b : ℕ) {K : ℝ}
    (hK : ∀ z : ℤ, (∑ w ∈ (words q).filter (fun w => displacement w=z), signMass c (u-c*a) w) ≤ K) :
    let v := c*(a+q+b:ℕ)-u
    (∑ w ∈ hitWords 1 (a+q+b+1), signMass c u w) ≤
      live c u a 1 * upChance v * live c (v-c) b 1 * K := by
  let v := c*(a+q+b:ℕ)-u
  let U := u-c*a
  let W := u-c*(a+q:ℕ)
  let P := fun w => if BallotFrom 0 w then signMass c u w else 0
  let S := fun w => if BallotFrom 0 (reverseWalk w) then signMass c W w else 0
  have hP (w) : 0 ≤ P w := by dsimp [P]; split <;> first | exact (signMass_pos ..).le | exact le_rfl
  have hS (w) : 0 ≤ S w := by dsimp [S]; split <;> first | exact (signMass_pos ..).le | exact le_rfl
  have hp : (∑ w ∈ words a, P w)=live c u a 1 := by rw [live_ballots,ballots,Finset.sum_filter]
  have hs : (∑ w ∈ words b, S w)=live c (v-c) b 1 := by
    have he : v-c = c*((b:ℝ)-1)-W := by dsimp [v,W]; push_cast; ring
    rw [he]; exact reversed_ballot_mass c W b
  have hu : 0 ≤ upChance v := by unfold upChance; positivity
  let F (last : Bool) (x : List Bool) := if FirstHitPath 1 (x++[last]) then signMass c u (x++[last]) else 0
  have zero (x : List Bool) : F false x=0 := by
    have h : ¬ FirstHitPath 1 (x++[false]) := by
      intro H
      have hh : FirstHitPath 1 (((x++[])++[])++[false]) := by simpa using H
      exact Bool.noConfusion (bridge_pieces x [] [] hh).1
    exact ite_eq_right h
  rw [hitWords,Finset.sum_filter,sum_snoc_words]
  change (∑ w ∈ words _, F false w)+(∑ w ∈ words _, F true w) ≤ _
  simp only [zero,Finset.sum_const_zero,zero_add]
  rw [split_word_sum (a+q) b]
  rw [split_word_sum a q]
  let pin (p s w : List Bool) := if displacement w= -displacement p-displacement s then signMass c U w else 0
  have bound (p w s : List Bool) (hpw : p ∈ words a) (hqw : w ∈ words q) (hsw : s ∈ words b) :
      F true ((p++w)++s) ≤ (P p*S s*upChance v)*pin p s w := by
    dsimp only [F]
    split
    · rename_i h
      obtain ⟨_,h₁,h₂,h₃⟩ := bridge_pieces p w s h
      simp only [P,S,pin,ite_eq_left h₁,ite_eq_left h₂,ite_eq_left h₃,append_mass,List.length_append,
        mem_words.mp hpw,mem_words.mp hqw,mem_words.mp hsw,Nat.cast_add]
      have hh : upChance v=signMass c (u-c*((a:ℝ)+q+b)) [true] := by
        dsimp [signMass,step,upChance,v]; push_cast
        rw [show c*((a:ℝ)+q+b)-u= -(u-c*(a+q+b)) by ring,cosh_neg]; ring_nf
      rw [hh]; dsimp [U,W]; push_cast; apply le_of_eq; ring_nf
    · have hpin : 0 ≤ pin p s w := by dsimp [pin]; split <;> first | exact (signMass_pos ..).le | exact le_rfl
      exact mul_nonneg (mul_nonneg (mul_nonneg (hP p) (hS s)) hu) hpin
  apply (Finset.sum_le_sum (fun p hpw => Finset.sum_le_sum (fun w hqw => Finset.sum_le_sum
    (fun s hsw => bound p w s hpw hqw hsw)))).trans
  have per (p : List Bool) :
      (∑ w ∈ words q, ∑ s ∈ words b, (P p*S s*upChance v)*pin p s w) ≤
        P p*((∑ s ∈ words b, S s)*upChance v*K) := by
    rw [Finset.sum_comm]
    have h (s : List Bool) : (∑ w ∈ words q, pin p s w) ≤ K := by
      simpa only [Finset.sum_filter] using hK (-displacement p-displacement s)
    simp_rw [← Finset.mul_sum]
    apply (Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h s)
      (mul_nonneg (mul_nonneg (hP p) (hS s)) hu))).trans_eq
    simp only [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
  apply (Finset.sum_le_sum (fun p _ => per p)).trans_eq
  rw [← Finset.sum_mul,hp,hs]
  ring

end CentralUnimodality.MarkedExcursion
