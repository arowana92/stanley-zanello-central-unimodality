module

public import CentralUnimodality.ReverseWalk
public import CentralUnimodality.Survival
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! A walk first hitting zero from positive height reverses to an initial
up-step and a ballot walk. The ordinary ballot count gives the exact
first-hit probability used in the killed-block estimates. -/
@[expose] public section

namespace CentralUnimodality

def FirstHitPath (a : ℕ) (w : List Bool) : Prop :=
  w ≠ [] ∧ (a:ℤ)+displacement w = 0 ∧ PositiveVertices a w.dropLast

instance (a : ℕ) (w : List Bool) : Decidable (FirstHitPath a w) :=
  inferInstanceAs (Decidable (w ≠ [] ∧ (a:ℤ)+displacement w = 0 ∧ ∀ x ∈ vertices a w.dropLast, 0 < x))

def hitWords (a m : ℕ) := (words m).filter (FirstHitPath a)
def endBallots (m e : ℕ) := (ballots m).filter (fun w => displacement w = (e:ℤ))

private theorem hit_snoc (a : ℕ) (w : List Bool) (b : Bool) :
    FirstHitPath (a+1) (w++[b]) ↔ b=true ∧ BallotFrom 0 (reverseWalk w) ∧ displacement (reverseWalk w) = (a:ℤ) := by
  simp only [FirstHitPath,
    List.dropLast_append_of_ne_nil (by simp : [b] ≠ []),List.dropLast_singleton,List.append_nil,
    Nat.cast_succ,displacement_snoc,reverseWalk_disp]
  constructor
  · rintro ⟨_,hd,hp⟩
    have ht := hp _ (endpoint_mem_vertices _ w)
    obtain rfl : b = true := by cases b <;> simp_all [step]; omega
    have h₁ : (a:ℤ)+1+displacement w = 1 := by dsimp [step] at hd; omega
    refine ⟨rfl,(positive_one_iff _).mp ?_,by omega⟩
    rw [← h₁]
    exact (positive_reverse _ _).mpr hp
  · rintro ⟨rfl,hp,hd⟩
    have h₁ : (a:ℤ)+1+displacement w = 1 := by omega
    refine ⟨by simp,by dsimp [step]; omega,(positive_reverse _ _).mp ?_⟩
    rw [h₁]
    exact (positive_one_iff _).mpr hp

theorem card_hit_ballot (a m : ℕ) : (hitWords (a+1) (m+1)).card = (endBallots m a).card := by
  apply Finset.card_bij' (fun w _ => reverseWalk w.dropLast) (fun w _ => reverseWalk w ++ [true])
  · intro w hw
    obtain ⟨hl,h⟩ := Finset.mem_filter.mp hw
    have he := mem_words.mp hl
    induction w using List.reverseRecOn with
    | nil => simp at he
    | append_singleton v b _ =>
      obtain ⟨rfl,hb,hd⟩ := (hit_snoc _ _ _).mp h
      simp only [List.dropLast_append_of_ne_nil (by simp : [true] ≠ []),List.dropLast_singleton,List.append_nil]
      exact Finset.mem_filter.mpr ⟨mem_ballots.mpr ⟨by simpa using he,hb⟩,hd⟩
  · intro w hw
    obtain ⟨h,hd⟩ := Finset.mem_filter.mp hw
    obtain ⟨hl,hb⟩ := mem_ballots.mp h
    exact Finset.mem_filter.mpr ⟨mem_words.mpr (by simp [hl]),(hit_snoc _ _ _).mpr (by simp [hb,hd])⟩
  · intro w hw
    induction w using List.reverseRecOn with
    | nil => exact False.elim ((Finset.mem_filter.mp hw).2.1 rfl)
    | append_singleton v b _ =>
      obtain ⟨rfl,_,_⟩ := (hit_snoc _ _ _).mp (Finset.mem_filter.mp hw).2
      simp
  · intro w _
    simp

theorem card_endBallots (m e d : ℕ) (hm : m = e+2*d) :
    (endBallots m e).card = (partitions m d).card := by
  apply Finset.card_bij' (fun w _ => wordParts w) (fun v _ => wordOfParts m v)
  · intro w hw
    obtain ⟨hb,hd⟩ := Finset.mem_filter.mp hw
    obtain ⟨hl,hb⟩ := mem_ballots.mp hb
    have he := displacement_length w
    rw [hd,hl] at he
    exact mem_partitions.mpr ⟨by simpa [hl] using (ballot_iff_fits 0 w).mp hb,by omega⟩
  · intro v hv
    obtain ⟨hf,he⟩ := mem_partitions.mp hv
    have hl := ((ballotEquiv m).symm ⟨v,hf⟩).property
    change (wordOfParts m v).length = m ∧ BallotFrom 0 (wordOfParts m v) at hl
    refine Finset.mem_filter.mpr ⟨mem_ballots.mpr hl,?_⟩
    have hw := displacement_length (wordOfParts m v)
    rw [wordParts_wordOfParts hf,he,hl.1] at hw
    omega
  · intro w hw
    rw [← (mem_ballots.mp (Finset.mem_filter.mp hw).1).1,wordOfParts_wordParts]
  · intro v hv
    exact wordParts_wordOfParts (mem_partitions.mp hv).1

theorem first_hit_count (a m d : ℕ) (hm : m = a+2*d) :
    (m+1)*(hitWords (a+1) (m+1)).card = (a+1)*(m+1).choose d := by
  rw [card_hit_ballot,card_endBallots m a d hm]
  cases d with
  | zero =>
    simp only [Nat.mul_zero,Nat.add_zero] at hm
    subst a
    cases m <;> simp [partitions]
  | succ d =>
    have he := card_partitions_length m d (by omega)
    have hratio := Nat.choose_succ_right_eq m d
    have hs : m-d+d = m := by omega
    rw [Nat.choose_succ_succ]
    calc
      _ = (a+2*(d+1)+1)*(partitions m (d+1)).card := by rw [← hm]
      _ = _ := by
        nlinarith only [congrArg (·*(a+1)) he,congrArg (·*(d+1)) he,hratio,
          congrArg (fun k => m.choose d*k) hm,congrArg (fun k => m.choose d*k) hs]

theorem first_hit_incompatible (a m : ℕ) (hm : ¬ ∃ d, m = a+2*d) : hitWords (a+1) (m+1) = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [card_hit_ballot,Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hb,hd⟩ := Finset.mem_filter.mp hw
  have h := displacement_length w
  rw [(mem_ballots.mp hb).1,hd] at h
  exact hm ⟨(wordParts w).length,by omega⟩

theorem fair_first_hit (a m d : ℕ) (hm : m = a+2*d) :
    ((hitWords (a+1) (m+1)).card:ℝ)/(2:ℝ)^(m+1) =
      ((a:ℝ)+1)*((m+1).choose d:ℝ)/(((m:ℝ)+1)*2^(m+1)) := by
  have he : ((m:ℝ)+1)*(hitWords (a+1) (m+1)).card = ((a:ℝ)+1)*(m+1).choose d := by
    exact_mod_cast first_hit_count a m d hm
  field_simp
  linear_combination he

end CentralUnimodality
