module

public import CentralUnimodality.KilledKernel

/-! Restoring the lost mass at the boundary gives the unrestricted kernel
as the surviving kernel plus all first hits followed by a free suffix. -/
@[expose] public section

namespace CentralUnimodality

private theorem killed_loss (ω : ℝ) (a n : ℕ) (z : ℤ) :
    killedAt ω a (n+1) z + (if z=0 then hitAt ω a (n+1) else 0) =
      areaCharacter ω z*(killedAt ω a n (z-1)+killedAt ω a n (z+1)) := by
  rcases lt_trichotomy z 0 with hz|rfl|hz
  · rw [ite_eq_right hz.ne,killedAt_nonpos _ _ _ hz.le,
      killedAt_nonpos _ _ _ (by omega : z-1 ≤ 0),killedAt_nonpos _ _ _ (by omega : z+1 ≤ 0)]
    ring
  · rw [killedAt_nonpos _ _ _ le_rfl,ite_eq_left rfl,areaCharacter_zero,
      killedAt_nonpos _ _ _ (by decide : (0:ℤ)-1 ≤ 0),hitAt_succ]
    simp
  · rw [ite_eq_right hz.ne',add_zero,killedAt_step _ _ _ hz]

noncomputable def lostAt (ω : ℝ) (a n : ℕ) (z : ℤ) : ℂ :=
  ∑ t ∈ Finset.range (n+1), hitAt ω a t * freeAt ω 0 (n-t) z

private theorem lost_step (ω : ℝ) (a n : ℕ) (z : ℤ) :
    lostAt ω a (n+1) z = areaCharacter ω z*(lostAt ω a n (z-1)+lostAt ω a n (z+1)) +
      (if z=0 then hitAt ω a (n+1) else 0) := by
  rw [lostAt,Finset.sum_range_succ,Nat.sub_self,freeAt_zero]
  have last : hitAt ω a (n+1)*(if z=0 then 1 else 0) = if z=0 then hitAt ω a (n+1) else 0 := by
    split <;> simp
  rw [last]
  congr 1
  simp only [lostAt,mul_add,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have h := Finset.mem_range.mp ht
  rw [show n+1-t = (n-t)+1 by omega,freeAt_step]
  ring

theorem first_hit_expansion (ω : ℝ) {a : ℕ} (ha : 0 < a) (n : ℕ) (z : ℤ) :
    freeAt ω a n z = killedAt ω a n z + lostAt ω a n z := by
  induction n generalizing z with
  | zero => simp [freeAt_zero,killedAt_zero ω (by exact_mod_cast ha : (0:ℤ) < a),lostAt,hitAt_zero]
  | succ n ih =>
    rw [freeAt_step,ih (z-1),ih (z+1),lost_step]
    linear_combination -(killed_loss ω a n z)

theorem hitAt_norm (ω : ℝ) (a t : ℕ) : ‖hitAt ω a t‖ ≤ (hitWords a t).card := by
  exact (norm_sum_le ..).trans_eq (by simp [norm_areaCharacter])

private theorem freeAt_norm_bound (ω : ℝ) {n : ℕ} {B : ℝ} (h : EndpointNormBound ω n B)
    (a : ℤ) (s : Finset ℤ) : ∑ z ∈ s, ‖freeAt ω a n z‖ ≤ B := by
  simp only [freeAt,norm_mul,norm_areaCharacter,one_mul]
  have inj : Function.Injective (fun z : ℤ => z-a) := fun x y (he : x-a = y-a) => by omega
  simpa only [Finset.sum_image inj.injOn] using h (s.image (·-a))

theorem killed_norm_from_first_hits (ω : ℝ) {a : ℕ} (ha : 0 < a) (n : ℕ)
    (B : ℕ → ℝ) (hB : ∀ j ≤ n, EndpointNormBound ω j (B j)) (s : Finset ℤ) :
    ∑ z ∈ s, ‖killedAt ω a n z‖ ≤ B n + ∑ t ∈ Finset.range (n+1), (hitWords a t).card * B (n-t) := by
  have per (z : ℤ) : ‖killedAt ω a n z‖ ≤ ‖freeAt ω a n z‖ +
      ∑ t ∈ Finset.range (n+1), (hitWords a t).card * ‖freeAt ω 0 (n-t) z‖ := by
    have he := first_hit_expansion ω ha n z
    rw [show killedAt ω a n z = freeAt ω a n z - lostAt ω a n z by rw [he]; ring]
    apply (norm_sub_le ..).trans
    apply add_le_add le_rfl
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro t _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hitAt_norm ω a t) (norm_nonneg _)
  refine (Finset.sum_le_sum (fun z _ => per z)).trans ?_
  rw [Finset.sum_add_distrib,Finset.sum_comm (s := s) (t := Finset.range (n+1))]
  apply add_le_add (freeAt_norm_bound _ (hB _ le_rfl) _ _) (Finset.sum_le_sum ?_)
  intro t _
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (freeAt_norm_bound _ (hB _ (Nat.sub_le ..)) _ _) (by positivity)

end CentralUnimodality
