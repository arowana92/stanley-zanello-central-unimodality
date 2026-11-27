module

public import CentralUnimodality.ShiftedMoments

/-! A certificate for the first M moment columns is sufficient if the three
functional equations agree through order M. Uniqueness is by induction on
the size, so no analytic convergence or infinite certificate is needed. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

def SameJet (M : ℕ) (s t : PowerSeries ℚ) : Prop := ∀ j ≤ M, coeff j s = coeff j t

namespace SameJet

theorem refl (M : ℕ) (s : PowerSeries ℚ) : SameJet M s s := fun _ _ => rfl

theorem trans {M : ℕ} {s t u : PowerSeries ℚ} (h : SameJet M s t) (h' : SameJet M t u) :
    SameJet M s u := fun j hj => (h j hj).trans (h' j hj)

theorem add {M : ℕ} {a b c d : PowerSeries ℚ} (ha : SameJet M a b) (hc : SameJet M c d) :
    SameJet M (a+c) (b+d) := fun j hj => by rw [map_add, map_add, ha j hj, hc j hj]

theorem mul {M : ℕ} {a b c d : PowerSeries ℚ} (ha : SameJet M a b) (hc : SameJet M c d) :
    SameJet M (a*c) (b*d) := by
  intro j hj
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  rw [ha _ (by omega), hc _ (by omega)]

end SameJet

def SameColumns (M : ℕ) (F G : MomentBiseries) : Prop :=
  ∀ r ≤ M, momentColumn r F = momentColumn r G

private theorem sameColumns_iff (M : ℕ) (F G : MomentBiseries) :
    SameColumns M F G ↔ ∀ n, SameJet M (coeff n F) (coeff n G) := by
  constructor
  · intro h n r hr
    simpa only [← coeff_momentColumn] using congrArg (coeff n) (h r hr)
  · intro h r hr
    exact PowerSeries.ext fun n => by simpa only [coeff_momentColumn] using h n r hr

private theorem product_jet {A B F G : MomentBiseries} {n M : ℕ}
    (hA : ∀ i ≤ n, SameJet M (coeff i A) (coeff i F))
    (hB : ∀ i ≤ n, SameJet M (coeff i B) (coeff i G)) :
    SameJet M (coeff n (A*B)) (coeff n (F*G)) := by
  rw [coeff_mul, coeff_mul]
  intro r hr
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  exact ((hA _ (by omega)).mul (hB _ (by omega))) r hr

private theorem shifted_product_jet {A B F G : MomentBiseries} {n M : ℕ} (q : PowerSeries ℚ)
    (hA : ∀ i ≤ n, SameJet M (coeff i A) (coeff i F))
    (hB : ∀ i ≤ n, SameJet M (coeff i B) (coeff i G)) :
    SameJet M (coeff n (A*rescale q B)) (coeff n (F*rescale q G)) := by
  apply product_jet hA
  intro i hi
  rw [coeff_rescale, coeff_rescale]
  exact (SameJet.refl _ _).mul (hB _ hi)

/-- The candidate equations only need proof on the selected moment columns.
The candidate size coefficients then agree with the exact Catalan and ballot
series through that order at every length. -/
theorem certify_moment_series (q : PowerSeries ℚ) (M : ℕ) (D B O : MomentBiseries)
    (hD : SameColumns M D (1+X*(D*rescale q D)))
    (hB : SameColumns M B (D+X*(C q*(D*rescale q O))))
    (hO : SameColumns M O (D*rescale q B)) :
    SameColumns M D (dyckSeries q) ∧ SameColumns M B (evenBallotSeries q) ∧
      SameColumns M O (oddBallotSeries q) := by
  have hd := (sameColumns_iff ..).mp hD
  have hb := (sameColumns_iff ..).mp hB
  have ho := (sameColumns_iff ..).mp hO
  have all (n : ℕ) : SameJet M (coeff n D) (coeff n (dyckSeries q)) ∧
      SameJet M (coeff n B) (coeff n (evenBallotSeries q)) ∧
      SameJet M (coeff n O) (coeff n (oddBallotSeries q)) := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      have dd : SameJet M (coeff n D) (coeff n (dyckSeries q)) := by
        apply (hd n).trans
        conv_rhs => rw [dyckSeries_eq]
        rw [map_add, map_add]
        apply (SameJet.refl _ _).add
        cases n with
        | zero => simp [SameJet.refl]
        | succ k =>
          rw [coeff_succ_X_mul, coeff_succ_X_mul]
          exact shifted_product_jet q (fun i hi => (ih i (by omega)).1) (fun i hi => (ih i (by omega)).1)
      have bb : SameJet M (coeff n B) (coeff n (evenBallotSeries q)) := by
        apply (hb n).trans
        conv_rhs => rw [evenBallotSeries_eq]
        rw [map_add, map_add]
        apply dd.add
        cases n with
        | zero => simp [SameJet.refl]
        | succ k =>
          rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_C_mul, coeff_C_mul]
          exact (SameJet.refl _ _).mul
            (shifted_product_jet q (fun i hi => (ih i (by omega)).1) (fun i hi => (ih i (by omega)).2.2))
      refine ⟨dd,bb,(ho n).trans ?_⟩
      rw [oddBallotSeries_eq]
      apply shifted_product_jet q
      · intro i hi
        rcases hi.eq_or_lt with rfl | h
        · exact dd
        · exact (ih i h).1
      · intro i hi
        rcases hi.eq_or_lt with rfl | h
        · exact bb
        · exact (ih i h).2.1
  exact ⟨(sameColumns_iff ..).mpr fun n => (all n).1, (sameColumns_iff ..).mpr fun n => (all n).2.1,
    (sameColumns_iff ..).mpr fun n => (all n).2.2⟩

end CentralUnimodality
