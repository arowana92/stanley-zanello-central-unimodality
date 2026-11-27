module

public import CentralUnimodality.MomentUniqueness

/-! Certifying the three moment columns directly in the form used by Stump's
recurrence requires only rescalings of the Dyck and even-ballot series. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

namespace SameColumns

theorem refl (M : ℕ) (F : MomentBiseries) : SameColumns M F F := fun _ _ => rfl

theorem symm {M} {F G : MomentBiseries} (h : SameColumns M F G) : SameColumns M G F :=
  fun r hr => (h r hr).symm

theorem trans {M} {F G H : MomentBiseries} (h : SameColumns M F G) (h' : SameColumns M G H) :
    SameColumns M F H := fun r hr => (h r hr).trans (h' r hr)

theorem add {M} {A B F G : MomentBiseries} (h : SameColumns M A F) (h' : SameColumns M B G) :
    SameColumns M (A+B) (F+G) := by
  intro r hr
  apply PowerSeries.ext
  intro n
  simp only [coeff_momentColumn, map_add]
  rw [← coeff_momentColumn, h r hr, ← coeff_momentColumn r n B, h' r hr]
  simp only [coeff_momentColumn]

theorem sub {M} {A B F G : MomentBiseries} (h : SameColumns M A F) (h' : SameColumns M B G) :
    SameColumns M (A-B) (F-G) := by
  intro r hr
  apply PowerSeries.ext
  intro n
  simp only [coeff_momentColumn, map_sub]
  rw [← coeff_momentColumn, h r hr, ← coeff_momentColumn r n B, h' r hr]
  simp only [coeff_momentColumn]

theorem mul {M} {A B F G : MomentBiseries} (h : SameColumns M A F) (h' : SameColumns M B G) :
    SameColumns M (A*B) (F*G) := by
  intro r hr
  rw [momentColumn_mul, momentColumn_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have := Finset.mem_range.mp hj
  rw [h j (by omega), h' (r-j) (by omega)]

theorem dilation {M} {A F : MomentBiseries} (h : SameColumns M A F) (q : PowerSeries ℚ) :
    SameColumns M (rescale q A) (rescale q F) := by
  intro r hr
  apply PowerSeries.ext
  intro n
  simp only [coeff_momentColumn, coeff_rescale]
  have hj : SameJet M (coeff n A) (coeff n F) := by
    intro j hle
    simpa only [coeff_momentColumn] using congrArg (coeff n) (h j hle)
  exact ((SameJet.refl M (q^n)).mul hj) r hr

end SameColumns

theorem certify_stump_moments (q : PowerSeries ℚ) (M : ℕ) (D B O : MomentBiseries)
    (hD : SameColumns M D (1+X*(D*rescale q D)))
    (hB : SameColumns M B (D+C q*((D-1)*rescale (q^2) B)))
    (hO : SameColumns M O (D*rescale q B)) :
    SameColumns M D (dyckSeries q) ∧ SameColumns M B (evenBallotSeries q) ∧
      SameColumns M O (oddBallotSeries q) := by
  apply certify_moment_series q M D B O hD _ hO
  have h₁ := hD.sub (SameColumns.refl M 1)
  rw [add_sub_cancel_left] at h₁
  have hd := hO.dilation q
  rw [map_mul, rescale_rescale, ← pow_two] at hd
  apply hB.trans
  apply (SameColumns.refl M D).add
  apply ((SameColumns.refl M (C q)).mul (h₁.mul (SameColumns.refl M (rescale (q^2) B)))).trans
  have he : C q * (X * (D * rescale q D) * rescale (q^2) B) =
      X * (C q * (D * (rescale q D * rescale (q^2) B))) := by ac_rfl
  rw [he]
  exact (SameColumns.refl M X).mul ((SameColumns.refl M (C q)).mul ((SameColumns.refl M D).mul hd.symm))

end CentralUnimodality
