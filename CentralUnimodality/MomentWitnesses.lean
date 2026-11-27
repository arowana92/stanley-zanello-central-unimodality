module

public import CentralUnimodality.WitnessPolynomial

/-! The two explicit witnesses and their antiderivative tests. Only the
row-dependent weighted expectation signs are hypotheses of the final test. -/
@[expose] public section

namespace CentralUnimodality.Witness

structure Data where
  a : ℚ
  B : ℚ
  t : ℚ
  roots : List ℚ

def first : Data := ⟨0.262, 0.355, 1.0825,
  [0.142, 0.215, 0.562, 0.716, 0.873, 1.010, 1.307, 1.578, 1.894]⟩

def second : Data := ⟨0.169, 0.524, 0.9365, [0.335, 1.191]⟩

def Data.gap (v : Data) : ℚ :=
  primitiveAt v.t 0 (coefficients v.B v.t v.roots) - primitiveAt v.a 0 (coefficients v.B v.t v.roots)

noncomputable def Data.G (v : Data) := primitive v.B v.t v.roots

theorem first_gap : (1:ℚ)/10^10 < first.gap := by decide +kernel
theorem second_gap : (1:ℚ)/10^5 < second.gap := by decide +kernel

theorem Data.gap_eq (v : Data) : (v.gap:ℝ) = v.G v.t - v.G v.a := by
  simp only [Data.gap, Rat.cast_sub, primitiveAt_cast, Data.G, primitive]

theorem Data.monotonicity (v : Data) (hBt : (v.B:ℝ) ≤ v.t) :
    MonotoneOn v.G (Set.Iic v.B) ∧ AntitoneOn v.G (Set.Icc v.B v.t) ∧ MonotoneOn v.G (Set.Ici v.t) := by
  have hD := primitive_derivative v.B v.t v.roots
  have hdiff : Differentiable ℝ v.G := fun x => (hD x).differentiableAt
  refine ⟨monotoneOn_of_deriv_nonneg (convex_Iic _) hdiff.continuous.continuousOn hdiff.differentiableOn ?_,
    antitoneOn_of_deriv_nonpos (convex_Icc _ _) hdiff.continuous.continuousOn hdiff.differentiableOn ?_,
    monotoneOn_of_deriv_nonneg (convex_Ici _) hdiff.continuous.continuousOn hdiff.differentiableOn ?_⟩
  · intro x hx
    have h : x ≤ v.B := interior_subset hx
    rw [Data.G, (hD x).deriv]
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (h.trans hBt))) (sq_nonneg _)
  · intro x hx
    have h : (v.B:ℝ) ≤ x ∧ x ≤ v.t := interior_subset hx
    rw [Data.G, (hD x).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h.1) (sub_nonneg.mpr h.2)) (sq_nonneg _)
  · intro x hx
    have h : (v.t:ℝ) ≤ x := interior_subset hx
    rw [Data.G, (hD x).deriv]
    exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hBt.trans h)) (sub_nonpos.mpr h))
      (sq_nonneg _)

noncomputable def Data.weightedSum (v : Data) (z : ℕ → ℝ) (f : ℕ → ℕ) (d : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (d+1), f k • (v.G (z (k+1))-v.G (z k))

theorem Data.reflected (v : Data) (haB : v.a ≤ v.B) (hBt : v.B ≤ v.t) (hg : 0 ≤ v.gap)
    {f : ℕ → ℕ} {d i j M : ℕ} (hu : UnimodalOn f 0 d) (hij : i < j) (hjd : j ≤ d)
    (hM : ∀ k ≤ d, f k ≤ M) (z : ℕ → ℝ) (hz : Monotone z)
    (hi : z i ≤ v.a) (hj : z j ≤ v.B) (hneg : v.weightedSum z f d < 0) : f i ≤ f j := by
  have ha : (v.a:ℝ) ≤ v.B := by exact_mod_cast haB
  obtain ⟨left, middle, right⟩ := v.monotonicity (by exact_mod_cast hBt)
  have hgap : v.G v.a ≤ v.G v.t := by
    have hp : (0:ℝ) ≤ v.gap := by exact_mod_cast hg
    rwa [v.gap_eq, sub_nonneg] at hp
  apply reflected_of_negative_sum hu hij hjd hM (fun k => v.G (z k)) _ _ hneg
  · intro l r hlr hr
    exact left ((hz (hlr.trans hr)).trans hj) ((hz hr).trans hj) (hz hlr)
  · intro l r hl hr _
    have hla := (hz hl).trans hi
    have hlr := hz (by omega : l ≤ r)
    by_cases hsmall : z r ≤ (v.B:ℝ)
    · exact left (hla.trans ha) hsmall hlr
    · refine (left (hla.trans ha) ha hla).trans (hgap.trans ?_)
      rcases le_total (v.t:ℝ) (z r) with h | h
      · exact right le_rfl h h
      · exact middle ⟨le_of_not_ge hsmall,h⟩ ⟨by exact_mod_cast hBt,le_rfl⟩ h

/-- Here z gives the left cell boundaries. The center condition of the
research proof implies the displayed threshold for those left boundaries. -/
theorem reflected_from_two_witnesses {f : ℕ → ℕ} {d i j M : ℕ} (hu : UnimodalOn f 0 d)
    (hij : i < j) (hjd : j ≤ d) (hM : ∀ k ≤ d, f k ≤ M) (z : ℕ → ℝ) (hz : Monotone z)
    (h0 : 0 ≤ z i) (hcut : z i + z j ≤ 0.524)
    (h₁ : first.weightedSum z f d < 0) (h₂ : second.weightedSum z f d < 0) : f i ≤ f j := by
  have hi := hz hij.le
  by_cases h : z j ≤ 0.355
  · apply first.reflected (by decide +kernel) (by decide +kernel)
      ((by decide +kernel : (0:ℚ) ≤ 1/10^10).trans first_gap.le) hu hij hjd hM z hz _ _ h₁
    · norm_num [first]; linarith
    · simpa [first] using h
  · apply second.reflected (by decide +kernel) (by decide +kernel)
      ((by decide +kernel : (0:ℚ) ≤ 1/10^5).trans second_gap.le) hu hij hjd hM z hz _ _ h₂
    · norm_num [second]; linarith
    · norm_num [second]; linarith

end CentralUnimodality.Witness
