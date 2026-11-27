module

public import CentralUnimodality.FourierResidual
public import CentralUnimodality.Survival
public import Mathlib.Analysis.Complex.Trigonometric

/-! At frequency ω for the integer sum of heights, the signed strict transform
is exactly the cosine transform of the shifted staircase coranks, and the free
input is a product of cosines. For the half-area use ω = θ/2. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

noncomputable def areaCharacter (ω : ℝ) (a : ℤ) : ℂ :=
  Complex.exp (((ω * (a:ℝ) : ℝ):ℂ) * Complex.I)

theorem areaCharacter_zero (ω : ℝ) : areaCharacter ω 0 = 1 := by simp [areaCharacter]

theorem areaCharacter_add (ω : ℝ) (a b : ℤ) :
    areaCharacter ω (a+b) = areaCharacter ω a * areaCharacter ω b := by
  simp [areaCharacter, mul_add, add_mul, Complex.exp_add]

theorem norm_areaCharacter (ω : ℝ) (a : ℤ) : ‖areaCharacter ω a‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem areaCharacter_pair (ω : ℝ) (a : ℤ) :
    areaCharacter ω a + areaCharacter ω (-a) = 2*(Real.cos (ω*a) : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  simp only [areaCharacter, Int.cast_neg, mul_neg, Complex.ofReal_neg]
  ring

theorem fourier_signed_ranks (ω : ℝ) (n δ : ℕ) (hδ : δ ≤ 1) :
    coeff (2*n+δ+1) (fairSeries (areaCharacter ω) strictWords) =
      (2:ℂ)⁻¹^(2*n+δ+1) * ∑ j ∈ Finset.range (n*(n+δ)+1),
        rankCount (2*n+δ) j • (2 * (Real.cos (ω * signedAreaAtRank n δ j) : ℂ)) := by
  rw [coeff_walkSeries, signed_ranks _ n δ hδ]
  simp only [areaCharacter_pair]

/-- Summing over the leading sign adds the two character values of its weight. -/
theorem free_step {R : Type*} [CommSemiring R] (χ : ℤ → R)
    (hχ : ∀ x y, χ (x+y) = χ x * χ y) (n : ℕ) :
    (∑ w ∈ words (n+1), χ (walkArea w)) =
      (∑ w ∈ words n, χ (walkArea w)) * (χ (n+1) + χ (-(n+1:ℤ))) := by
  have dis : Disjoint ((words n).image (false :: ·)) ((words n).image (true :: ·)) := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨v, _, h⟩ := Finset.mem_image.mp h₂
    exact Bool.noConfusion (List.cons.inj h).1
  have inj (b : Bool) : Function.Injective (b :: · : List Bool → List Bool) :=
    fun _ _ he => (List.cons.inj he).2
  rw [words, Finset.sum_union dis, Finset.sum_image (inj false).injOn, Finset.sum_image (inj true).injOn,
    mul_add, Finset.sum_mul, Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro w hw <;>
    simp [walkArea_cons, step, hχ, mem_words.mp hw]

theorem fourier_free_product (ω : ℝ) (n : ℕ) :
    coeff n (fairSeries (areaCharacter ω) words) =
      ∏ i ∈ Finset.range n, (Real.cos (ω*(i+1)) : ℂ) := by
  induction n with
  | zero => simp [coeff_walkSeries, words, walkArea, heights, areaCharacter_zero]
  | succ n ih =>
    rw [coeff_walkSeries] at ih ⊢
    rw [Finset.prod_range_succ, free_step _ (areaCharacter_add ω), areaCharacter_pair, ← ih, pow_succ]
    push_cast
    ring

end CentralUnimodality
