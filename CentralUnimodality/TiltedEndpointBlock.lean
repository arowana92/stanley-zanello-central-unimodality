module

public import CentralUnimodality.PairProbabilityRange
public import CentralUnimodality.StoppedPrefixVariance

/-! Pair the two halves of a tilted sign block at fixed rank-label
spacing. An arbitrary restriction of the paths, including a ballot wall,
retains at most half of one plus the unrestricted endpoint norm bound. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Polynomial

noncomputable def endpointAtom (c u a θ : ℝ) (w : List Bool) : Polynomial ℂ :=
  monomial (wordParts w).length ((signMass c u w:ℂ)*phase (θ*prefixRank a w))

/-- The exponent records the number of down-steps. For fixed block length
and starting height this is equivalent to recording its final height. -/
noncomputable def endpointRow (c u a θ : ℝ) (A : Finset (List Bool)) := ∑ w ∈ A, endpointAtom c u a θ w

theorem endpointRow_coeff (c u a θ : ℝ) (A : Finset (List Bool)) (k : ℕ) :
    (endpointRow c u a θ A).coeff k =
      ∑ w ∈ A, if (wordParts w).length=k then (signMass c u w:ℂ)*phase (θ*prefixRank a w) else 0 := by
  simp [endpointRow,endpointAtom,Finsupp.single_apply]

theorem endpointRow_mass (c u a θ : ℝ) (A : Finset (List Bool)) :
    endpointNorm (endpointRow c u a θ A) ≤ ∑ w ∈ A, signMass c u w := by
  apply (endpointNorm_sum ..).trans_eq
  apply Finset.sum_congr rfl
  intro w _
  simp only [endpointAtom,endpointNorm_monomial,norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (signMass_pos ..)]

private theorem atom_cons (c u a θ : ℝ) (b : Bool) (w : List Bool) :
    endpointAtom c u a θ (b::w) =
      (if b then monomial 1 ((upChance (-u):ℂ)*phase (θ*a)) else monomial 0 (upChance u:ℂ)) *
      endpointAtom c (u-c) (a-1) θ w := by
  cases b <;> simp [endpointAtom,signMass,upChance,wordParts,prefixRank,step,monomial_mul_monomial,
    mul_add,phase_add,mul_left_comm,mul_comm,mul_assoc]

theorem endpointRow_product (c u a θ : ℝ) (n : ℕ) :
    endpointRow c u a θ (words n) = ∏ i ∈ Finset.range n, signFactor (upChance (-(u-c*i))) (θ*(a-i)) := by
  induction n generalizing u a with
  | zero => simp [endpointRow,endpointAtom,words,signMass,wordParts,prefixRank]
  | succ n ih =>
    rw [endpointRow,sum_cons_words]
    simp only [atom_cons,Bool.false_eq_true,ite_false,ite_true,← Finset.mul_sum,← add_mul]
    change (_+_)*endpointRow c (u-c) (a-1) θ (words n) = _
    rw [ih,Finset.prod_range_succ']
    simp only [Nat.cast_zero,mul_zero,sub_zero,Nat.cast_succ,mul_add,mul_one]
    rw [mul_comm]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      rw [show u-c-c*(i:ℝ)=u-(c*i+c) by ring,show a-1-(i:ℝ)=a-(i+1) by ring]
    · unfold signFactor; rw [show 1-upChance (-u)=upChance u by linarith only [up_total u]]

/-- Group corresponding positions in the two equal halves before taking
the endpoint norm. The loss depends only on their common label spacing. -/
theorem free_paired_block (c u a θ : ℝ) (l : ℕ) {w : ℝ} (hw : 0 ≤ w)
    (hp : ∀ i ∈ Finset.range l,
      let p := upChance (-(u-c*i))
      let q := upChance (-(u-c*(l+i:ℕ)))
      w*(p*(1-q)+(1-p)*q) ≤ 2*(p*(1-q))*((1-p)*q)) :
    endpointNorm (endpointRow c u a θ (words (2*l))) ≤ exp (-w*l*sin (l*θ/2)^2) := by
  let p (i : ℕ) := upChance (-(u-c*i))
  let F (i : ℕ) := signFactor (p i) (θ*(a-i))
  have H (i : ℕ) : 0 < p i ∧ p i < 1 := by
    have h (z : ℝ) : 0 < upChance z := by unfold upChance; positivity
    refine ⟨h _,?_⟩; dsimp only [p]; linarith only [up_total (u-c*i),h (u-c*i)]
  rw [endpointRow_product,two_mul]
  change endpointNorm (∏ i ∈ Finset.range (l+l), F i) ≤ _
  rw [Finset.prod_range_add,← Finset.prod_mul_distrib]
  apply (endpointNorm_prod ..).trans
  have per (i : ℕ) (hi : i ∈ Finset.range l) :
      endpointNorm (F i*F (l+i)) ≤ exp (-w*sin (l*θ/2)^2) := by
    have hp' := H i
    have hq' := H (l+i)
    have hz : 0 < p i*(1-p (l+i))+(1-p i)*p (l+i) := by
      exact add_pos (mul_pos hp'.1 (sub_pos.mpr hq'.2)) (mul_pos (sub_pos.mpr hp'.2) hq'.1)
    apply (weighted_pair_bound hp'.1.le hp'.2.le hq'.1.le hq'.2.le hw (hp i hi) hz _ _).trans_eq
    rw [Nat.cast_add]; congr 4; ring
  apply (Finset.prod_le_prod₀ (fun _ _ => endpointNorm_nonneg _) per).trans_eq
  rw [Finset.prod_const,Finset.card_range,← exp_nat_mul]; congr 1; ring

/-- The restricted row has its own mass as a bound. It also equals the
unrestricted row less the omitted row, whose norm is at most the omitted mass. -/
theorem retained_row (c u a θ : ℝ) {n : ℕ} (A : Finset (List Bool)) (hA : A ⊆ words n) {ρ : ℝ}
    (hρ : endpointNorm (endpointRow c u a θ (words n)) ≤ ρ) :
    endpointNorm (endpointRow c u a θ A) ≤ (1+ρ)/2 := by
  let B := words n \ A
  have addrow : endpointRow c u a θ B+endpointRow c u a θ A = endpointRow c u a θ (words n) :=
    Finset.sum_sdiff hA
  have addmass : (∑ w ∈ B, signMass c u w)+(∑ w ∈ A, signMass c u w)=1 :=
    (Finset.sum_sdiff hA).trans (signMass_total ..)
  have hneg (P : Polynomial ℂ) : endpointNorm (-P)=endpointNorm P := by
    simp [endpointNorm]
  have he : endpointRow c u a θ A=endpointRow c u a θ (words n)+ -endpointRow c u a θ B := by rw [← addrow]; abel
  have hh := endpointNorm_add (endpointRow c u a θ (words n)) (-endpointRow c u a θ B)
  rw [← he,hneg] at hh
  linarith only [hh,hρ,endpointRow_mass c u a θ A,endpointRow_mass c u a θ B,addmass]

/-- The .20 and .12 losses for an actual tilted block with any path
restriction. In particular A can be survival from any prescribed height. -/
theorem tilted_retained_pair (c u a θ : ℝ) (l : ℕ) (A : Finset (List Bool)) (hA : A ⊆ words (2*l)) :
    let p := fun i : ℕ => upChance (-(u-c*i))
    ((∀ i < 2*l, 9/25 ≤ p i ∧ p i ≤ 31/50) →
      endpointNorm (endpointRow c u a θ A) ≤ (1+exp (-(1/5)*l*sin (l*θ/2)^2))/2) ∧
    ((∀ i < 2*l, 11/50 ≤ p i ∧ p i ≤ 17/25) →
      endpointNorm (endpointRow c u a θ A) ≤ (1+exp (-(3/25)*l*sin (l*θ/2)^2))/2) := by
  constructor <;> intro hp
  · apply retained_row c u a θ A hA (free_paired_block c u a θ l (by norm_num) _)
    intro i hi; have h := Finset.mem_range.mp hi
    exact (pair_probability_ranges ..).1 (hp i (by omega)) (hp (l+i) (by omega))
  · apply retained_row c u a θ A hA (free_paired_block c u a θ l (by norm_num) _)
    intro i hi; have h := Finset.mem_range.mp hi
    exact (pair_probability_ranges ..).2 (hp i (by omega)) (hp (l+i) (by omega))

end CentralUnimodality.MarkedExcursion
