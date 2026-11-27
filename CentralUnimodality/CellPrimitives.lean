module

public import CentralUnimodality.WitnessSigns

/-! The witness expectation equals the sum of primitive differences at the
actual cell boundaries, up to the positive mass and scale factors. -/
@[expose] public section

namespace CentralUnimodality.Witness

open Laurent

def leftEndpoint (n δ k : ℕ) : ℚ := k + (3*((n+δ:ℕ):ℚ)/2+(-(δ:ℚ)/2))

noncomputable def boundary (n δ k : ℕ) : ℝ := (leftEndpoint n δ k:ℝ)/cellScale (n+δ)

private theorem leftEndpoint_succ (n δ k : ℕ) :
    leftEndpoint n δ (k+1) = leftEndpoint n δ k+1 := by simp [leftEndpoint]; ring

private noncomputable def integrateRow (n δ : ℕ) (G : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n*(n+δ)+1), (rankCount (2*n+δ) i:ℝ) *
    (G (boundary n δ (n*(n+δ)-i+1))-G (boundary n δ (n*(n+δ)-i)))

private theorem integrateRow_add (n δ : ℕ) (G H : ℝ → ℝ) :
    integrateRow n δ (fun x => G x+H x) = integrateRow n δ G + integrateRow n δ H := by
  unfold integrateRow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem integrateRow_scale (n δ : ℕ) (c : ℝ) (G : ℝ → ℝ) :
    integrateRow n δ (fun x => c*G x) = c*integrateRow n δ G := by
  unfold integrateRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem integrateRow_monomial (n δ r : ℕ) (hn : 0 < n+δ) :
    integrateRow n δ (fun z => z^(r+1)/((r:ℝ)+1)) =
      (massFactor n δ:ℝ)/cellScale (n+δ)*normalizedCell n δ r := by
  have hs : cellScale (n+δ) ≠ 0 := (cellScale_pos hn).ne'
  have hm : (massFactor n δ:ℝ) ≠ 0 := by exact_mod_cast (massFactor_pos n δ).ne'
  rw [normalizedCell]
  calc
    _ = (rawCell n δ r:ℝ)/(cellScale (n+δ))^(r+1) := by
      simp only [rawCell,integrateRow,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast]
      rw [div_eq_mul_inv,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      change _ = (rankCount (2*n+δ) i:ℝ) * (cellPower (leftEndpoint n δ (n*(n+δ)-i)) r:ℚ) *
        (cellScale (n+δ)^(r+1))⁻¹
      simp only [cellPower,boundary,leftEndpoint_succ,Rat.cast_div,Rat.cast_sub,Rat.cast_pow,
        Rat.cast_add,Rat.cast_one,Rat.cast_natCast,div_pow]
      ring
    _ = _ := by rw [pow_succ]; field_simp

private theorem integrateRow_primitive (n δ : ℕ) (hn : 0 < n+δ) (cs : List ℚ) (r : ℕ) :
    integrateRow n δ (fun z => primitiveAt z r cs) =
      (massFactor n δ:ℝ)/cellScale (n+δ)* polyExpectation (normalizedCell n δ) r cs := by
  induction cs generalizing r with
  | nil => simp [integrateRow,primitiveAt,polyExpectation]
  | cons c cs ih =>
    have he (z : ℝ) : primitiveAt z r (c::cs) =
        (c:ℝ)*(z^(r+1)/((r:ℝ)+1)) + primitiveAt z (r+1) cs := by rw [primitiveAt]; ring
    simp_rw [he]
    rw [integrateRow_add,integrateRow_scale,integrateRow_monomial n δ r hn,ih,polyExpectation]
    ring

theorem weightedSum_expectation (v : Data) (n δ : ℕ) (hn : 0 < n+δ) :
    v.weightedSum (boundary n δ) (fun k => rankCount (2*n+δ) (n*(n+δ)-k)) (n*(n+δ)) =
      (massFactor n δ:ℝ)/cellScale (n+δ)*
        polyExpectation (normalizedCell n δ) 0 (coefficients v.B v.t v.roots) := by
  rw [← integrateRow_primitive n δ hn]
  let D := n*(n+δ)
  let f (k : ℕ) := (rankCount (2*n+δ) (D-k):ℝ) * (v.G (boundary n δ (k+1))-v.G (boundary n δ k))
  change (∑ k ∈ Finset.range (D+1), rankCount (2*n+δ) (D-k) •
      (v.G (boundary n δ (k+1))-v.G (boundary n δ k))) = _
  simp only [nsmul_eq_mul]
  change (∑ k ∈ Finset.range (D+1), f k) = _
  rw [← Finset.sum_range_reflect f (D+1)]
  apply Finset.sum_congr rfl
  intro i hi
  have h := Finset.mem_range.mp hi
  change (rankCount (2*n+δ) (D-(D+1-1-i)):ℝ)*_ = (rankCount (2*n+δ) i:ℝ)*_
  rw [show D+1-1 = D by omega,show D-(D-i) = i by omega]
  rfl

end CentralUnimodality.Witness
