module

public import CentralUnimodality.NormalizedCells

/-! The reciprocal-size polynomial for a moment of the signed half-area
at its lattice site. Even orders give the moments in its cosine transform. -/
@[expose] public section

namespace CentralUnimodality.Witness
open Laurent

def halfAreaSite (n δ i : ℕ) : ℚ :=
  ((n*(n+δ)-i:ℕ):ℚ)+(3*((n+δ:ℕ):ℚ)/2+(1-(δ:ℚ))/2)

def rawPoint (n δ r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n*(n+δ)+1), (rankCount (2*n+δ) i:ℚ)*(halfAreaSite n δ i)^r

noncomputable def pointMoment (n δ r : ℕ) : ℝ :=
  (rawPoint n δ r:ℝ)/((massFactor n δ:ℝ)*(cellScale (n+δ))^r)

def pointNumerator (δ : ℕ) (P : ℕ → Laurent) (r : ℕ) : Laurent :=
  sumRange (fun j => scaleShift (r.choose j) 0 (translate ((1-(δ:ℚ))/2) (P j) (r-j))) (r+1)

theorem pointNumerator_exact {n δ r : ℕ} {P : ℕ → Laurent}
    (h : ∀ j≤r, (rankMoment n δ j:ℚ)=massFactor n δ*ratioSum (n+δ) (P j)) :
    rawPoint n δ r=massFactor n δ*ratioSum (n+δ) (pointNumerator δ P r) := by
  let shift := 3*((n+δ:ℕ):ℚ)/2+(1-(δ:ℚ))/2
  let f := fun j => (r.choose j:ℚ)*shift^(r-j)
  have hpoint (x : ℚ) : (x+shift)^r=∑ j ∈ Finset.range (r+1), f j*x^j := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]; ring
  unfold rawPoint halfAreaSite
  change (∑ i ∈ Finset.range _, _*(_+shift)^r)=_
  simp_rw [hpoint]
  rw [pointNumerator,ratioSum_sumRange]
  simp only [ratioSum_scale,ratioSum_translate,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := h j (by simpa using Finset.mem_range.mp hj)
  simp only [rankMoment,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow] at hm
  calc
    _ = f j*(∑ i ∈ Finset.range (n*(n+δ)+1),
        (rankCount (2*n+δ) i:ℚ)*((n*(n+δ)-i:ℕ):ℚ)^j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    _ = _ := by rw [hm]; dsimp [f,shift]; ring

def pointPolynomial (m δ r : ℕ) : Option (List ℚ) :=
  let T := tables m
  polynomialFromCell (pointNumerator δ (rawNumerator (lookup T.1) (lookup T.2) δ) r) r

theorem pointPolynomial_exact {n δ m r : ℕ} (hδ : δ≤1) (hn : 0<n+δ) (hr : r≤m)
    {p : List ℚ} (h : pointPolynomial m δ r=some p) :
    pointMoment n δ r=(if r%2=0 then 1 else wallisFactor (n+δ))*horner ((n+δ:ℕ):ℝ)⁻¹ p := by
  apply normalized_from_numerator hn _ _ h
  exact pointNumerator_exact (fun j hj => rawNumerator_exact m n δ j hδ (hj.trans hr))

end CentralUnimodality.Witness
