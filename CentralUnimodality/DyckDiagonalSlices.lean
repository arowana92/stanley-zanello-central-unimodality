module

public import CentralUnimodality.DyckDiagonalDegree
public import CentralUnimodality.ReflectedPolynomials

/-! Reduce the ordinary Dyck input to the usual symmetric, unimodal
homogeneous slices of the area/dinv polynomial. Only slices actually
attained by a path occur in the sum. -/
@[expose] public section

namespace CentralUnimodality

/-- The q^k t^(d-k) coefficient, counting the original Dyck walks. -/
def dyckSliceCount (n d k : ℕ) : ℕ :=
  ∑ w ∈ (dycks n).filter (fun w => dyckTotalDegree w = d), if walkCorank w = k then 1 else 0

theorem dyck_slice_sum (n k : ℕ) :
    (dyckPoly n).coeff k = ∑ d ∈ (dycks n).image dyckTotalDegree, dyckSliceCount n d k := by
  rw [dyckPoly,corankSum,Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  symm
  unfold dyckSliceCount
  rw [show (fun w => if k = walkCorank w then 1 else (0:ℕ)) =
    (fun w => if walkCorank w = k then 1 else 0) by funext w; by_cases he : k = walkCorank w <;> simp_all [eq_comm]]
  exact Finset.sum_fiberwise_of_maps_to (s := dycks n)
    (fun w hw => Finset.mem_image_of_mem dyckTotalDegree hw)
    (fun w => if walkCorank w = k then 1 else (0:ℕ))

/-- Symmetry and weak increase through the middle of each total degree of
the ordinary area/dinv q,t-Catalan polynomial. -/
def DyckDiagonalUnimodality : Prop :=
  ∀ n d, (∀ k ≤ d, dyckSliceCount n d k = dyckSliceCount n d (d-k)) ∧
    ∀ k, 2*k < d → dyckSliceCount n d k ≤ dyckSliceCount n d (k+1)

theorem dyck_comparisons_of_diagonal_unimodality (h : DyckDiagonalUnimodality) : DyckComparisons := by
  intro n i j hij hsum
  rw [dyck_slice_sum,dyck_slice_sum]
  apply Finset.sum_le_sum
  intro d hd
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hd
  let d := dyckTotalDegree w
  have hcut := dyck_diagonal_cutoff hw
  have hs : i+j ≤ d := by dsimp [d]; omega
  obtain ⟨hsym,hinc⟩ := h n d
  have hmono (a b : ℕ) (hab : a ≤ b) (hb : 2*b ≤ d) : dyckSliceCount n d a ≤ dyckSliceCount n d b := by
    induction b with
    | zero => simp [show a = 0 by omega]
    | succ b ih =>
      by_cases hEq : a = b+1
      · rw [hEq]
      · exact (ih (by omega) (by omega)).trans (hinc b (by omega))
  by_cases hj : 2*j ≤ d
  · exact hmono i j hij.le hj
  · change dyckSliceCount n d i ≤ dyckSliceCount n d j
    rw [hsym j (by omega)]
    exact hmono i (d-j) (by omega) (by omega)

theorem conjecture34_of_diagonal_unimodality_and_midpoints (hd : DyckDiagonalUnimodality)
    (hc : ∀ n ≥ 96, ∀ δ ≤ 1, CentralToMidpoint n δ) : Conjecture34 :=
  conjecture34_of_comparisons_and_midpoints (dyck_comparisons_of_diagonal_unimodality hd) hc

end CentralUnimodality
