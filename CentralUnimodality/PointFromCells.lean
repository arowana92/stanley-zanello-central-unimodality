module

public import CentralUnimodality.PointMoments

/-! Recover point moments by removing the uniform width-one cell about
each lattice site. The coefficient on the current point moment is one. -/
@[expose] public section

namespace CentralUnimodality.Witness
open Laurent

def boxTerm (r j : ℕ) : ℚ :=
  ((r+1).choose j:ℚ)*((1/2:ℚ)^(r+1-j)-(-1/2:ℚ)^(r+1-j))/((r:ℚ)+1)

theorem boxTerm_self (r : ℕ) : boxTerm r r=1 := by
  simp [boxTerm]
  field_simp
  norm_num

private theorem centered_box (x : ℚ) (r : ℕ) :
    cellPower (x-1/2) r=∑ j ∈ Finset.range (r+1), boxTerm r j*x^j := by
  rw [cellPower,show x-1/2+1=x+1/2 by ring,show x-1/2=x+(-1/2) by ring,
    add_pow,add_pow,← Finset.sum_sub_distrib,Finset.sum_range_succ]
  simp only [Nat.sub_self,pow_zero,mul_one,sub_self,add_zero]
  rw [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [boxTerm]
  ring

theorem cell_point_moments (n δ r : ℕ) :
    rawCell n δ r=∑ j ∈ Finset.range (r+1), boxTerm r j*rawPoint n δ j := by
  have shift (i : ℕ) : ((n*(n+δ)-i:ℕ):ℚ)+(3*((n+δ:ℕ):ℚ)/2+(-(δ:ℚ)/2))=
      halfAreaSite n δ i-1/2 := by dsimp [halfAreaSite]; ring
  simp only [rawCell,shift,centered_box,rawPoint,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

def pointsFromCells (C : Array Laurent) : ℕ → Array Laurent
  | 0 => #[]
  | r+1 =>
    let A := pointsFromCells C r
    A.push (add (sumRange (fun j => scaleShift (-boxTerm r j) 0 (lookup A j)) r) (lookup C r))

private theorem points_size (C : Array Laurent) (r : ℕ) : (pointsFromCells C r).size=r := by
  induction r <;> simp [pointsFromCells, *]

theorem recovered_points {n δ : ℕ} (C : Array Laurent) (m : ℕ)
    (hc : ∀ j<m, rawCell n δ j=massFactor n δ*ratioSum (n+δ) (lookup C j)) :
    ∀ j<m, rawPoint n δ j=massFactor n δ*ratioSum (n+δ) (lookup (pointsFromCells C m) j) := by
  induction m with
  | zero => omega
  | succ r ih =>
    have prev := ih (fun j hj => hc j (by omega))
    intro j hj
    let A := pointsFromCells C r
    have sizeA : A.size=r := points_size C r
    by_cases hit : j=r
    · subst j
      rw [pointsFromCells]
      let R := add (sumRange (fun i => scaleShift (-boxTerm r i) 0 (lookup A i)) r) (lookup C r)
      change rawPoint n δ r=massFactor n δ*ratioSum (n+δ) (lookup (A.push R) r)
      have endVal : lookup (A.push R) r=R := by rw [← sizeA,lookup,Array.getElem?_push_size]; rfl
      rw [endVal]
      dsimp only [R]
      rw [ratioSum_add,ratioSum_sumRange,mul_add,← hc r (by omega),cell_point_moments,
        Finset.sum_range_succ,boxTerm_self,one_mul,Finset.mul_sum]
      have corr : (∑ i ∈ Finset.range r, massFactor n δ*
          ratioSum (n+δ) (scaleShift (-boxTerm r i) 0 (lookup A i))) =
          -(∑ i ∈ Finset.range r, boxTerm r i*rawPoint n δ i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [ratioSum_scale,prev i (Finset.mem_range.mp hi)]
        dsimp only [A]; ring
      rw [corr]; ring
    · have lt : j<r := by omega
      have ltA : j<A.size := by rwa [sizeA]
      change rawPoint n δ j=massFactor n δ*ratioSum (n+δ) (lookup (A.push _) j)
      simp only [lookup,Array.getElem?_push_lt ltA]
      have p : rawPoint n δ j=massFactor n δ*ratioSum (n+δ) (lookup A j) := prev j lt
      simpa only [lookup,getElem?_pos A j ltA] using p

end CentralUnimodality.Witness
