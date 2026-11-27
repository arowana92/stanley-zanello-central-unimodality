module

public import CentralUnimodality.CellVerifier
public import CentralUnimodality.TaylorDigits
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.ComputeDegree

/-! The endpoint numerator for a cell moment is a polynomial in the rank.
Newton expansion reduces the exact sample calculation to at most 22
binomial moments, independently of the length of the rank distribution. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open Polynomial
open scoped fwdDiff

def diffAtZero (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k+1), (-1:ℤ)^(k-i)*(k.choose i)* f i

private theorem diffAtZero_eq (P : ℤ[X]) (k : ℕ) :
    diffAtZero (fun j => P.eval j) k = (fwdDiff 1)^[k] P.eval 0 := by
  simp [diffAtZero,fwdDiff_iter_eq_sum_shift]

theorem newton_bounded (P : ℤ[X]) (d j : ℕ) (hd : P.natDegree ≤ d) :
    P.eval (j:ℤ) = ∑ k ∈ Finset.range (d+1), (j.choose k:ℤ)*diffAtZero (fun x => P.eval x) k := by
  have h := shift_eq_sum_fwdDiff_iter (1:ℤ) P.eval j 0
  simp only [nsmul_eq_mul,mul_one,zero_add] at h
  simp_rw [diffAtZero_eq]
  rw [h]
  rcases le_total j d with hj | hj
  · apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    have hlt : j < k := by simpa using hk
    simp [Nat.choose_eq_zero_of_lt hlt]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    have hlt : P.natDegree < k := by
      simp only [Finset.mem_range,not_lt] at hk
      omega
    simp [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hlt]

def endpointValue (top r j : ℕ) : ℤ :=
  ((top:ℤ)-2*j+2)^(r+1)-((top:ℤ)-2*j)^(r+1)

private noncomputable def endpointPoly (top r : ℕ) : ℤ[X] :=
  (C (top:ℤ)-C 2*X+C 2)^(r+1) - (C (top:ℤ)-C 2*X)^(r+1)

private theorem eval_endpoint (top r j : ℕ) :
    (endpointPoly top r).eval (j:ℤ) = endpointValue top r j := by
  simp [endpointPoly,endpointValue]

private theorem degree_endpoint (top r : ℕ) : (endpointPoly top r).natDegree ≤ r+1 := by
  unfold endpointPoly
  compute_degree

def cellTop (n δ : ℕ) := 2*(n*(n+δ)) + (3*(n+δ)-δ)

private theorem endpointValue_cell {n δ j : ℕ} (hj : j ≤ n*(n+δ)) (r : ℕ) :
    endpointValue (cellTop n δ) r j =
      (((twiceLeft n δ j+2)^(r+1) - (twiceLeft n δ j)^(r+1) : ℕ):ℤ) := by
  have he : ((twiceLeft n δ j:ℕ):ℤ) = (cellTop n δ:ℤ)-2*j := by
    simp only [twiceLeft,cellTop,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hj]
    ring
  have hpos := Nat.pow_le_pow_left (by omega : twiceLeft n δ j ≤ twiceLeft n δ j+2) (r+1)
  simp only [endpointValue,Nat.cast_sub hpos,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,he]

theorem binomial_cell (n δ r : ℕ) (hδ : δ ≤ 1) :
    (momentInt (rankCells n δ) r:ℤ) =
      ∑ k ∈ Finset.range (r+2), (binomialMoment (2*n+δ) k:ℤ)*diffAtZero (endpointValue (cellTop n δ) r) k := by
  let f := endpointValue (cellTop n δ) r
  have hpt (j : ℕ) : f j = ∑ k ∈ Finset.range (r+2), (j.choose k:ℤ)*diffAtZero f k := by
    simpa only [eval_endpoint] using newton_bounded (endpointPoly (cellTop n δ) r) (r+1) j
      (degree_endpoint ..)
  have hs := sum_over_ranks f n δ hδ
  have hsum : (momentInt (rankCells n δ) r:ℤ) =
      ∑ j ∈ Finset.range (n*(n+δ)+1), rankCount (2*n+δ) j • f j := by
    have hlist (g : ℕ → ℕ) (D : ℕ) : ((List.range D).map g).sum = ∑ i ∈ Finset.range D, g i := by
      induction D with
      | zero => simp
      | succ D ih => simp [List.range_succ,Finset.sum_range_succ,ih]
    simp only [momentInt,rankCells,List.map_map,Function.comp_def,hlist,Nat.cast_sum,
      Nat.cast_mul,packedRow_digit _ _ _ (Nat.lt_succ_self _),nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show f j = _ from endpointValue_cell (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) r]
  rw [hsum,← hs]
  simp_rw [hpt,Finset.sum_comm (s := allPartitions (2*n+δ)),binomialMoment,Nat.cast_sum,Finset.sum_mul]
  rfl

end CentralUnimodality.Laurent
