module

public import CentralUnimodality.MomentPivots
import Mathlib.Tactic.LinearCombination

/-! At every requested order the triangular Laurent construction satisfies the
original moment equations. Together with coefficient extraction, this gives
exact moments for both staircase families at arbitrary size and order. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

private structure Correct (m : ℕ) (D B : Array Laurent) : Prop where
  sizeD : D.size = m+1
  sizeB : B.size = m+1
  zeroD : eval (lookup D 0) = 1
  zeroB : eval (lookup B 0) = 1
  dyck : ∀ i ≤ m, eval (lookup D i) = eval (dyckRhs (lookup D) i)
  ballot : ∀ i ≤ m, eval (mul alpha (lookup B i)) = eval (ballotRhs (lookup D) (lookup B) i)

private theorem lookup_push_below {A : Array Laurent} {i : ℕ} (hi : i < A.size) (p : Laurent) :
    lookup (A.push p) i = lookup A i := by simp only [lookup, Array.getElem?_push_lt hi, getElem?_pos A i hi]

private theorem pivot_solution {A : Array Laurent} {r : ℕ} (hs : A.size = r) (p : Laurent) :
    catalanRoot * eval (lookup (A.push (scaleShift 1 (-1) p)) r) = eval p := by
  subst r
  rw [lookup, Array.getElem?_push_size]
  simp [eval_scaleShift,rootPower_neg_one,← mul_assoc,catalanRoot_mul_ballotBase]

private theorem correct_succ {m : ℕ} {D B : Array Laurent} (hc : Correct m D B) :
    let r := m+1
    let D' := D.push (scaleShift 1 (-1) (dyckRhs (lookup D) r))
    let B' := B.push (scaleShift 1 (-1) (ballotRhs (lookup D') (lookup B) r))
    Correct r D' B' := by
  let r := m+1
  let dval := dyckRhs (lookup D) r
  let D' := D.push (scaleShift 1 (-1) dval)
  let bval := ballotRhs (lookup D') (lookup B) r
  let B' := B.push (scaleShift 1 (-1) bval)
  change Correct r D' B'
  have hr : 0 < r := Nat.zero_lt_succ _
  have hD : ∀ i < r, lookup D' i = lookup D i := fun _ hi => lookup_push_below (hc.sizeD ▸ hi) _
  have hB : ∀ i < r, lookup B' i = lookup B i := fun _ hi => lookup_push_below (hc.sizeB ▸ hi) _
  have hd0 : lookup D r = [] := by simp [lookup, ← hc.sizeD, r]
  have hb0 : lookup B r = [] := by simp [lookup, ← hc.sizeB, r]
  have hz := (congrArg eval (hD 0 hr)).trans hc.zeroD
  refine ⟨by simp [D',r,hc.sizeD], by simp [B',r,hc.sizeB], hz,
    (congrArg eval (hB 0 hr)).trans hc.zeroB, ?_, ?_⟩
  · intro i hi
    rcases hi.eq_or_lt with rfl | hi
    · have he := dyckRhs_difference hr hD hc.zeroD
      simp only [hd0,eval,sub_zero] at he
      have hp : catalanRoot*eval (lookup D' r) = eval (dyckRhs (lookup D) r) :=
        pivot_solution (A := D) (r := r) hc.sizeD dval
      linear_combination -he + hp + eval (lookup D' r)*beta_pivot
    · rw [hD i hi, dyckRhs_congr (fun j hj => hD j (hj.trans_lt hi))]
      exact hc.dyck i (by dsimp [r] at hi; omega)
  · intro i hi
    rcases hi.eq_or_lt with rfl | hi
    · have he := ballotRhs_difference (lookup D') hr hB hz
      simp only [hb0,eval,sub_zero] at he
      have hp : catalanRoot*eval (lookup B' r) = eval (ballotRhs (lookup D') (lookup B) r) :=
        pivot_solution (A := B) (r := r) hc.sizeB bval
      rw [eval_mul]
      linear_combination -he + hp + eval (lookup B' r)*alpha_add_beta + eval (lookup B' r)*beta_pivot
    · rw [hB i hi, ballotRhs_congr (fun j hj => hD j (hj.trans_lt hi)) (fun j hj => hB j (hj.trans_lt hi))]
      exact hc.ballot i (by dsimp [r] at hi; omega)

private theorem tables_correct (m : ℕ) : Correct m (tables m).1 (tables m).2 := by
  induction m with
  | zero =>
    have h : tableCheck (tables 0).1 (tables 0).2 0 = true := by decide +kernel
    simp only [tableCheck,Bool.and_eq_true] at h
    refine ⟨rfl,rfl,?_,?_,?_,?_⟩
    · change eval [(0,1)] = 1
      simp [eval,rootPower_zero]
    · change eval [(0,1)] = 1
      simp [eval,rootPower_zero]
    · intro i hi
      obtain rfl : i = 0 := by omega
      exact eval_eq_of_sameValue h.1
    · intro i hi
      obtain rfl : i = 0 := by omega
      exact eval_eq_of_sameValue h.2
  | succ m ih => exact correct_succ ih

theorem tables_exact (m : ℕ) :
    let A := lookup (tables m).1
    let B := lookup (tables m).2
    SameColumns m (model dyckBase A) (dyckSeries (exp ℚ)) ∧
    SameColumns m (model ballotBase B) (evenBallotSeries (exp ℚ)) ∧
    SameColumns m (model (dyckBase*ballotBase) (oddRhs A B)) (oddBallotSeries (exp ℚ)) := by
  have h := tables_correct m
  exact certify_columns m _ _ _ h.dyck h.ballot (fun _ _ => rfl)

/-- Unnormalized r-th corank moment of the odd-part staircase at every size. -/
theorem exact_even_moment (n r : ℕ) :
    (rankMoment n 0 r : ℚ) = r.factorial*(n.centralBinom:ℚ)*
      ratioSum n (evenNumerator (lookup (tables r).2 r)) :=
  extracted_even (tables_exact r).2.1 n r le_rfl

/-- Unnormalized r-th corank moment of the even-part staircase at every size.
The factor of two comes from extracting at semilength n+1. -/
theorem exact_odd_moment (n r : ℕ) :
    2*(rankMoment n 1 r : ℚ) = r.factorial*((n+1).centralBinom:ℚ)*
      ratioSum (n+1) (oddNumerator (oddRhs (lookup (tables r).1) (lookup (tables r).2) r)) :=
  extracted_odd (tables_exact r).2.2 n r le_rfl

end CentralUnimodality.Laurent
