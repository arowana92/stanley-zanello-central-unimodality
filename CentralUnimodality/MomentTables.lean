module

public import CentralUnimodality.MomentCertificate

/-! Generate candidate Laurent columns from the triangular moment equations.
Equality of the original equations, checked independently of how the candidates
were generated, implies the exact all-size moment identities. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

def lookup (A : Array Laurent) (r : ℕ) : Laurent := A[r]?.getD []

def tables : ℕ → Array Laurent × Array Laurent
  | 0 => (#[[(0,1)]], #[[(0,1)]])
  | n+1 =>
    let (D,B) := tables n
    let D' := D.push (scaleShift 1 (-1) (dyckRhs (lookup D) (n+1)))
    let B' := B.push (scaleShift 1 (-1) (ballotRhs (lookup D') (lookup B) (n+1)))
    (D',B')

def sameValue (p q : Laurent) := decide (add p [] = add q [])

theorem eval_eq_of_sameValue {p q : Laurent} (h : sameValue p q = true) : eval p = eval q := by
  have he : add p [] = add q [] := of_decide_eq_true h
  simpa [eval_add,eval] using congrArg eval he

def tableCheck (D B : Array Laurent) (r : ℕ) : Bool :=
  sameValue (lookup D r) (dyckRhs (lookup D) r) &&
    sameValue (mul alpha (lookup B r)) (ballotRhs (lookup D) (lookup B) r)

theorem checked_tables {D B : Array Laurent} {M : ℕ} (h : ∀ r ≤ M, tableCheck D B r = true) :
    SameColumns M (model dyckBase (lookup D)) (dyckSeries (exp ℚ)) ∧
    SameColumns M (model ballotBase (lookup B)) (evenBallotSeries (exp ℚ)) ∧
    SameColumns M (model (dyckBase*ballotBase) (oddRhs (lookup D) (lookup B)))
      (oddBallotSeries (exp ℚ)) := by
  apply certify_columns
  · intro r hr
    have hh := h r hr
    simp only [tableCheck,Bool.and_eq_true] at hh
    exact eval_eq_of_sameValue hh.1
  · intro r hr
    have hh := h r hr
    simp only [tableCheck,Bool.and_eq_true] at hh
    exact eval_eq_of_sameValue hh.2
  · intro r _
    rfl

end CentralUnimodality.Laurent
