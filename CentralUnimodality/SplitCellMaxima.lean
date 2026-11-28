module

public import CentralUnimodality.SplitPairBudgets
public meta import CentralUnimodality.SplitPairBudgets
import Mathlib.Tactic.Eval

/-! Four maxima in each half-unit cell. The maximum is taken
separately for the lattice term and the three derivative terms,
since different splits can attain the four suprema. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit

def PairBudget.join (a b : PairBudget) : PairBudget :=
  ⟨max a.lattice b.lattice,max a.second b.second,max a.third b.third,max a.fourth b.fourth⟩

def PairBudget.test (a b : PairBudget) :=
  decide (a.lattice≤b.lattice) && decide (a.second≤b.second) &&
  decide (a.third≤b.third) && decide (a.fourth≤b.fourth)

def adjacentBudget (i p : ℕ) :=
  let a := splitInputs p
  (pairBudget a (splitInputs (i-p))).join (pairBudget a (splitInputs (i-p-1)))

def proposeMaxima (i : ℕ) : PairBudget :=
  (List.range (i+1)).foldl (fun m p => m.join (adjacentBudget i p)) ⟨0,0,0,0⟩

set_option maxRecDepth 65536 in
def cellMaxima : Array PairBudget := eval% ((List.range 288).map proposeMaxima).toArray

def maxBudget (i : ℕ) := cellMaxima[i]?.getD default

def cellMaxTest (i : ℕ) :=
  let cap := maxBudget i
  (List.range (i+1)).all fun p => (adjacentBudget i p).test cap

theorem pair_within_max {i p q : ℕ} (test : cellMaxTest i=true)
    (hp : p≤ i) (hq : q≤ i-p) (low : i≤p+q+1) :
    let c := pairBudget (splitInputs p) (splitInputs q)
    let m := maxBudget i
    c.lattice≤m.lattice ∧ c.second≤m.second ∧ c.third≤m.third ∧ c.fourth≤m.fourth := by
  let u := pairBudget (splitInputs p) (splitInputs (i-p))
  let w := pairBudget (splitInputs p) (splitInputs (i-p-1))
  have eq := List.all_eq_true.mp test p (List.mem_range.mpr (by omega))
  change (u.join w).test (maxBudget i)=true at eq
  simp only [PairBudget.test,PairBudget.join,Bool.and_eq_true,decide_eq_true_eq,max_le_iff] at eq
  rcases eq with ⟨⟨⟨a,b⟩,c⟩,d⟩
  rcases (show q=i-p ∨ q=i-p-1 by omega) with rfl|rfl
  · exact ⟨a.1,b.1,c.1,d.1⟩
  · exact ⟨a.2,b.2,c.2,d.2⟩

/-- The four contributions have common denominator `4,800,000·10⁶⁰`
after inserting the upper endpoint `(i+1)/2` of the cell. -/
def costUnits (i : ℕ) :=
  let m := maxBudget i
  ceilQuotient (4800000*(splitInputs i).freeNoise*10^30+192*m.lattice+
    75000*(i+1)*m.second+100000*(i+1)*m.third+9375*(i+1)^2*m.fourth) (4800000*10^30)

end CentralUnimodality.PolynomialTrial
