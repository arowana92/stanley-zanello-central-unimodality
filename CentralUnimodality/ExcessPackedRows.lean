module

public import CentralUnimodality.PackedPeak
import Mathlib.Tactic.Ring

/-! A strict partition with `d` parts has rank at least `d(d+1)/2`.
Remove those zero digits from every packed endpoint. A sequential
pass over neighboring endpoint counts updates a whole ballot layer. -/
@[expose] public section

namespace CentralUnimodality.PackedComparisons

def triangular : ℕ → ℕ
  | 0 => 0
  | d+1 => triangular d+(d+1)

def excessPairs (bits : ℕ) : ℕ → ℕ → List ℕ → List ℕ
  | _, 0, _ => []
  | d, k+1, a => ((a.headD 0)+((a.tail.headD 0) <<< (bits*d)))::excessPairs bits (d+1) k a.tail

def excessNext (bits m : ℕ) (a : List ℕ) := 1::excessPairs bits 1 (m/2) a

def excessLayers (bits : ℕ) : ℕ → List ℕ
  | 0 => [1]
  | m+1 => excessNext bits (m+1) (excessLayers bits m)

private theorem pair_length (b d k : ℕ) (a : List ℕ) : (excessPairs b d k a).length=k := by
  induction k generalizing d a with
  | zero => rfl
  | succ k ih => simp [excessPairs,ih]

private theorem pair_entry (b d k : ℕ) (a : List ℕ) {j : ℕ} (hj : j<k) :
    entry (excessPairs b d k a) j=entry a j+(entry a (j+1) <<< (b*(d+j))) := by
  have hd (p : List ℕ) : p.headD 0=entry p 0 := by cases p <;> rfl
  have tail (p : List ℕ) (i : ℕ) : entry p.tail i=entry p (i+1) := by cases p <;> rfl
  induction k generalizing d a j with
  | zero => omega
  | succ k ih =>
    cases j with
    | zero =>
      change a.headD 0+(a.tail.headD 0 <<< (b*d))=_
      rw [hd,hd,tail]
      simp only [Nat.add_zero]
    | succ j =>
      change entry (excessPairs b (d+1) k a.tail) j=_
      rw [ih _ _ (by omega),tail,tail,show d+1+j=d+(j+1) by omega]

theorem excess_entry (b m d : ℕ) :
    entry (excessLayers b m) d <<< (b*triangular d)=entry (packedLayers b m) d := by
  induction m generalizing d with
  | zero => cases d <;> simp [excessLayers,packedLayers,entry,triangular]
  | succ m ih =>
    have len : (excessLayers b (m+1)).length=(m+1)/2+1 := by simp [excessLayers,excessNext,pair_length]
    by_cases inside : d<(m+1)/2+1
    · have next : entry (packedLayers b (m+1)) d=(match d with
        | 0 => 1
        | k+1 => (entry (packedLayers b m) (k+1)+entry (packedLayers b m) k) <<< (b*(k+1))) := by
        cases d <;> simp only [packedLayers,nextLayer,entry,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]
      rw [next]
      cases d with
      | zero => simp [excessLayers,excessNext,entry,triangular]
      | succ d =>
        change (entry (excessPairs b 1 ((m+1)/2) (excessLayers b m)) d <<< (b*triangular (d+1)))=
          (entry (packedLayers b m) (d+1)+entry (packedLayers b m) d) <<< (b*(d+1))
        rw [pair_entry _ _ _ _ (by omega),← ih,← ih,Nat.add_comm 1 d]
        simp only [Nat.shiftLeft_eq,triangular,Nat.mul_add,Nat.pow_add]
        ring
    · have out : (excessLayers b (m+1)).length≤d := by omega
      have endpt : (packedLayers b (m+1)).length≤d := by simp [packedLayers,nextLayer]; omega
      simp [entry,List.getElem?_eq_none out,List.getElem?_eq_none endpt]

def excessAssemble (b : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | d, a::p => a+(excessAssemble b (d+1) p <<< (b*(d+1)))

private theorem assemble_from (b d : ℕ) (a : List ℕ) :
    excessAssemble b d a <<< (b*triangular d)=
      ∑ j ∈ Finset.range a.length, entry a j <<< (b*triangular (d+j)) := by
  induction a generalizing d with
  | nil => simp [excessAssemble]
  | cons c a ih =>
    rw [List.length_cons,Finset.sum_range_succ',excessAssemble]
    have z : entry (c::a) 0=c := rfl
    simp only [z,Nat.add_zero]
    have tail (j : ℕ) : entry (c::a) (j+1)=entry a j := rfl
    have eq : (∑ j ∈ Finset.range a.length, entry (c::a) (j+1) <<< (b*triangular (d+(j+1))))=
        ∑ j ∈ Finset.range a.length, entry a j <<< (b*triangular (d+1+j)) := by
      apply Finset.sum_congr rfl; intro j _; rw [tail,show d+(j+1)=d+1+j by omega]
    rw [eq,← ih (d+1)]
    simp only [Nat.shiftLeft_eq,triangular,Nat.mul_add,Nat.pow_add]
    ring

theorem excess_assemble_eq (b m : ℕ) : excessAssemble b 0 (excessLayers b m)=packedRow b m := by
  have len : (excessLayers b m).length=(packedLayers b m).length := by
    cases m with
    | zero => rfl
    | succ m => simp [excessLayers,excessNext,pair_length,packedLayers,nextLayer]
  have s (a : List ℕ) : ∑ j ∈ Finset.range a.length, entry a j=a.sum := by
    induction a with
    | nil => simp
    | cons c a ih =>
      rw [List.length_cons,Finset.sum_range_succ']
      change (∑ j ∈ Finset.range a.length, entry a j)+c=c+a.sum
      rw [ih,Nat.add_comm]
  have eq := assemble_from b 0 (excessLayers b m)
  simpa only [triangular,Nat.mul_zero,Nat.shiftLeft_zero,Nat.zero_add,len,excess_entry,packedRow,s] using eq

def checkExcess (w : ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | k+1, m, a => checkPeak w (m*m/4) (excessAssemble (w+1) 0 a) && checkExcess w k (m+1) (excessNext (w+1) (m+1) a)

theorem checkExcess_sound {w k m : ℕ} (hw : m+k≤w)
    (ok : checkExcess w k m (excessLayers (w+1) m)=true) (i : ℕ) (hi : i<k) :
    UnimodalOn (rankCount (m+i)) 0 ((m+i)*(m+i)/4) := by
  induction k generalizing i m with
  | zero => omega
  | succ k ih =>
    simp only [checkExcess,Bool.and_eq_true] at ok
    cases i with
    | zero =>
      simp only [Nat.add_zero]
      apply checkPeak_rank (by omega : m<w)
      rw [← excess_assemble_eq]; exact ok.1
    | succ i =>
      rw [show m+(i+1)=m+1+i by omega]
      exact ih (by omega) ok.2 _ (by omega)

end CentralUnimodality.PackedComparisons
