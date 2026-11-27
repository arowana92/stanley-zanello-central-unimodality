module

public import CentralUnimodality.PackedRows
public import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-! Evaluating a rank polynomial at one plus a large base packs its
binomial moments into the low digits. The value can be computed modulo a
fixed power of the base throughout the rank-by-length recurrence. -/
@[expose] public section

namespace CentralUnimodality.Laurent

private theorem partial_lt {b : ℕ} (f : ℕ → ℕ) (d : ℕ)
    (hf : ∀ i < d, f i < b) : ∑ i ∈ Finset.range d, f i*b^i < b^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ,pow_succ']
    have h := Nat.add_lt_add_right (ih (fun i hi => hf i (by omega))) (f d*b^d)
    apply h.trans_le
    rw [Nat.add_comm,← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (hf d (by omega))

/-- High terms make no contribution to the first r digits of a polynomial. -/
private theorem truncate_mod (b : ℕ) (f : ℕ → ℕ) (r d : ℕ) :
    (∑ i ∈ Finset.range (r+d), f i*b^i) % b^r =
      (∑ i ∈ Finset.range r, f i*b^i) % b^r := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc,Finset.sum_range_succ,pow_add]
    rw [show f (r+d)*(b^r*b^d) = f (r+d)*b^d*b^r by ring,Nat.add_mul_mod_self_right,ih]

/-- Extract the j-th coefficient when all preceding coefficients fit. -/
theorem taylor_digit {b j D : ℕ} (hb : 0 < b) (hj : j ≤ D) (f : ℕ → ℕ)
    (hf : ∀ i ≤ j, f i < b) :
    ((∑ i ∈ Finset.range (D+1), f i*b^i) / b^j) % b = f j := by
  have hd : D+1 = (j+1)+(D-j) := by omega
  rw [← Nat.mod_mul_right_div_self,← pow_succ,hd,truncate_mod,Finset.sum_range_succ,
    pow_succ,Nat.mod_mul_right_div_self,Nat.mul_comm (f j),
    Nat.add_mul_div_left _ _ (Nat.pow_pos hb),Nat.div_eq_of_lt
      (partial_lt f j (fun i hi => hf i hi.le)),Nat.zero_add,Nat.mod_eq_of_lt (hf j le_rfl)]

def binomialMoment (m k : ℕ) : ℕ := ∑ l ∈ allPartitions m, l.sum.choose k

private theorem padded_binomial (b : ℕ) {w D : ℕ} (hw : w ≤ D) :
    (b+1)^w = ∑ i ∈ Finset.range (D+1), w.choose i*b^i := by
  rw [add_pow]
  simp only [one_pow,mul_one]
  simp only [Nat.cast_id]
  simp_rw [mul_comm (b^_) (w.choose _)]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i _ hi
  simp only [Finset.mem_range,not_lt] at hi
  simp [Nat.choose_eq_zero_of_lt (by omega : w < i)]

theorem taylor_weight {m D : ℕ} (b : ℕ) (hD : ∀ l ∈ allPartitions m, l.sum ≤ D) :
    (∑ l ∈ allPartitions m, (b+1)^l.sum) =
      ∑ i ∈ Finset.range (D+1), binomialMoment m i * b^i := by
  simp only [binomialMoment,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  exact fun l hl => padded_binomial b (hD l hl)

def nextMod (b M m : ℕ) (row : List ℕ) :=
  (List.range (m/2+1)).map fun
    | 0 => 1%M
    | d+1 => ((entry row (d+1)+entry row d)*(b^(d+1)%M))%M

def modularLayers (b M : ℕ) : ℕ → List ℕ
  | 0 => [1%M]
  | m+1 => nextMod b M (m+1) (modularLayers b M m)

private theorem modularLayers_eq (b M m : ℕ) :
    modularLayers b M m = (List.range (m/2+1)).map (fun d => weightByLength b m d % M) := by
  induction m with
  | zero => simp [modularLayers,List.range_succ,weight_zero_parts]
  | succ m ih =>
    rw [modularLayers,nextMod,ih]
    apply List.map_congr_left
    intro i hi
    have he (d : ℕ) : entry ((List.range (m/2+1)).map (fun i => weightByLength b m i % M)) d =
        weightByLength b m d % M := by
      by_cases hd : d < m/2+1
      · simp [entry,List.getElem?_map,List.getElem?_range hd]
      · simp [entry,hd,weight_zero_of_length (by omega : m < 2*d)]
    cases i with
    | zero => rw [weight_zero_parts]
    | succ d =>
      have := List.mem_range.mp hi
      change ((entry _ _+entry _ _)*_)%_ = _
      rw [he,he,weight_step b m d (by omega),Nat.mul_mod _ _ M,Nat.add_mod]
      simp [Nat.mul_mod]

def modularWeight (b M m : ℕ) := (modularLayers b M m).sum % M

theorem modularWeight_eq (b M m : ℕ) :
    modularWeight b M m = (∑ l ∈ allPartitions m, b^l.sum)%M := by
  rw [modularWeight,modularLayers_eq,allPartitions,Finset.sum_biUnion (fun _ _ _ _ h => disjoint_lengths h)]
  change _ = (∑ d ∈ Finset.range (m/2+1), weightByLength b m d) % M
  generalize m/2+1 = t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.range_succ,List.map_append,List.sum_append,Finset.sum_range_succ]
    simp only [List.map_singleton,List.sum_singleton]
    rw [Nat.add_mod,ih,Nat.mod_mod,← Nat.add_mod]

theorem digit_mod_weight {b t k : ℕ} (hk : k < t) (x : ℕ) :
    (x % b^t / b^k) % b = (x / b^k) % b := by
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hk)
  rw [hd,pow_add,pow_succ,mul_assoc,Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (dvd_mul_right ..)

end CentralUnimodality.Laurent
