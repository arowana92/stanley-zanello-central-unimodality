module

public import CentralUnimodality.CellSamples
public import CentralUnimodality.PackedRows

/-! Check cell moments using only the digits of a packed rank row, integer
endpoint powers, and coefficients of individual Catalan-root powers. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

def rootCoeffValue (h : ℤ) : ℕ → ℚ
  | 0 => 1
  | n+1 => (4*(n:ℚ)-2*h)*rootCoeffValue h n/((n:ℚ)+1)

theorem rootCoeffValue_eq (h : ℤ) (n : ℕ) : rootCoeffValue h n = coeff n (rootPower h) := by
  induction n with
  | zero => exact (rootPower_coeff_zero h).symm
  | succ n ih =>
    rw [rootCoeffValue,ih,← rootPower_coeff_step]
    field_simp

def evaluateWith (f : ℤ → ℚ) : Laurent → ℚ
  | [] => 0
  | (h,c)::p => c*f h + evaluateWith f p

theorem evaluateWith_eq (n : ℕ) (p : Laurent) :
    evaluateWith (fun h => rootCoeffValue h n) p = coeff n (eval p) := by
  induction p with
  | nil => simp [evaluateWith,eval]
  | cons t p ih =>
    obtain ⟨h,c⟩ := t
    rw [evaluateWith,ih,rootCoeffValue_eq,eval,map_add, coeff_C_mul]

def twiceLeft (n δ j : ℕ) := 2*(n*(n+δ)-j)+(3*(n+δ)-δ)

def rankCells (n δ : ℕ) : List (ℕ × ℕ) :=
  let m := 2*n+δ
  let bits := m+1
  let v := packedRow bits m
  (List.range (n*(n+δ)+1)).map fun j => (twiceLeft n δ j,digit bits v j)

def momentDen (r : ℕ) := 2^(r+1)*(r+1)

def momentInt (cells : List (ℕ × ℕ)) (r : ℕ) :=
  (cells.map fun (u,w) => w*((u+2)^(r+1)-u^(r+1))).sum

private theorem listSum {R : Type*} [AddCommMonoid R] (f : ℕ → R) (d : ℕ) :
    ((List.range d).map f).sum = ∑ i ∈ Finset.range d, f i := by
  induction d with
  | zero => simp
  | succ d ih => simp [List.range_succ,Finset.sum_range_succ,ih]

theorem momentInt_eq (n δ r : ℕ) : (momentInt (rankCells n δ) r:ℚ) =
    (momentDen r:ℚ)*Witness.rawCell n δ r := by
  simp only [momentInt,rankCells,List.map_map,Function.comp_def,listSum,Nat.cast_sum,
    Nat.cast_mul,packedRow_digit _ _ _ (Nat.lt_succ_self _),Witness.rawCell,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let u := twiceLeft n δ i
  have hu : (u:ℚ)/2 = ((n*(n+δ)-i:ℕ):ℚ) + (3*((n+δ:ℕ):ℚ)/2+(-(δ:ℚ)/2)) := by
    dsimp [u,twiceLeft]
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : δ ≤ 3*(n+δ))]
    push_cast
    ring
  have he : (u:ℚ)/2+1 = ((u+2:ℕ):ℚ)/2 := by push_cast; ring
  have hmono := Nat.pow_le_pow_left (by omega : u ≤ u+2) (r+1)
  change (rankCount _ i:ℚ)*(((u+2)^(r+1)-u^(r+1):ℕ):ℚ) = _*(_*_)
  rw [← hu,cellPower,he,Nat.cast_sub hmono,Nat.cast_pow,Nat.cast_pow,div_pow,div_pow]
  simp only [momentDen,Nat.cast_mul,Nat.cast_pow,Nat.cast_succ]
  field_simp
  ring

def sampleOK (n δ r : ℕ) (p : Laurent) : Bool :=
  decide (evaluateWith (fun h => rootCoeffValue h (n+δ)) p * (momentDen r:ℚ) =
    ((δ:ℚ)+1)*(momentInt (rankCells n δ) r:ℚ))

theorem sampleOK_sound {n δ r : ℕ} {p : Laurent} (h : sampleOK n δ r p = true) :
    coeff (n+δ) (eval p) = ((δ:ℚ)+1)*Witness.rawCell n δ r := by
  have he := of_decide_eq_true h
  rw [evaluateWith_eq,momentInt_eq] at he
  have hd : (momentDen r:ℚ) ≠ 0 := by unfold momentDen; positivity
  apply mul_right_cancel₀ hd
  linear_combination he

end CentralUnimodality.Laurent
