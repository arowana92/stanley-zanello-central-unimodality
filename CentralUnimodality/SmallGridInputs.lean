module

public import CentralUnimodality.DyadicRotation
public import CentralUnimodality.BridgeProduct

/-! Enclose the true Fourier inputs by integer arithmetic when all free
cosines through the last odd length lie in the first quadrant. -/
@[expose] public section

namespace CentralUnimodality.SmallGrid

open PowerSeries PositiveEnclosure

structure Inputs where
  halfPhase : Phase
  oddPhase : Phase
  bridge : ℕ × ℕ
  evenFree : ℕ × ℕ
  oddFree : ℕ × ℕ
  valid : Bool

def start (d k f : ℕ) : Inputs :=
  ⟨phaseZero d,basePhase d k f,one d,one d,(basePhase d k f).c,true⟩

def next (d k f : ℕ) (v : Inputs) : Inputs :=
  let z := basePhase d k f
  let a := advance d v.halfPhase z
  let b := advance d v.oddPhase z
  let c := advance d b z
  let r := halfQuotient d (product d (product d v.bridge a.c) v.oddPhase.s) a.s
  let e := product d v.oddFree b.c
  ⟨a,c,r,e,product d e c.c,v.valid && decide (0 < a.s.1)⟩

def inputs (d k f : ℕ) : ℕ → Inputs
  | 0 => start d k f
  | j+1 => next d k f (inputs d k f j)

def Contains (d : ℕ) (a : ℕ × ℕ) (z : ℂ) := ∃ x : ℝ, z = (x:ℂ) ∧ Holds d a x

private theorem free_succ (ω : ℝ) (t : ℕ) :
    coeff (t+1) (fairSeries (areaCharacter ω) words) =
      coeff t (fairSeries (areaCharacter ω) words) * (Real.cos (ω*((t+1:ℕ):ℝ)):ℂ) := by
  simp only [fourier_free_product,Finset.prod_range_succ,Nat.cast_add,Nat.cast_one]

private theorem free_contains {d k f t : ℕ} (hd : 0 < d) {a b : ℕ × ℕ}
    (h : Contains d a (coeff t (fairSeries (areaCharacter (frequency k f)) words)))
    (ht : Holds d b (Real.cos (frequency k f*((t+1:ℕ):ℝ)))) :
    Contains d (product d a b)
      (coeff (t+1) (fairSeries (areaCharacter (frequency k f)) words)) := by
  obtain ⟨x,hx,ha⟩ := h
  exact ⟨_,by rw [free_succ,hx,Complex.ofReal_mul],holds_product hd ha ht⟩

structure Correct (d k f n : ℕ) (a : Inputs) : Prop where
  halfPhase : PhaseHolds d a.halfPhase (frequency k f*n)
  oddPhase : PhaseHolds d a.oddPhase (frequency k f*((2*n+1:ℕ):ℝ))
  bridge : Contains d a.bridge (coeff (2*n) (fairSeries (areaCharacter (frequency k f)) bridges))
  evenFree : Contains d a.evenFree (coeff (2*n) (fairSeries (areaCharacter (frequency k f)) words))
  oddFree : Contains d a.oddFree (coeff (2*n+1) (fairSeries (areaCharacter (frequency k f)) words))

private theorem start_correct {d k f : ℕ} (hf : f ≤ 2^k) : Correct d k f 0 (start d k f) := by
  refine ⟨by simpa [start] using zero_holds d,by simpa [start] using base_holds (d := d) hf,
    ⟨1,?_,holds_one d⟩,⟨1,?_,holds_one d⟩,⟨Real.cos (frequency k f),?_,(base_holds hf).c⟩⟩
  · have h : bridges 0 = {[]} := by decide +kernel
    simp [coeff_walkSeries,h,walkArea,heights,areaCharacter_zero]
  · simp [fourier_free_product]
  · simp [fourier_free_product]

private theorem next_correct {d k f j : ℕ} (hd : 0 < d) {v : Inputs} (h : Correct d k f j v)
    (ht : (2*j+3)*f ≤ 2^k) (hn : 0 < (advance d v.halfPhase (basePhase d k f)).s.1) :
    Correct d k f (j+1) (next d k f v) := by
  have ht' (i : ℕ) (hi : i ≤ 2*j+3) : i*f ≤ 2^k := (Nat.mul_le_mul_right f hi).trans ht
  have hA := advance_holds hd h.halfPhase (ht' (j+1) (by omega))
  have hB := advance_holds hd h.oddPhase (ht' (2*j+1+1) (by omega))
  have hC := advance_holds hd hB (ht' (2*j+1+1+1) (by omega))
  have he := free_contains hd h.oddFree hB.c
  have ho := free_contains hd he hC.c
  refine ⟨hA,by simpa only [next,Nat.mul_add,Nat.mul_one] using hC,
    ?_,by simpa only [next,Nat.mul_add,Nat.mul_one] using he,
    by simpa only [next,Nat.mul_add,Nat.mul_one] using ho⟩
  let ω := frequency k f
  let a : ℝ := ω*((j+1:ℕ):ℝ)
  let b : ℝ := ω*((2*j+1:ℕ):ℝ)
  obtain ⟨x,hx,hr⟩ := h.bridge
  have ha : 0 < Real.sin a := pos_of_mul_pos_right
    ((by exact_mod_cast hn : (0:ℝ) < (advance d v.halfPhase (basePhase d k f)).s.1).trans_le hA.s.1)
    (Nat.cast_nonneg d)
  refine ⟨(x*Real.cos a*Real.sin b)/(2*Real.sin a),?_,
    holds_halfQuotient hd (holds_product hd (holds_product hd hr hA.c) h.oddPhase.s) hA.s hn⟩
  have hh := fair_bridge_sine_step ω j
  change coeff (2*j) (fairSeries (areaCharacter ω) bridges) = (x:ℂ) at hx
  rw [hx] at hh
  rw [Nat.mul_add,Nat.mul_one,Complex.ofReal_div]
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num) ha).ne')).mpr
  change _ * ((2*Real.sin a:ℝ):ℂ) = ((x*Real.cos a*Real.sin b:ℝ):ℂ)
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  dsimp [a,b]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  linear_combination hh

theorem inputs_sound {d k f n : ℕ} (hd : 0 < d) (ht : (2*n+1)*f ≤ 2^k)
    (hv : (inputs d k f n).valid = true) : Correct d k f n (inputs d k f n) := by
  induction n with
  | zero => exact start_correct (by simpa using ht)
  | succ j ih =>
    change (next d k f (inputs d k f j)).valid = true at hv
    simp only [next,Bool.and_eq_true,decide_eq_true_eq] at hv
    have ht' : (2*j+3)*f ≤ 2^k := by simpa only [Nat.mul_add,Nat.mul_one] using ht
    exact next_correct hd (ih ((Nat.mul_le_mul_right f (show 2*j+1 ≤ 2*j+3 by omega)).trans ht') hv.1) ht' hv.2

end CentralUnimodality.SmallGrid
