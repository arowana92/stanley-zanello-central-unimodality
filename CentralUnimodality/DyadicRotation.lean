module

public import CentralUnimodality.PositiveEnclosure

/-! Enclose successive phases by the addition formulas. Only the initial
grid phase requires integer square roots. -/
@[expose] public section

namespace CentralUnimodality.SmallGrid

open PositiveEnclosure

structure Phase where
  c : ℕ × ℕ
  s : ℕ × ℕ

def phaseZero (d : ℕ) : Phase := ⟨one d,(0,0)⟩
def basePhase (d k f : ℕ) : Phase := ⟨DyadicAngle.cosine d k f,DyadicAngle.sine d k f⟩
def advance (d : ℕ) (a b : Phase) : Phase :=
  ⟨difference (product d a.c b.c) (product d a.s b.s),
   sum (product d a.s b.c) (product d a.c b.s)⟩

noncomputable def frequency (k f : ℕ) := (f:ℝ)*Real.pi/(2:ℝ)^(k+1)

structure PhaseHolds (d : ℕ) (p : Phase) (x : ℝ) : Prop where
  c : Holds d p.c (Real.cos x)
  s : Holds d p.s (Real.sin x)

theorem zero_holds (d : ℕ) : PhaseHolds d (phaseZero d) 0 :=
  ⟨by simpa only [Real.cos_zero,phaseZero] using holds_one d,by simp [phaseZero,Holds]⟩

theorem base_holds {d k f : ℕ} (hf : f ≤ 2^k) : PhaseHolds d (basePhase d k f) (frequency k f) :=
  ⟨DyadicAngle.cosine_sound d k f hf,DyadicAngle.sine_sound d k f hf⟩

/-- Add one grid step, staying in the first quadrant. -/
theorem advance_holds {d k f i : ℕ} (hd : 0 < d) {p : Phase}
    (hp : PhaseHolds d p (frequency k f*i)) (ht : (i+1)*f ≤ 2^k) :
    PhaseHolds d (advance d p (basePhase d k f)) (frequency k f*(i+1:ℕ)) := by
  have hf : f ≤ 2^k :=
    (show f ≤ (i+1)*f by simpa using Nat.mul_le_mul_right f (show 1 ≤ i+1 by omega)).trans ht
  have hz := base_holds (d := d) hf
  let ω := frequency k f
  have hangle : ω*((i+1:ℕ):ℝ) ≤ Real.pi/2 := by
    dsimp [ω,frequency]
    rw [div_mul_eq_mul_div,pow_succ]
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right (by exact_mod_cast ht : ((i+1:ℕ):ℝ)*f ≤ (2:ℝ)^k) Real.pi_pos.le
    linarith only [show (f:ℝ)*Real.pi*((i+1:ℕ):ℝ) ≤ 2^k*Real.pi by simpa only [mul_comm,mul_left_comm,mul_assoc] using hh]
  have hpos : 0 ≤ ω*((i+1:ℕ):ℝ) := by dsimp [ω,frequency]; positivity
  have hcos := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos] : -(Real.pi/2) ≤ ω*((i+1:ℕ):ℝ)) hangle
  have he : ω*((i+1:ℕ):ℝ) = ω*i+ω := by push_cast; ring
  rw [he,Real.cos_add] at hcos
  change PhaseHolds d _ (ω*((i+1:ℕ):ℝ))
  rw [he]
  constructor
  · rw [Real.cos_add]
    exact holds_difference (holds_product hd hp.c hz.c) (holds_product hd hp.s hz.s) (sub_nonneg.mp hcos)
  · rw [Real.sin_add]
    exact holds_sum (holds_product hd hp.s hz.c) (holds_product hd hp.c hz.s)

end CentralUnimodality.SmallGrid
