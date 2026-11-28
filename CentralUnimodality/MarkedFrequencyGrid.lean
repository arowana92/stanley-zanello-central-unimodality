module

public import CentralUnimodality.OppositeBlockBins

/-! One grid of scaled frequencies covers [0,4096]. Its block counts are
witnesses only. The kernel computes both contraction factors, rounds them
up, and checks the integrated bounds using rational arithmetic. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.FrequencyGrid
open Real

/-- Endpoints are stored in quarter units. -/
def gridTick : ℕ → ℕ
  | 0 => 0
  | i+1 => let a := gridTick i; min 16384 (a+1+a/25)

def edge (i : ℕ) : ℚ := gridTick i/4

def blocks (i : ℕ) : ℕ :=
  1+([146,334,565,842,1157,1469,1862,2268,2656,3109,3499,4095,4608,5185,5609,6311,
    6827,7386,7990,8643,9349,10112,10938,11376,12306,12799,13844,14398,14974,15573,16196]
    : List ℕ).countP (· ≤ gridTick (i+1))

def roundUp (d : ℕ) (q : ℚ) : ℚ := (⌈q*d⌉₊:ℚ)/d

def weight (i : ℕ) : ℚ :=
  let k := blocks i
  roundUp (10^14) ((roundUp (10^6) (binFactor k (edge i) (edge (i+1))))^k)

theorem rational_round_up {d : ℕ} (hd : 0<d) (q : ℚ) : q≤roundUp d q := by
  exact (le_div_iff₀ (by exact_mod_cast hd)).mpr (Nat.le_ceil _)

theorem weight_nonneg (i : ℕ) : 0≤weight i := by dsimp [weight,roundUp]; positivity

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

private theorem grid_geometry : ∀ i : Fin 180, edge i<edge (i+1:ℕ) ∧
    0<blocks i ∧ 0≤blockFraction (blocks i) ∧
    0≤(blockFraction (blocks i))^3-blockFraction (blocks i)*(1/4096)^2 := by decide +kernel

theorem edge_strict (i : Fin 180) : edge i<edge (i+1:ℕ) := (grid_geometry i).1

theorem covers {t : ℝ} (ht : 0≤t) (hu : t≤4096) :
    ∃ i : Fin 180, (edge i:ℝ)≤t ∧ t≤(edge (i+1:ℕ):ℝ) := by
  have aux (n : ℕ) (hn : n≤180) (h : t≤(edge n:ℝ)) :
      t=0 ∨ ∃ i : Fin 180, (edge i:ℝ)≤t ∧ t≤(edge (i+1:ℕ):ℝ) := by
    induction n with
    | zero => left; simpa [edge,gridTick] using le_antisymm h (by simpa [edge,gridTick] using ht)
    | succ n ih =>
      by_cases hp : t≤(edge n:ℝ)
      · exact ih (by omega) hp
      · exact Or.inr ⟨⟨n,by omega⟩,(le_of_not_ge hp),h⟩
  have hend : edge 180=4096 := by decide +kernel
  rcases aux 180 le_rfl (by rw [hend]; simpa using hu) with h|h
  · subst t; exact ⟨0,by norm_num [edge,gridTick],by norm_num [edge,gridTick]⟩
  · exact h

theorem bin_bounds {m : ℕ} (hm : 4096≤m) (i : Fin 180) {θ : ℝ}
    (hlo : (edge i:ℝ)≤m*√m*|θ|) (hhi : (m:ℝ)*√m*|θ|≤(edge (i+1:ℕ):ℝ)) :
    let k := blocks i
    let l := (BinArithmetic.timeCut m (37/40)-BinArithmetic.timeCut m (3/40))/(2*k)
    (twoHarmonicFactor l θ)^k ≤ (weight i:ℝ) := by
  obtain ⟨_,hk,hW,hE⟩ := grid_geometry i
  have H := marked_frequency_factor hm hk (by dsimp [edge]; positivity) hlo hhi hW hE
  have hr := (Rat.cast_le (K:=ℝ)).mpr (rational_round_up (by decide : 0<10^6) (binFactor (blocks i) (edge i) (edge (i+1:ℕ))))
  have hρ (l : ℕ) : 0≤twoHarmonicFactor l θ := by dsimp [twoHarmonicFactor]; positivity
  apply (pow_le_pow_left₀ (hρ _) (H.trans hr) (blocks i)).trans
  have h := (Rat.cast_le (K:=ℝ)).mpr (rational_round_up (by decide : 0<10^14)
    ((roundUp (10^6) (binFactor (blocks i) (edge i) (edge (i+1:ℕ))))^(blocks i)))
  simpa only [Rat.cast_pow,weight] using h

def binMoment (i r : ℕ) : ℚ := weight i*((edge (i+1))^(r+1)-(edge i)^(r+1))/(r+1)

def lowLimit (r : Fin 3) : ℚ := if r=0 then 41 else if r=1 then 2454 else 402487

theorem low_moments (r : Fin 3) : ∑ i ∈ Finset.range 180, binMoment i r ≤ lowLimit r := by
  fin_cases r <;> decide +kernel

end CentralUnimodality.MarkedExcursion.FrequencyGrid
