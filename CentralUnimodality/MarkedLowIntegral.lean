module

public import CentralUnimodality.MarkedLateCharacter
public import CentralUnimodality.LateArcIntegrals

/-! Integrate the two-harmonic bound over all positive and negative
frequencies up to 4096 in the area scale, retaining the exact bin volumes. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.FrequencyGrid
open Real Set MeasureTheory BinArithmetic

noncomputable def band (a b : ℝ) (r : ℕ) (θ : ℝ) := (Icc a b).indicator (fun x : ℝ => x^r) |θ|

private theorem band_nonneg (a b : ℝ) (r : ℕ) (θ : ℝ) : 0≤band a b r θ := by
  unfold band; by_cases h : |θ|∈Icc a b <;> simp [h]

theorem band_integral {a b : ℝ} (ha : 0≤a) (hab : a<b) (r : ℕ) :
    Integrable (band a b r) ∧ (∫ θ, band a b r θ)=2*(b^(r+1)-a^(r+1))/((r:ℝ)+1) := by
  have he : (∫ θ, band a b r θ)=2*(b^(r+1)-a^(r+1))/((r:ℝ)+1) := by
    rw [show band a b r = fun θ : ℝ => ((Icc a b).indicator (fun x : ℝ => x^r)) |θ| from rfl,
      integral_comp_abs,← integral_Ici_eq_integral_Ioi,setIntegral_indicator measurableSet_Icc,
      inter_eq_right.mpr (show Icc a b ⊆ Ici 0 from fun _ h => ha.trans h.1),
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab.le,integral_pow]
    ring
  refine ⟨Integrable.of_integral_ne_zero (he.trans_ne (ne_of_gt ?_)),he⟩
  have hp := pow_lt_pow_left₀ hab ha (Nat.succ_ne_zero r)
  positivity

noncomputable def lowEnvelope (s : ℝ) (r : ℕ) (θ : ℝ) :=
  ∑ i ∈ Finset.range 180, (weight i:ℝ)*band ((edge i:ℝ)/s) ((edge (i+1):ℝ)/s) r θ

theorem low_nonneg (s : ℝ) (r : ℕ) (θ : ℝ) : 0≤lowEnvelope s r θ :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (by exact_mod_cast weight_nonneg i) (band_nonneg ..))

theorem low_integral {s : ℝ} (hs : 0<s) (r : Fin 3) :
    Integrable (lowEnvelope s r) ∧ (∫ θ, lowEnvelope s r θ)≤2*(lowLimit r:ℝ)/s^(r.val+1) := by
  let f (i : ℕ) (θ : ℝ) := (weight i:ℝ)*band ((edge i:ℝ)/s) ((edge (i+1):ℝ)/s) r θ
  have B (i : ℕ) (hi : i∈Finset.range 180) := band_integral
    (div_nonneg (by dsimp only [edge]; positivity : (0:ℝ)≤(edge i:ℝ)) hs.le)
    (div_lt_div_of_pos_right (by exact_mod_cast edge_strict ⟨i,Finset.mem_range.mp hi⟩ : (edge i:ℝ)<(edge (i+1):ℝ)) hs) r.val
  have I (i : ℕ) (hi : i∈Finset.range 180) : Integrable (f i) := (B i hi).1.const_mul _
  refine ⟨integrable_finsetSum _ I,?_⟩
  change (∫ θ, ∑ i ∈ Finset.range 180, f i θ) ≤ _
  rw [integral_finsetSum _ I]
  have he (i : ℕ) (hi : i∈Finset.range 180) :
      (∫ θ, f i θ)=(2/s^(r.val+1))*(binMoment i r:ℝ) := by
    dsimp only [f]
    rw [integral_const_mul,(B i hi).2]
    unfold binMoment; push_cast; simp only [div_pow]; field_simp [hs.ne']
  rw [Finset.sum_congr rfl he,← Finset.mul_sum,← Rat.cast_sum]
  have H := mul_le_mul_of_nonneg_left ((Rat.cast_le (K:=ℝ)).mpr (low_moments r)) (by positivity : 0≤2/s^(r.val+1))
  exact H.trans_eq (by ring)

theorem wall_low_dominates {v b U : ℝ} {m : ℕ} (hm : 4096≤m)
    (hv : 0≤v) (hb' : b≤6/25) (hU' : U≤6/25) (hcap : v*m-b≤U)
    {θ : ℝ} (hu : sizeScale m*|θ|≤4096) (r : ℕ) :
    let L := timeCut m (3/40)
    let T := timeCut m (37/40)
    endpointNorm (wallRow v (v*m-b) m θ 0 T)*|θ|^r ≤ live v (v*m-b) L 1*lowEnvelope (sizeScale m) r θ := by
  let s := sizeScale m
  have hmp : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hs : 0<s := mul_pos hmp (sqrt_pos.mpr hmp)
  obtain ⟨i,hl,hh⟩ := covers (mul_nonneg hs.le (abs_nonneg θ)) hu
  have H := marked_wall_transform hm hv hb' hU' hcap i hl hh
  have hmem : |θ|∈Icc ((edge i:ℝ)/s) ((edge (i+1:ℕ):ℝ)/s) :=
    ⟨(div_le_iff₀ hs).mpr (by simpa only [mul_comm] using hl),(le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hh)⟩
  have h := Finset.single_le_sum (s:=Finset.range 180)
    (f:=fun j => (weight j:ℝ)*band ((edge j:ℝ)/s) ((edge (j+1):ℝ)/s) r θ)
    (fun j _ => mul_nonneg (by exact_mod_cast weight_nonneg j) (band_nonneg ..))
    (Finset.mem_range.mpr i.isLt)
  rw [show band ((edge i:ℝ)/s) ((edge (i+1:ℕ):ℝ)/s) r θ=|θ|^r by simp [band,hmem]] at h
  apply (mul_le_mul_of_nonneg_right H (by positivity : 0≤|θ|^r)).trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h (live_nonneg ..)

end CentralUnimodality.MarkedExcursion.FrequencyGrid
