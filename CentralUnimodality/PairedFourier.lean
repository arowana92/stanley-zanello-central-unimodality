module

public import CentralUnimodality.EndpointTransforms

/-! Pairing the first and last sign of an unrestricted block makes the two
mixed terms at the same endpoint interfere. Bound their sum before taking
absolute values. -/
@[expose] public section

namespace CentralUnimodality

private theorem paired_endpoint (ω : ℝ) (n : ℕ) (z : ℤ) :
    endpointTransform ω (n+2) z = areaCharacter ω z *
      (areaCharacter ω (n+1)*endpointTransform ω n (z-2) +
       areaCharacter ω (-(n+1:ℤ))*endpointTransform ω n (z+2) +
       (areaCharacter ω (n+1)+areaCharacter ω (-(n+1:ℤ)))*endpointTransform ω n z) := by
  rw [endpoint_append,endpoint_prepend,endpoint_prepend,
    show z-1-1 = z-2 by omega, show z+1+1 = z+2 by omega,
    show z-1+1 = z by omega, show z+1-1 = z by omega]
  ring

private theorem paired_norm (ω : ℝ) (n : ℕ) (z : ℤ) :
    ‖endpointTransform ω (n+2) z‖ ≤
      ‖endpointTransform ω n (z-2)‖ + ‖endpointTransform ω n (z+2)‖ +
      (2*|Real.cos (ω*(n+1))|)*‖endpointTransform ω n z‖ := by
  rw [paired_endpoint,norm_mul,norm_areaCharacter,one_mul]
  apply (norm_add_le ..).trans
  apply add_le_add
  · apply (norm_add_le ..).trans_eq
    simp [norm_areaCharacter]
  · rw [areaCharacter_pair,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,show ‖(2:ℂ)‖ = 2 by norm_num]
    simp only [Int.cast_add,Int.cast_natCast,Int.cast_one,le_refl]

/-- A common bound for every finite set of endpoints. This also bounds any
individual entry and the sum over the entire support of the walk. -/
def EndpointNormBound (ω : ℝ) (n : ℕ) (B : ℝ) : Prop :=
  ∀ s : Finset ℤ, ∑ z ∈ s, ‖endpointTransform ω n z‖ ≤ B

private theorem norm_translate {ω : ℝ} {n : ℕ} {B : ℝ} (h : EndpointNormBound ω n B)
    (s : Finset ℤ) (a : ℤ) : ∑ z ∈ s, ‖endpointTransform ω n (z+a)‖ ≤ B := by
  have he := h (s.image (·+a))
  rwa [Finset.sum_image (fun _ _ _ _ hh => add_right_cancel hh)] at he

theorem endpoint_norm_pair {ω : ℝ} {n : ℕ} {B : ℝ} (h : EndpointNormBound ω n B) :
    EndpointNormBound ω (n+2) ((2+2*|Real.cos (ω*(n+1))|)*B) := by
  intro s
  refine (Finset.sum_le_sum (fun z _ => paired_norm ω n z)).trans ?_
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  have ha := norm_translate h s (-2)
  have hb := norm_translate h s 2
  have hc := mul_le_mul_of_nonneg_left (h s) (by positivity : 0 ≤ 2*|Real.cos (ω*(n+1))|)
  simpa only [sub_eq_add_neg,add_mul,two_mul,add_assoc] using add_le_add (add_le_add ha hb) hc

theorem endpoint_norm_one {ω : ℝ} {n : ℕ} {B : ℝ} (h : EndpointNormBound ω n B) :
    EndpointNormBound ω (n+1) (2*B) := by
  intro s
  have per (z : ℤ) : ‖endpointTransform ω (n+1) z‖ ≤
      ‖endpointTransform ω n (z-1)‖+‖endpointTransform ω n (z+1)‖ := by
    rw [endpoint_append,norm_mul,norm_areaCharacter,one_mul]
    exact norm_add_le ..
  refine (Finset.sum_le_sum (fun z _ => per z)).trans ?_
  rw [Finset.sum_add_distrib,two_mul]
  simpa only [sub_eq_add_neg] using add_le_add (norm_translate h s (-1)) (norm_translate h s 1)

noncomputable def pairFactor (ω : ℝ) (l : ℕ) : ℝ :=
  ∏ i ∈ Finset.range l, ((1+|Real.cos (ω*(2*i+1))|)/2)

theorem endpoint_norm_even (ω : ℝ) (l : ℕ) :
    EndpointNormBound ω (2*l) ((2:ℝ)^(2*l)*pairFactor ω l) := by
  induction l with
  | zero =>
    intro s
    simp only [Nat.mul_zero,pow_zero,pairFactor,Finset.range_zero,Finset.prod_empty,mul_one,
      endpointTransform,words,Finset.sum_singleton,displacement,List.map_nil,List.sum_nil]
    have hz : walkArea [] = 0 := rfl
    simp [hz,areaCharacter_zero,apply_ite norm,eq_comm (a := (0:ℤ))]
    split <;> norm_num
  | succ l ih =>
    rw [Nat.mul_succ,pow_add,pairFactor,Finset.prod_range_succ]
    convert endpoint_norm_pair ih using 1
    unfold pairFactor
    push_cast
    ring

theorem fair_bridge_pair_bound (ω : ℝ) (l : ℕ) :
    ‖PowerSeries.coeff (2*l) (fairSeries (areaCharacter ω) bridges)‖ ≤ pairFactor ω l := by
  have h := endpoint_norm_even ω l {0}
  simp only [Finset.sum_singleton] at h
  rw [fair_bridge_endpoint,norm_mul,norm_pow,norm_inv]
  have he : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [he,inv_pow,inv_mul_le_iff₀ (by positivity)]
  exact h

private theorem endpoint_sum (ω : ℝ) (n : ℕ) :
    (∑ z ∈ (words n).image displacement, endpointTransform ω n z) =
      ∑ w ∈ words n, areaCharacter ω (walkArea w) := by
  unfold endpointTransform
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  simp [Finset.mem_image_of_mem displacement hw]

/-- After a paired prefix, any number of extra unrestricted steps preserve
the same upper bound on the fair free and fair bridge inputs. -/
theorem fair_inputs_after_pairs (ω : ℝ) {l n : ℕ} (hn : 2*l ≤ n) :
    ‖PowerSeries.coeff n (fairSeries (areaCharacter ω) words)‖ ≤ pairFactor ω l ∧
    ‖PowerSeries.coeff n (fairSeries (areaCharacter ω) bridges)‖ ≤ pairFactor ω l := by
  have h : EndpointNormBound ω n ((2:ℝ)^n*pairFactor ω l) := by
    induction n,hn using Nat.le_induction with
    | base => exact endpoint_norm_even ω l
    | succ n _ ih =>
      simpa only [pow_succ,mul_left_comm,mul_comm,mul_assoc] using endpoint_norm_one ih
  have he : ‖(2:ℂ)‖ = 2 := by norm_num
  constructor
  · rw [coeff_walkSeries,← endpoint_sum,norm_mul,norm_pow,norm_inv,he,inv_pow,inv_mul_le_iff₀ (by positivity)]
    exact (norm_sum_le ..).trans (h _)
  · rw [fair_bridge_endpoint,norm_mul,norm_pow,norm_inv,he,inv_pow,inv_mul_le_iff₀ (by positivity)]
    simpa only [Finset.sum_singleton] using h {0}

end CentralUnimodality
