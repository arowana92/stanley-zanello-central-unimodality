module

public import CentralUnimodality.TiltedEndpointBlock
public import CentralUnimodality.ReverseWalk

/-! Retain the cancellation between prefixes with the same endpoint when
continuing a tilted ballot walk. The continuation may depend on the endpoint. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Polynomial

theorem endpointAtom_append (c u a θ : ℝ) (v w : List Bool) :
    endpointAtom c u a θ (v++w) =
      endpointAtom c u a θ v * endpointAtom c (u-c*v.length) (a-v.length) θ w := by
  have hl : (wordParts (v++w)).length=(wordParts v).length+(wordParts w).length := by
    have h := displacement_length (v++w)
    rw [displacement_append,List.length_append,Nat.cast_add] at h
    have := displacement_length v
    have := displacement_length w
    omega
  simp only [endpointAtom,monomial_mul_monomial,hl,append_mass,Complex.ofReal_mul,
    prefixRank_append,mul_add,phase_add]
  ring_nf

/-- With an endpoint-dependent continuation, collecting each prefix fiber
before applying the triangle inequality preserves the one-block contraction. -/
theorem endpoint_continuation (c u a θ : ℝ) (A : Finset (List Bool)) (K : ℕ → Polynomial ℂ)
    {C : ℝ} (hK : ∀ k, endpointNorm (K k) ≤ C) :
    endpointNorm (∑ v ∈ A, endpointAtom c u a θ v * K (wordParts v).length) ≤
      endpointNorm (endpointRow c u a θ A)*C := by
  classical
  let d (v : List Bool) := (wordParts v).length
  let T := A.image d
  let P := endpointRow c u a θ A
  let z (v : List Bool) := (signMass c u v:ℂ)*phase (θ*prefixRank a v)
  have coeff (k : ℕ) : P.coeff k=∑ v ∈ A.filter (fun v => d v=k), z v := by
    rw [Finset.sum_filter]
    exact endpointRow_coeff ..
  have cover : P.support ⊆ T := by
    intro k hk
    by_contra hn
    have hz : A.filter (fun v => d v=k)=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hv h
      exact hn (h ▸ Finset.mem_image_of_mem d hv)
    exact (Polynomial.mem_support_iff.mp hk) (by rw [coeff,hz,Finset.sum_empty])
  have grouped : (∑ v ∈ A, endpointAtom c u a θ v * K (d v)) =
      ∑ k ∈ T, monomial k (P.coeff k) * K k := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := T) (fun v hv => Finset.mem_image_of_mem d hv)
      (fun v => endpointAtom c u a θ v * K (d v))]
    apply Finset.sum_congr rfl
    intro k _
    rw [coeff,map_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v hv
    change monomial (d v) (z v)*K (d v)=_
    rw [(Finset.mem_filter.mp hv).2]
  change endpointNorm (∑ v ∈ A, endpointAtom c u a θ v * K (d v)) ≤ endpointNorm P*C
  rw [grouped,norm_over_cover P T cover,Finset.sum_mul]
  apply (endpointNorm_sum ..).trans (Finset.sum_le_sum (fun k _ => ?_))
  apply (endpointNorm_mul ..).trans
  rw [endpointNorm_monomial]
  exact mul_le_mul_of_nonneg_left (hK k) (norm_nonneg _)

noncomputable def wallRow (c u a θ : ℝ) (h n : ℕ) :=
  endpointRow c u a θ ((words n).filter (BallotFrom h))

theorem ballot_split (h : ℕ) (v w : List Bool) :
    BallotFrom h (v++w) ↔ BallotFrom h v ∧ BallotFrom (h+v.length-2*(wordParts v).length) w := by
  have front (hh : BallotFrom h (v++w)) : BallotFrom h v := by
    rw [ballot_iff_heights,heights_append] at hh
    exact (ballot_iff_heights ..).mpr fun x hx => hh x (List.mem_append_left _ hx)
  by_cases hv : BallotFrom h v
  · have hn : 0 ≤ (h:ℤ)+displacement v := by
      have H := endpoint_mem_vertices (h:ℤ) v
      rcases List.mem_cons.mp H with H|H
      · omega
      · exact (ballot_iff_heights h v).mp hv _ H
    have he : ((h+v.length-2*(wordParts v).length : ℕ):ℤ) = (h:ℤ)+displacement v := by
      have := displacement_length v
      omega
    simp only [ballot_iff_heights,heights_append,List.forall_mem_append,he]
  · exact iff_of_false (fun hh => hv (front hh)) (fun hh => hv hh.1)

theorem wallRow_split (c u a θ : ℝ) (h m n : ℕ) :
    wallRow c u a θ h (m+n) =
      ∑ v ∈ (words m).filter (BallotFrom h), endpointAtom c u a θ v *
        wallRow c (u-c*m) (a-m) θ (h+m-2*(wordParts v).length) n := by
  unfold wallRow endpointRow
  rw [Finset.sum_filter,split_word_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have hl := mem_words.mp hv
  simp only [ballot_split,hl,endpointAtom_append]
  by_cases hb : BallotFrom h v
  · simp only [hb,true_and,ite_true,Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]
  · simp [hb]

theorem wallRow_compose (c u a θ : ℝ) (h m n : ℕ) {C : ℝ}
    (hC : ∀ b, endpointNorm (wallRow c (u-c*m) (a-m) θ b n) ≤ C) :
    endpointNorm (wallRow c u a θ h (m+n)) ≤ endpointNorm (wallRow c u a θ h m)*C := by
  rw [wallRow_split]
  exact endpoint_continuation c u a θ _ (fun k => wallRow c (u-c*m) (a-m) θ (h+m-2*k) n) (fun _ => hC _)

/-- Any number of blocks, with the early prefix left at its own endpoint norm.
The intercept and the rank labels advance with the actual step index. -/
theorem wallRow_blocks (c u a θ : ℝ) (h p L k : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (H : ∀ j < k, ∀ b, endpointNorm (wallRow c (u-c*(p+j*L:ℕ)) (a-(p+j*L:ℕ)) θ b L) ≤ ρ) :
    endpointNorm (wallRow c u a θ h (p+k*L)) ≤ endpointNorm (wallRow c u a θ h p)*ρ^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul,← Nat.add_assoc,pow_succ,← mul_assoc]
    exact (wallRow_compose c u a θ h (p+k*L) L (H k (Nat.lt_succ_self k))).trans
      (mul_le_mul_of_nonneg_right (ih (fun j hj => H j (Nat.lt_succ_of_lt hj))) hρ)

/-- The surviving tilted prefix followed by consecutive paired blocks.
Only the down probabilities in those blocks enter the two rectangle bounds. -/
theorem paired_wall_powers (c u a θ : ℝ) (h p l k : ℕ) :
    let D := fun i : ℕ => upChance (-(u-c*i))
    let X := endpointNorm (wallRow c u a θ h (p+k*(2*l)))
    let W := ∑ v ∈ (words p).filter (BallotFrom h), signMass c u v
    ((∀ i, p ≤ i → i < p+k*(2*l) → 9/25 ≤ D i ∧ D i ≤ 31/50) →
      X ≤ W*((1+exp (-(1/5)*l*sin (l*θ/2)^2))/2)^k) ∧
    ((∀ i, p ≤ i → i < p+k*(2*l) → 11/50 ≤ D i ∧ D i ≤ 17/25) →
      X ≤ W*((1+exp (-(3/25)*l*sin (l*θ/2)^2))/2)^k) := by
  dsimp only
  have indices {j i : ℕ} (hj : j < k) (hi : i < 2*l) :
      p ≤ p+j*(2*l)+i ∧ p+j*(2*l)+i < p+k*(2*l) := by
    have he := Nat.mul_le_mul_right (2*l) (show j+1 ≤ k by omega)
    rw [Nat.add_mul,one_mul] at he
    omega
  have label (j i : ℕ) : u-c*(p+j*(2*l):ℕ)-c*i=u-c*(p+j*(2*l)+i:ℕ) := by push_cast; ring
  constructor <;> intro H
  · apply (wallRow_blocks c u a θ h p (2*l) k (by positivity) _).trans
      (mul_le_mul_of_nonneg_right (endpointRow_mass ..) (by positivity))
    intro j hj b
    apply (tilted_retained_pair _ _ _ θ l _ (Finset.filter_subset ..)).1
    intro i hi
    simpa only [← label j i] using H _ (indices hj hi).1 (indices hj hi).2
  · apply (wallRow_blocks c u a θ h p (2*l) k (by positivity) _).trans
      (mul_le_mul_of_nonneg_right (endpointRow_mass ..) (by positivity))
    intro j hj b
    apply (tilted_retained_pair _ _ _ θ l _ (Finset.filter_subset ..)).2
    intro i hi
    simpa only [← label j i] using H _ (indices hj hi).1 (indices hj hi).2

end CentralUnimodality.MarkedExcursion
