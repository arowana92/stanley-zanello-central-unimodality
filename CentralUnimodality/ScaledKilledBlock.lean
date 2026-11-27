module

public import CentralUnimodality.LateHitBins

/-! Separate the short first hits, whose total probability is at most one,
from the long first hits on a single parity lattice. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def fairHitMass (a j : ℕ) : ℝ := (hitWords a j).card/(2:ℝ)^j
noncomputable def cubicDecay (c : ℝ) (L j : ℕ) := Real.exp (-(c*((j:ℝ)/L)^3))

private theorem restore_hits (a L : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (L+1), fairHitMass a j*f (L-j))*(2:ℝ)^L =
      ∑ j ∈ Finset.range (L+1), (hitWords a j).card*(2:ℝ)^(L-j)*f (L-j) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have he : j+(L-j) = L := by have := Finset.mem_range.mp hj; omega
  have hp : (2:ℝ)^L = 2^j*2^(L-j) := by rw [← pow_add,he]
  rw [hp,fairHitMass]
  field_simp

theorem fairHitMass_sum {a : ℕ} (ha : 0 < a) (L : ℕ) :
    ∑ j ∈ Finset.range (L+1), fairHitMass a j ≤ 1 := by
  have hh : ((survivors a L).card:ℝ) +
      ∑ t ∈ Finset.range (L+1), (hitWords a t).card*(2:ℝ)^(L-t) = 2^L := by exact_mod_cast survivor_hit_total ha L
  have he := restore_hits a L (fun _ => 1)
  simp only [mul_one] at he
  apply le_of_mul_le_mul_right (a := (2:ℝ)^L) _ (by positivity)
  rw [he,one_mul]
  linarith only [hh,Nat.cast_nonneg (α := ℝ) (survivors a L).card]

private theorem fairHitMass_parity {a j : ℕ} (ha : 0 < a) (hj : j%2 ≠ a%2) : fairHitMass a j = 0 := by
  have hm : ¬(a ≤ j ∧ (j-a)%2 = 0) := by omega
  simp [fairHitMass,← hitNumber_exact ha,hitNumber,hm]

theorem killed_free_envelope {a : ℕ} (ha : 0 < a) (ω : ℝ) (L : ℕ) (ρ : ℕ → ℝ)
    (hρ : ∀ j ≤ L, EndpointNormBound ω j ((2:ℝ)^j*ρ j)) (s : Finset ℤ) :
    (∑ z ∈ s, ‖killedAt ω a L z‖)/(2:ℝ)^L ≤
      ρ L + ∑ t ∈ Finset.range (L+1), fairHitMass a t*ρ (L-t) := by
  apply (div_le_iff₀ (by positivity)).mpr
  have h := killed_norm_from_first_hits ω ha L (fun j => (2:ℝ)^j*ρ j) hρ s
  rw [add_mul,restore_hits,mul_comm (ρ L)]
  simpa only [mul_assoc] using h

theorem split_cubic_hits {c : ℝ} (hc : 0 ≤ c) {a L M low : ℕ}
    (ha : 0 < a) (hM : 20 ≤ M) (hML : M ≤ L) (hlow : 0 < low)
    (hlo : (low:ℝ)/400+2/(M:ℝ) ≤ 1/10) :
    (∑ t ∈ Finset.range (L+1), fairHitMass a t*cubicDecay c L (L-t)) ≤
      Real.exp (-(c*(9/10)^3)) + ∑ i ∈ Finset.range 400, binCharge c M low i := by
  let b := Real.exp (-(c*(9/10)^3))
  let u (t : ℕ) := fairHitMass a t*cubicDecay c L (L-t)
  have hLp : (0:ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have h₁ : (∑ t ∈ Finset.range (L+1), u t) ≤
      ∑ t ∈ Finset.range (L+1), (fairHitMass a t*b + if t ∈ lateHits a L then u t else 0) := by
    apply Finset.sum_le_sum
    intro t ht
    have ht' : t ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
    have hpos : 0 ≤ fairHitMass a t := by unfold fairHitMass; positivity
    by_cases h : t ∈ lateHits a L
    · simp only [ite_eq_left h]
      exact le_add_of_nonneg_left (mul_nonneg hpos (Real.exp_pos _).le)
    · rw [ite_eq_right h,add_zero]
      by_cases hpar : t%2=a%2
      · have he : 10*t ≤ L := by simp [lateHits,ht,hpar] at h; omega
        apply mul_le_mul_of_nonneg_left _ hpos
        apply Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left _ hc))
        apply pow_le_pow_left₀ (by norm_num)
        rw [Nat.cast_sub ht']
        apply (le_div_iff₀ hLp).mpr
        have he' : 10*(t:ℝ) ≤ L := by exact_mod_cast he
        linarith only [he']
      · simp [u,fairHitMass_parity ha hpar]
  have hfil : (Finset.range (L+1)).filter (· ∈ lateHits a L) = lateHits a L := by
    ext t
    simp +contextual [lateHits]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_filter,hfil] at h₁
  have h₂ := mul_le_mul_of_nonneg_right (fairHitMass_sum ha L) (show 0 ≤ b from (Real.exp_pos _).le)
  rw [one_mul] at h₂
  exact h₁.trans (add_le_add h₂ (late_hit_sum hc hM hML hlow ha hlo))

theorem scaled_free_cubic {v θ H c e : ℝ} {L : ℕ} (hv₀ : 0 ≤ v) (hθ : 0 ≤ θ)
    (hL : 0 < L) (hH : θ/2*L ≤ H) (hH' : H^2 ≤ 6) (hv : v ≤ (1-H^2/6)^2)
    (hc : c ≤ v*θ^2*(L:ℝ)^3/96) (he : v*θ^2*L/96 ≤ e) {j : ℕ} (hj : j ≤ L) :
    EndpointNormBound (θ/2) j ((2:ℝ)^j*(Real.exp e*cubicDecay c L j)) := by
  intro s
  apply (free_cubic_block hθ hH hH' hv j hj s).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [cubicEnvelope,cubicDecay,← Real.exp_add,Real.exp_le_exp]
  have hp : (0:ℝ) < L := by exact_mod_cast hL
  have hh := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ ((j:ℝ)/L)^3)
  have hs : v*θ^2*(L:ℝ)^3/96*((j:ℝ)/L)^3 = v*θ^2*j^3/96 := by field_simp
  rw [hs] at hh
  have ht := mul_le_mul_of_nonneg_left (by exact_mod_cast hj : (j:ℝ) ≤ L)
    (mul_nonneg hv₀ (sq_nonneg θ))
  linarith only [hh,ht,he]

theorem scaled_killed_cubic {v θ H c e : ℝ} {L M low : ℕ} (hv₀ : 0 ≤ v) (hθ : 0 ≤ θ)
    (hM : 20 ≤ M) (hML : M ≤ L) (hlow : 0 < low) (hlo : (low:ℝ)/400+2/(M:ℝ) ≤ 1/10)
    (hH : θ/2*L ≤ H) (hH' : H^2 ≤ 6) (hv : v ≤ (1-H^2/6)^2) (hc₀ : 0 ≤ c)
    (hc : c ≤ v*θ^2*(L:ℝ)^3/96) (he : v*θ^2*L/96 ≤ e) :
    KilledBound (θ/2) L (Real.exp e*(Real.exp (-c) + Real.exp (-(c*(9/10)^3)) +
      ∑ i ∈ Finset.range 400, binCharge c M low i)) := by
  intro a ha s
  have hL : 0 < L := by omega
  have h := killed_free_envelope ha (θ/2) L (fun j => Real.exp e*cubicDecay c L j)
    (fun _ hj => scaled_free_cubic hv₀ hθ hL hH hH' hv hc he hj) s
  have hfull : cubicDecay c L L = Real.exp (-c) := by simp [cubicDecay,(by exact_mod_cast hL.ne' : (L:ℝ) ≠ 0)]
  simp only [hfull,← mul_left_comm (Real.exp e),← Finset.mul_sum,← mul_add] at h
  have hh := add_le_add_right (split_cubic_hits hc₀ ha hM hML hlow hlo) (Real.exp (-c))
  have hb := h.trans (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le)
  rw [← add_assoc] at hb
  simpa only [mul_comm ((2:ℝ)^L)] using (div_le_iff₀ (by positivity)).mp hb

end CentralUnimodality
