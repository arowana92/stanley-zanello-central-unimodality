module

public import CentralUnimodality.TiltedWallProducts
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! A wall may retain any subset of a free endpoint fiber. Its
character is controlled by the two unrestricted harmonics at that
endpoint, using the quadratic upper bound for the positive cosine. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Polynomial

private theorem cosine_positive_part (x : ℝ) :
    max 0 (cos x) ≤ 3/8+cos x/2+cos (2*x)/8 := by
  rw [cos_two_mul]; apply max_le
  · nlinarith only [sq_nonneg (1+cos x)]
  · nlinarith only [sq_nonneg (1-cos x)]

private noncomputable def character {α : Type*} (s : Finset α) (p x : α→ℝ) :=
  ∑ i ∈ s, (p i:ℂ)*phase (x i)

private theorem rotate_character {α : Type*} (s : Finset α) (p x : α→ℝ) (t : ℝ) :
    (phase t*character s p x).re=∑ i ∈ s, p i*cos (t+x i) := by
  rw [character,Finset.mul_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show phase t*((p i:ℂ)*phase (x i))=(p i:ℂ)*phase (t+x i) by rw [phase_add]; ring]
  rw [Complex.re_ofReal_mul,phase,Complex.exp_ofReal_mul_I_re]

private theorem harmonic_fiber {α : Type*} {s t : Finset α} (ht : t⊆s) (p x : α→ℝ)
    (hp : ∀ i∈s, 0≤p i) :
    ‖character t p x‖ ≤ 3/8*(∑ i ∈ s, p i)+‖character s p x‖/2+
      ‖character s p (fun i => 2*x i)‖/8 := by
  let z := character t p x
  let a := -z.arg
  have rot : phase a*z=(‖z‖:ℂ) := by
    have H := Complex.norm_mul_exp_arg_mul_I z
    change (‖z‖:ℂ)*phase z.arg=z at H
    calc
      phase a*z = phase a*((‖z‖:ℂ)*phase z.arg) := congrArg (phase a*·) H.symm
      _ = (‖z‖:ℂ)*(phase a*phase z.arg) := by ring
      _ = _ := by rw [← phase_add]; simp [a,phase]
  have line (S : Finset α) (y : α→ℝ) (b : ℝ) :
      ∑ i ∈ S, p i*cos (b+y i) ≤ ‖character S p y‖ := by
    rw [← rotate_character]
    exact (Complex.re_le_norm _).trans_eq (by rw [norm_mul,phase_norm,one_mul])
  have selected : ‖z‖ = ∑ i ∈ t, p i*cos (a+x i) := by
    rw [← rotate_character]; exact (congrArg Complex.re rot).symm
  rw [← show z=character t p x from rfl,selected]
  apply (Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (le_max_right 0 _) (hp i (ht hi)))).trans
  apply (Finset.sum_le_sum_of_subset_of_nonneg ht (fun i hi _ => mul_nonneg (hp i hi) (le_max_left ..))).trans
  apply (Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (cosine_positive_part _) (hp i hi))).trans
  simp only [mul_add,mul_div_assoc',Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul]
  have H₁ := line s x a
  have H₂ := line s (fun i => 2*x i) (2*a)
  linarith only [H₁,H₂]

theorem retained_two_harmonics (c u a θ : ℝ) {n : ℕ} (A : Finset (List Bool)) (hA : A⊆words n) :
    endpointNorm (endpointRow c u a θ A) ≤ 3/8+
      endpointNorm (endpointRow c u a θ (words n))/2+endpointNorm (endpointRow c u a (2*θ) (words n))/8 := by
  classical
  let e (w : List Bool) := (wordParts w).length
  let S := (words n).image e
  let p := signMass c u
  let x (w : List Bool) := θ*prefixRank a w
  have coeff (V : Finset (List Bool)) (v : ℝ) (k : ℕ) :
      (endpointRow c u a v V).coeff k = character (V.filter (fun w => e w=k)) p (fun w => v*prefixRank a w) := by
    rw [endpointRow_coeff,character,Finset.sum_filter]
  have cover (V : Finset (List Bool)) (hV : V⊆words n) (v : ℝ) : (endpointRow c u a v V).support⊆S := by
    intro k hk
    by_contra hn
    have h : V.filter (fun w => e w=k)=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw he
      exact hn (he ▸ Finset.mem_image_of_mem e (hV hw))
    exact (mem_support_iff.mp hk) (by rw [coeff,h]; simp [character])
  rw [norm_over_cover _ S (cover A hA θ),norm_over_cover _ S (cover _ (fun _ h => h) θ),
    norm_over_cover _ S (cover _ (fun _ h => h) (2*θ))]
  have mass : (∑ k ∈ S, ∑ w ∈ (words n).filter (fun w => e w=k), p w)=1 :=
    (Finset.sum_fiberwise_of_maps_to (t:=S) (fun w hw => Finset.mem_image_of_mem e hw) p).trans (signMass_total ..)
  have H (k : ℕ) := harmonic_fiber (Finset.filter_subset_filter (fun w => e w=k) hA) p x
    (fun w _ => (signMass_pos ..).le)
  calc
    _ ≤ ∑ k ∈ S, (3/8*(∑ w ∈ (words n).filter (fun w => e w=k), p w)+
      ‖(endpointRow c u a θ (words n)).coeff k‖/2+‖(endpointRow c u a (2*θ) (words n)).coeff k‖/8) := by
      apply Finset.sum_le_sum
      intro k _
      rw [coeff,coeff,coeff]
      simpa only [x,mul_assoc] using H k
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,mass,← Finset.sum_div,← Finset.sum_div,mul_one]

end CentralUnimodality.MarkedExcursion
