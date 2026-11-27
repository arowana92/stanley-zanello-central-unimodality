module

public import CentralUnimodality.LateRankInversion
public import CentralUnimodality.LateArcIntegrals

/-! The absolute mass and the signed first and second differences of the
late event, after its change of law. All four outer arc volumes and the
Gamma term come from the Fourier integral over the actual rank variable. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory Set

noncomputable def lateFourierBudget (d : ℝ) (r : ℕ) :=
  (3*((14/25)/(17/2)*d)^(-3*((r:ℝ)+1)/2)*Gamma (3*((r:ℝ)+1)/2) +
    ∑ s : Fin 4, exp (-(pairRate s false:ℝ)*d)*
      (2*((outerHi s)^(r+1)-(outerLo s)^(r+1))/((r:ℝ)+1)))/π

private theorem arc_cover {t : ℝ} (hlo : 1/8 ≤ t) (hhi : t ≤ π) :
    ∃ s : Fin 4, outerLo s ≤ t ∧ t ≤ outerHi s := by
  by_cases h₁ : t ≤ 9/50
  · exact ⟨0,hlo,h₁⟩
  by_cases h₂ : t ≤ 1/4
  · exact ⟨1,(le_of_not_ge h₁),h₂⟩
  by_cases h₃ : t ≤ 1/2
  · exact ⟨2,(le_of_not_ge h₂),h₃⟩
  exact ⟨3,(le_of_not_ge h₃),hhi⟩

/-- The explicit three Fourier losses for paths surviving through T and
crossing later, normalized by the exact change of rank parameter at the saddle.
The bound holds at all integer ranks, also for the adjacent sites in (5). -/
theorem late_rank_moments {c z b U : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) (hb : 0 ≤ b)
    (hb' : b ≤ 6/25) (hU : 0 ≤ U) (hU' : U ≤ 6/25)
    {m L T : ℕ} (hL : 0<L) (hLT : L<T) (hT : T≤m)
    (hcap : (c+z)*m-b ≤ U) (hcut : b*m ≤ (tanh (c*m)/m+z)*prefixLabels m T)
    (r : Fin 3) (k : ℤ) :
    rankChange c z (meanRank c m) m * |rankDifference r k (eventSiteMass (c+z) m (lateHitEvent m T))| ≤
      exp (z^2*labelSquares m/2-m*b^2/2)*(2*U+(4/5)/√L)*lateFourierBudget (T-L:ℕ) r.val := by
  let d : ℝ := (T-L:ℕ)
  let a : ℝ := (14/25)/(17/2)*d
  let N := exp (z^2*labelSquares m/2-m*b^2/2)*(2*U+(4/5)/√L)
  let f (s : Fin 4) (θ : ℝ) := exp (-(pairRate s false:ℝ)*d)*lateOuterKernel s r.val θ
  let g (θ : ℝ) := (2*N)*(lateInnerKernel a r.val θ+∑ s : Fin 4, f s θ)
  have hd : 0<d := by dsimp [d]; exact_mod_cast (Nat.sub_pos_of_lt hLT)
  have ha : 0<a := by dsimp [a]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hf (s : Fin 4) (θ : ℝ) : 0 ≤ f s θ := by
    apply mul_nonneg (exp_pos _).le
    unfold lateOuterKernel
    by_cases h : |θ| ∈ Icc (outerLo s) (outerHi s) <;> simp [h]
  have hin (θ : ℝ) : 0 ≤ lateInnerKernel a r.val θ := by dsimp [lateInnerKernel]; positivity
  have hsum (θ : ℝ) : 0 ≤ ∑ s : Fin 4, f s θ := Finset.sum_nonneg (fun s _ => hf s θ)
  have hg (θ : ℝ) : 0 ≤ g θ := mul_nonneg (by positivity) (add_nonneg (hin θ) (hsum θ))
  have hfi (s : Fin 4) : Integrable (f s) := (late_outer_integral s r.val).1.const_mul _
  have hsi : Integrable (fun θ => ∑ s : Fin 4, f s θ) := integrable_finsetSum _ (fun s _ => hfi s)
  have hgi : Integrable g := ((late_inner_integral ha r.val).1.add hsi).const_mul _
  let R := rankChange c z (meanRank c m) m
  have hdom (θ : ℝ) (hθ : θ ∈ Ioc (-π) π) : R*‖lateRankCharacter (c+z) θ m T‖*|θ|^r.val ≤ g θ := by
    obtain ⟨inner,outer⟩ := late_rank_arcs hc hz hb hb' hU hU' θ hL hLT.le hT hcap hcut
    have hp : 0 ≤ |θ|^r.val := by positivity
    by_cases hsmall : |θ| ≤ 1/8
    · apply (mul_le_mul_of_nonneg_right (inner hsmall) hp).trans
      have e : -(innerPairRate |θ|)*d= -a*|θ|^(2/3:ℝ) := by dsimp [innerPairRate,a]; ring
      change N*(2*exp (-(innerPairRate |θ|)*d))*_ ≤ _
      rw [e]
      have h := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (a:=lateInnerKernel a r.val θ) (hsum θ)) (by positivity : 0 ≤ 2*N)
      dsimp only [g,lateInnerKernel] at h ⊢
      linarith only [h]
    · obtain ⟨s,hlo,hhi⟩ := arc_cover (le_of_not_ge hsmall) (abs_le.mpr ⟨hθ.1.le,hθ.2⟩)
      apply (mul_le_mul_of_nonneg_right (outer s hlo hhi) hp).trans
      have H := Finset.single_le_sum (s:=Finset.univ) (f:=fun i => f i θ) (fun i _ => hf i θ) (Finset.mem_univ s)
      have hh : f s θ ≤ lateInnerKernel a r.val θ+∑ i : Fin 4, f i θ := by linarith only [H,hin θ]
      have per : f s θ=exp (-(pairRate s false:ℝ)*d)*|θ|^r.val := by simp [f,lateOuterKernel,Set.mem_Icc.mpr ⟨hlo,hhi⟩]
      have H' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*N)
      rw [per] at H'
      change N*(2*exp (-(pairRate s false:ℝ)*d))*_ ≤ _
      dsimp only [g]; linarith only [H']
  have H := late_difference_integral (c+z) m T (rankChange_pos c z (meanRank c m) m).le r k hgi hg hdom
  have hInt : (∫ θ, g θ)=(2*π)*N*lateFourierBudget d r.val := by
    dsimp only [g]
    rw [integral_const_mul,integral_add (late_inner_integral ha r.val).1 hsi,
      (late_inner_integral ha r.val).2,integral_finsetSum _ (fun s _ => hfi s)]
    simp only [f,integral_const_mul,(late_outer_integral _ r.val).2]
    dsimp only [lateFourierBudget,a]
    field_simp [pi_ne_zero]
  rw [hInt] at H
  change R*|rankDifference r k _| ≤ N*lateFourierBudget d r.val
  exact le_of_mul_le_mul_left (a:=2*π) (by simpa only [mul_assoc] using H) (by positivity)

end CentralUnimodality.MarkedExcursion
