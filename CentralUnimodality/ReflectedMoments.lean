module

public import CentralUnimodality.CellPrimitives
public import CentralUnimodality.ReflectedBase

/-! A bounded pair of cell expectations gives the reflected inequalities
at every sufficiently large size under the induction hypothesis that the
row is unimodal. The integer cutoff uses squared lengths throughout. -/
@[expose] public section

namespace CentralUnimodality.Witness

open Laurent

private theorem weightedSum_neg (v : Data) {n δ : ℕ} (hn : 0 < n+δ)
    (h : polyExpectation (normalizedCell n δ) 0 (coefficients v.B v.t v.roots) < 0) :
    v.weightedSum (boundary n δ) (fun k => rankCount (2*n+δ) (n*(n+δ)-k)) (n*(n+δ)) < 0 := by
  rw [weightedSum_expectation v n δ hn]
  have hp : 0 < (massFactor n δ:ℝ) := by exact_mod_cast massFactor_pos n δ
  exact mul_neg_of_pos_of_neg (div_pos hp (cellScale_pos hn)) h

private theorem boundary_mono (n δ : ℕ) (hn : 0 < n+δ) : Monotone (boundary n δ) := by
  intro i j hij
  unfold boundary
  apply div_le_div_of_nonneg_right _ (cellScale_pos hn).le
  exact_mod_cast (show leftEndpoint n δ i ≤ leftEndpoint n δ j by
    unfold leftEndpoint; exact add_le_add (by exact_mod_cast hij) le_rfl)

theorem reflected_cut_le_degree {n δ j : ℕ} (hδ : δ ≤ 1)
    (hj : (j:ℝ)+3*((n+δ:ℕ):ℝ)+(1-δ) ≤ (131/250)*cellScale (n+δ)) :
    j ≤ n*(n+δ) := by
  let N : ℝ := (n+δ:ℕ)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hs : Real.sqrt (2*N) ≤ 1+N/2 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity,by nlinarith [sq_nonneg (1-N/2)]⟩
  have hscale : cellScale (n+δ) ≤ N^2+2*N := by
    change 2*N*Real.sqrt (2*N) ≤ N^2+2*N
    nlinarith only [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*N)]
  have factor : (131/250:ℝ)*cellScale (n+δ) ≤ 1*(N^2+2*N) :=
    mul_le_mul (by norm_num) hscale (by unfold cellScale; positivity) zero_le_one
  have hδ' : (δ:ℝ) ≤ 1 := by exact_mod_cast hδ
  have part := mul_le_mul_of_nonneg_right hδ' hN
  change (j:ℝ)+3*N+(1-δ) ≤ _ at hj
  have h' : (j:ℝ) ≤ (N-δ)*N := by nlinarith only [hj,factor,part,hδ']
  have hn' : N-(δ:ℝ) = n := by simp [N]
  rw [hn'] at h'
  dsimp only [N] at h'
  exact_mod_cast h'

theorem reflected_large_of_expectations {n δ : ℕ} (hδ : δ ≤ 1) (hn : 96 ≤ n+δ)
    (h₁ : polyExpectation (normalizedCell n δ) 0 (coefficients first.B first.t first.roots) < 0)
    (h₂ : polyExpectation (normalizedCell n δ) 0 (coefficients second.B second.t second.roots) < 0)
    (hu : UnimodalOn (rankCount (2*n+δ)) 0 (n*(n+δ))) {i j : ℕ} (hij : i < j)
    (hcut : (250*(i+j+3*(n+δ)+(1-δ)))^2 ≤ 131^2*(2*(n+δ))^3) :
    rankCount (2*n+δ) (n*(n+δ)-i) ≤ rankCount (2*n+δ) (n*(n+δ)-j) := by
  let N := n+δ
  have hN : (96:ℝ) ≤ N := by exact_mod_cast hn
  have hscale_pos := cellScale_pos (N := N) (by omega)
  have hscale : (cellScale N)^2 = (2*(N:ℝ))^3 := by
    rw [cellScale,mul_pow,Real.sq_sqrt (by positivity)]; ring
  have hcut' : (250*((i:ℝ)+j+3*(N:ℝ)+(1-δ)))^2 ≤ (131*cellScale N)^2 := by
    rw [mul_pow (131:ℝ),hscale]
    exact_mod_cast (show (250*(i+j+3*N+(1-δ)))^2 ≤ 131^2*(2*N)^3 from hcut)
  have hδ' : (δ:ℝ) ≤ 1 := by exact_mod_cast hδ
  have hleft : 0 ≤ 250*((i:ℝ)+j+3*(N:ℝ)+(1-δ)) :=
    mul_nonneg (by norm_num) (add_nonneg (by positivity) (sub_nonneg.mpr hδ'))
  have hc := (sq_le_sq₀ hleft (mul_nonneg (by norm_num) hscale_pos.le)).mp hcut'
  have hdeg : j ≤ n*N := reflected_cut_le_degree hδ (by
    change (j:ℝ)+3*(N:ℝ)+(1-δ) ≤ (131/250)*cellScale N
    linarith only [hc,Nat.cast_nonneg (α := ℝ) i])
  let D := n*N
  let f (k : ℕ) := rankCount (2*n+δ) (D-k)
  let M := ∑ k ∈ Finset.range (D+1), f k
  have hf (k : ℕ) (hk : k ≤ D) : f k ≤ M :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (f i)) (Finset.mem_range.mpr (by omega) : k ∈ Finset.range (D+1))
  apply reflected_from_two_witnesses hu.reverse hij hdeg hf (boundary n δ) (boundary_mono n δ (by omega)) _ _
    (weightedSum_neg first (by omega) h₁)
    (weightedSum_neg second (by omega) h₂)
  · unfold boundary leftEndpoint
    simp only [Rat.cast_add,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_natCast]
    apply div_nonneg _ hscale_pos.le
    change 0 ≤ (i:ℝ)+(3*(N:ℝ)/2+ - (δ:ℝ)/2)
    linarith [Nat.cast_nonneg (α := ℝ) i]
  · unfold boundary leftEndpoint
    simp only [Rat.cast_add,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_natCast,← add_div]
    apply (div_le_iff₀ hscale_pos).mpr
    change (i:ℝ)+(3*(N:ℝ)-δ)/2+((j:ℝ)+(3*(N:ℝ)-δ)/2) ≤ 0.524*cellScale N
    linarith only [hc]

theorem reflected_large_of_checks {n δ : ℕ} (hδ : δ ≤ 1) (hn : 96 ≤ n+δ)
    (h₁ : checkPair first δ (1/10000000000) = true)
    (h₂ : checkPair second δ (7/1000000) = true)
    (hu : UnimodalOn (rankCount (2*n+δ)) 0 (n*(n+δ))) {i j : ℕ} (hij : i < j)
    (hcut : (250*(i+j+3*(n+δ)+(1-δ)))^2 ≤ 131^2*(2*(n+δ))^3) :
    rankCount (2*n+δ) (n*(n+δ)-i) ≤ rankCount (2*n+δ) (n*(n+δ)-j) :=
  reflected_large_of_expectations hδ hn ((checkPair_sound first hδ hn h₁).trans_lt (by norm_num))
    ((checkPair_sound second hδ hn h₂).trans_lt (by norm_num)) hu hij hcut

end CentralUnimodality.Witness
