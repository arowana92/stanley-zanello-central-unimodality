module

public import CentralUnimodality.SmoothReturnInverse
public import CentralUnimodality.FourierCertificate
public import CentralUnimodality.AliasTail
import Mathlib.Tactic.FieldSimp

/-! An error estimate for the actual signed ballot amplitude at either
parity. At a frequency of order `N^(-3/2)`, the coefficient on the
residual stays bounded as N grows. -/
@[expose] public section

namespace CentralUnimodality
open PowerSeries

noncomputable def parityResidual (ω : ℝ) (V : PowerSeries ℂ) (σ j : ℕ) : ℂ :=
  coeff (2*j+σ) (fairSeries (areaCharacter ω) words - fairSeries (areaCharacter ω) bridges * V)

theorem sum_even_indices (f : ℕ → ℂ) (hz : ∀ j, f (2*j+1)=0) (N σ : ℕ) (hs : σ≤1) :
    (∑ i ∈ Finset.range (2*N+σ+1), f i) = ∑ j ∈ Finset.range (N+1), f (2*j) := by
  have base (k : ℕ) : (∑ i ∈ Finset.range (2*k+1), f i)=∑ j ∈ Finset.range (k+1), f (2*j) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2*(k+1)+1=(2*k+1)+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,
        ih,hz,add_zero,Finset.sum_range_succ (n:=k+1)]
      rfl
  rcases (show σ=0 ∨ σ=1 by omega) with rfl|rfl
  · simpa using base N
  · rw [Finset.sum_range_succ,hz,add_zero,base]

noncomputable def inverseAt (ω : ℝ) (N : ℕ) (E : ℕ → ℂ) : ℂ :=
  E N-∑ j ∈ Finset.range (N+1), returnSymbol ω j*E (N-j)

theorem strict_error_eq_inverseAt (ω : ℝ) (V : PowerSeries ℂ) (N σ : ℕ) (hs : σ≤1) :
    coeff (2*N+σ) (fairSeries (areaCharacter ω) strictWords - V)=
      inverseAt ω N (parityResidual ω V σ) := by
  let R := fairSeries (areaCharacter ω) words - fairSeries (areaCharacter ω) bridges * V
  let H := fairSeries (areaCharacter ω) firstReturns
  let f (i : ℕ) := coeff i H * coeff (2*N+σ-i) R
  have hz (j : ℕ) : f (2*j+1)=0 := by
    simp only [f,H,coeff_walkSeries,firstReturns_odd_empty,Finset.sum_empty,mul_zero,zero_mul]
  have he : coeff (2*N+σ) (H*R)=∑ j ∈ Finset.range (N+1),
      returnSymbol ω j*parityResidual ω V σ (N-j) := by
    rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,sum_even_indices f hz N σ hs]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have idx : 2*N+σ-2*j=2*(N-j)+σ := by omega
    dsimp only [f,returnSymbol,parityResidual]
    rw [idx]
  have id := walkSeries_residual (2:ℂ)⁻¹ (areaCharacter ω) (areaCharacter_zero _) (areaCharacter_add _) V
  change fairSeries (areaCharacter ω) strictWords-V=(1-H)*R at id
  rw [id,sub_mul,one_mul,map_sub,he]
  rfl

theorem smooth_strict_error (ω : ℝ) (V : PowerSeries ℂ) (N σ : ℕ) (hs : σ≤1) {L : ℝ}
    (h : ∀ j≤N, ‖parityResidual ω V σ N-parityResidual ω V σ (N-j)‖≤j*L) :
    ‖coeff (2*N+σ) (fairSeries (areaCharacter ω) strictWords - V)‖ ≤
      (survival N+N*(|ω|/2))*‖parityResidual ω V σ N‖+(N*survival N)*L := by
  rw [strict_error_eq_inverseAt _ _ _ _ hs]
  exact inverse_smooth_bound ω N _ h

theorem smooth_amplitude_error (n δ : ℕ) (hδ : δ≤1) (θ : ℝ) (V : PowerSeries ℂ) {L : ℝ}
    (h : ∀ j≤n+δ, ‖parityResidual (θ/2) V (1-δ) (n+δ)-
      parityResidual (θ/2) V (1-δ) (n+δ-j)‖≤j*L) :
    |signedAmplitude n δ θ-residualAmplitude (2*n+δ) V| ≤
      (1+(n+δ:ℕ)*(|θ|/4)/survival (n+δ))*‖parityResidual (θ/2) V (1-δ) (n+δ)‖ +
      (n+δ:ℕ)*L := by
  let N := n+δ
  let σ := 1-δ
  have hlen : 2*n+δ+1=2*N+σ := by dsimp [N,σ]; omega
  have hhalf : (2*n+δ+1)/2=N := by dsimp [N]; omega
  have hh := smooth_strict_error (θ/2) V N σ (by dsimp [σ]; omega) h
  rw [map_sub] at hh
  rw [signedAmplitude,residualAmplitude,← sub_div,abs_div,hhalf,abs_of_pos (survival_pos _),hlen,← Complex.sub_re]
  apply (div_le_div_of_nonneg_right ((Complex.abs_re_le_norm _).trans hh) (survival_pos N).le).trans_eq
  simp only [abs_div,abs_of_pos (show (0:ℝ)<2 by norm_num)]
  change _ = (1+N*(|θ|/4)/survival N)*‖parityResidual (θ/2) V σ N‖ + N*L
  field_simp [(survival_pos N).ne']
  ring

/-- Scale the frequency and time variation before the estimate. The final
right hand side is independent of the number of step pairs. -/
theorem uniform_smooth_amplitude {n δ : ℕ} (hδ : δ≤1) (hN : 0<n+δ)
    (θ : ℝ) (V : PowerSeries ℂ) {ξ e b : ℝ}
    (hfreq : |θ| * (n+δ:ℕ)*Real.sqrt (n+δ:ℕ) ≤ ξ)
    (hend : ‖parityResidual (θ/2) V (1-δ) (n+δ)‖≤e)
    (hvar : ∀ j≤n+δ, ‖parityResidual (θ/2) V (1-δ) (n+δ)-
      parityResidual (θ/2) V (1-δ) (n+δ-j)‖≤j*(b/(n+δ:ℕ))) :
    |signedAmplitude n δ θ-residualAmplitude (2*n+δ) V| ≤ (1+ξ/2)*e+b := by
  let N := n+δ
  have hpos : (0:ℝ)<(N:ℕ) := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_left (survival_inv_le hN)
    (show 0≤(N:ℝ)*(|θ|/4) by positivity)
  have hf : |θ| * (N:ℝ)*Real.sqrt N≤ξ := hfreq
  have factor : 1+(N:ℝ)*(|θ|/4)/survival N≤1+ξ/2 := by
    rw [div_eq_mul_inv]; linarith only [hmul,hf]
  have hξ := (show 0≤|θ| * (N:ℝ)*Real.sqrt N by positivity).trans hf
  have bound := smooth_amplitude_error n δ hδ θ V hvar
  apply bound.trans
  change (1+(N:ℝ)*(|θ|/4)/survival N)*_+(N:ℝ)*(b/(N:ℝ))≤_
  rw [show (N:ℝ)*(b/N)=b by field_simp [hpos.ne']]
  exact add_le_add (mul_le_mul factor hend (norm_nonneg _) (by positivity)) le_rfl

end CentralUnimodality
