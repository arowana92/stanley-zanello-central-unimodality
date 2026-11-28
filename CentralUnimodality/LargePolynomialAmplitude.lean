module

public import CentralUnimodality.CertifiedCurveResidual
public import CentralUnimodality.NormalizedCells

/-! A uniform polynomial approximation to the actual signed staircase
amplitude on the full central frequency interval, for both parities. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Real Set ReturnSplit Witness

theorem scaled_trial_bound {n δ : ℕ} (hδ : δ≤1) (hn : 10^54≤n+δ)
    {ξ u : ℝ} (hξ : |ξ|≤4096) (hu : u∈Icc (0:ℝ) 256) (cube : u^3=ξ^2) :
    |signedAmplitude n δ (ξ/cellScale (n+δ))-value candidate u|≤1/10^10 := by
  let N := n+δ
  let S := cellScale N
  let τ := u/(N:ℝ)
  have hn' : 0<N := by dsimp [N]; omega
  have pos : 0<(N:ℝ) := by exact_mod_cast hn'
  have big : (10:ℝ)^54≤N := by exact_mod_cast hn
  have root : (10:ℝ)^27≤sqrt N := Real.le_sqrt_of_sq_le (by linarith only [big])
  have spos : 0<S := cellScale_pos hn'
  have norm : S^2=(2*(N:ℝ))^3 := by
    dsimp [S,cellScale]; rw [mul_pow,Real.sq_sqrt (by positivity)]; ring
  have t0 : 0≤τ := div_nonneg hu.1 pos.le
  have endpt : τ*(N:ℝ)=u := div_mul_cancel₀ _ pos.ne'
  have step (k : ℕ) (hk : k≤N) : τ*k∈Icc (0:ℝ) 256 :=
    ⟨mul_nonneg t0 (Nat.cast_nonneg k),
     ((mul_le_mul_of_nonneg_left (by exact_mod_cast hk : (k:ℝ)≤N) t0).trans_eq endpt).trans hu.2⟩
  have freq : |ξ/S| * (N:ℝ)*sqrt N≤4096 := by
    have compare : (N:ℝ)*sqrt N≤S := by
      apply mul_le_mul (by linarith only [pos]) (Real.sqrt_le_sqrt (by linarith only [pos])) (sqrt_nonneg _) (by positivity)
    rw [abs_div,abs_of_pos spos,div_mul_eq_mul_div,div_mul_eq_mul_div,div_le_iff₀ spos,mul_assoc]
    exact mul_le_mul hξ compare (by positivity) (by norm_num)
  have phase : (ξ/S/2)^2=τ^3/32 := by
    dsimp [τ]; rw [div_pow,div_pow,div_pow,norm,← cube]; field_simp; ring
  have angle : |ξ/S/2| * (2*N+1:ℕ)≤1 := by
    have root' : (4096:ℝ)≤sqrt (2*N) := Real.le_sqrt_of_sq_le (by linarith only [big])
    have cap := mul_le_mul_of_nonneg_left root' (show 0≤2*(N:ℝ) by positivity)
    rw [abs_div,abs_div,abs_of_pos spos,abs_of_pos (by norm_num : (0:ℝ)<2),div_div,div_mul_eq_mul_div,
      div_le_iff₀ (by positivity),one_mul]
    push_cast
    have h := mul_le_mul_of_nonneg_right hξ (show 0≤2*(N:ℝ)+1 by positivity)
    dsimp only [S,cellScale]
    linarith only [h,cap,big]
  have H := signed_curve_bound (n:=n) (δ:=δ) hδ hn' (θ:=ξ/S) (τ:=τ) (ξ:=4096)
    (K:=18000000) (M:=2) (e:=15/10^16) (L:=36/10^14) t0 phase angle freq
    (value_continuous candidate) (by norm_num) (fun k hk => (candidate_bounds (step k hk)).1)
    (fun j hj => split_quadratic (step j hj))
    (curve_value_bound (step N le_rfl)) (fun x hx y hy => curve_lipschitz
      ⟨hx.1,hx.2.trans (step N le_rfl).2⟩ ⟨hy.1,hy.2.trans (step N le_rfl).2⟩)
  change |signedAmplitude n δ (ξ/S)-value candidate (τ*(N:ℝ))|≤
    (1+4096/2)*(15/10^16)+(36/10^14)*(τ*(N:ℝ))+4*sqrt N*
      ((1+2)*inputCost τ N+18000000*τ^2*(N:ℝ)/8) at H
  rw [endpt,inputCost_rescale hn'] at H
  let C := 3*(u^3+u^6)+18000000*u^2/8
  have eq : 4*sqrt N*((1+2)*((u^3+u^6)/(N:ℝ))+18000000*τ^2*(N:ℝ)/8)=4*C/sqrt N := by
    dsimp [τ,C]
    field_simp [pos.ne',(sqrt_pos.mpr pos).ne']
    rw [show (sqrt (N:ℝ))^2=(N:ℝ) from sq_sqrt pos.le]; ring
  rw [eq] at H
  have cub := pow_le_pow_left₀ hu.1 hu.2 3
  have six := pow_le_pow_left₀ hu.1 hu.2 6
  have two := pow_le_pow_left₀ hu.1 hu.2 2
  have tail : 4*C/sqrt N≤4/10^12 := by
    apply (div_le_iff₀ (sqrt_pos.mpr pos)).mpr
    dsimp [C]
    linarith only [cub,six,two,root]
  exact H.trans (by linarith only [tail,hu.2])

theorem amplitude_4096 {n δ : ℕ} (hδ : δ≤1) (hn : 10^54≤n+δ) {ξ : ℝ} (hξ : |ξ|≤4096) :
    |signedAmplitude n δ (ξ/cellScale (n+δ))-value candidate (|ξ|^(2/3:ℝ))|≤1/10^10 := by
  have hn₀ := abs_nonneg ξ
  have cube : (|ξ|^(2/3:ℝ))^3=ξ^2 := by
    rw [← rpow_natCast _ 3,← rpow_mul hn₀]
    norm_num [sq_abs]
  have bound : |ξ|^(2/3:ℝ)≤256 := by
    by_contra! h
    have H := pow_lt_pow_left₀ h (by norm_num : (0:ℝ)≤256) (by decide : 3≠0)
    rw [cube,← sq_abs] at H
    linarith only [H,pow_le_pow_left₀ hn₀ hξ 2]
  exact scaled_trial_bound hδ hn hξ ⟨rpow_nonneg hn₀ _,bound⟩ cube

end CentralUnimodality.PolynomialTrial
