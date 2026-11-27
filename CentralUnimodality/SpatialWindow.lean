module

public import CentralUnimodality.SpatialInterpolation

/-! A mesh enclosure at any real point and the derivative sign criterion
on three spatial intervals, in the rank convention of the main theorem. -/
@[expose] public section

namespace CentralUnimodality

theorem spatial_mesh_at {Q J r : ℕ} {G h x e : ℝ} (hG : 0 ≤ G) (hh : 0 < h) (hx : 0 ≤ x)
    (A : ℕ → ℝ) (sample : ℕ → ℝ)
    (hs : ∀ i ∈ Finset.Icc ⌊x/h⌋₊ (⌊x/h⌋₊+1), |spatialDerivative Q J G A r (i*h)-sample i| ≤ e) :
    let i := ⌊x/h⌋₊
    |spatialDerivative Q J G A r x - chord (x/h-i) (sample i) (sample (i+1))| ≤
      e + h^2*spectralAllowance G Q J (r+2) (fun t => |A t|)/8 := by
  let i := ⌊x/h⌋₊
  have hl : (i:ℝ) ≤ x/h := Nat.floor_le (div_nonneg hx hh.le)
  have hu : x/h < (i:ℝ)+1 := Nat.lt_floor_add_one _
  have he : chord (x/h-i) (i*h) ((i+1:ℕ)*h) = x := by dsimp [chord]; push_cast; field_simp; ring
  have hd : ((i+1:ℕ):ℝ)*h-i*h = h := by push_cast; ring
  have H := spatial_mesh_error (Q := Q) (J := J) hG A r (i*h) ((i+1:ℕ)*h) (x/h-i)
    (sample i) (sample (i+1)) e (by linarith only [hl]) (by linarith only [hu])
    (hs i (Finset.mem_Icc.mpr ⟨le_rfl,Nat.le_succ _⟩))
    (hs (i+1) (Finset.mem_Icc.mpr ⟨Nat.le_succ _,le_rfl⟩))
  rwa [he,hd] at H

/-- The same group scale and grid are used at both endpoint sizes.
Interpolating their amplitudes interpolates every spatial derivative. -/
theorem spatial_derivative_chord (Q J r : ℕ) (G x u : ℝ) (A B : ℕ → ℝ) :
    spatialDerivative Q J G (fun t => chord u (A t) (B t)) r x =
      chord u (spatialDerivative Q J G A r x) (spatialDerivative Q J G B r x) := by
  unfold spatialDerivative chord
  simp only [add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

private theorem chord_error {u x y a b e f : ℝ} (hu : 0 ≤ u) (hv : u ≤ 1)
    (hx : |x-a| ≤ e) (hy : |y-b| ≤ f) : |chord u x y-chord u a b| ≤ chord u e f := by
  rw [show chord u x y-chord u a b = (1-u)*(x-a)+u*(y-b) by unfold chord; ring]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hv),abs_of_nonneg hu]
  exact add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hv)) (mul_le_mul_of_nonneg_left hy hu)

/-- Two measured endpoint meshes enclose the interpolated group polynomial
at every real x ≥ 0. Both space and length interpolation weights are explicit. -/
theorem spatial_group_mesh {Q J r : ℕ} {G h x u e₀ e₁ : ℝ}
    (hG : 0 ≤ G) (hh : 0 < h) (hx : 0 ≤ x) (hu : 0 ≤ u) (hv : u ≤ 1)
    (A B a b : ℕ → ℝ)
    (h₀ : ∀ i ∈ Finset.Icc ⌊x/h⌋₊ (⌊x/h⌋₊+1), |spatialDerivative Q J G A r (i*h)-a i| ≤ e₀)
    (h₁ : ∀ i ∈ Finset.Icc ⌊x/h⌋₊ (⌊x/h⌋₊+1), |spatialDerivative Q J G B r (i*h)-b i| ≤ e₁) :
    let i := ⌊x/h⌋₊
    let v := x/h-i
    |spatialDerivative Q J G (fun t => chord u (A t) (B t)) r x -
        chord u (chord v (a i) (a (i+1))) (chord v (b i) (b (i+1)))| ≤
      chord u (e₀+h^2*spectralAllowance G Q J (r+2) (fun t => |A t|)/8)
        (e₁+h^2*spectralAllowance G Q J (r+2) (fun t => |B t|)/8) := by
  dsimp only
  rw [spatial_derivative_chord]
  exact chord_error hu hv (spatial_mesh_at hG hh hx A a h₀) (spatial_mesh_at hG hh hx B b h₁)

private theorem spatial_anti (n δ : ℕ) {G : ℝ} (hG : 0 ≤ G) : Antitone (fun j => spatialSite n δ j G) := by
  intro i j hij
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (show signedAreaAtRank n δ j ≤ signedAreaAtRank n δ i by dsimp [signedAreaAtRank]; omega)

/-- Below Nyquist, the three derivative tests used by the finite-window
certificate imply weak unimodality of all the integer rank counts between
the endpoints. Spatial coordinates decrease as rank increases. -/
theorem rank_window_of_spatial_signs {n δ Q J lo a b hi : ℕ} (hδ : δ ≤ 1)
    (hn : 2049 ≤ n+δ) (hmax : n+δ ≤ 300000) (hNy : 2*J < Q)
    (hQ : 5*Witness.cellScale (n+δ) ≤ Q)
    (hJ : 2048 ≤ (2*Real.pi*Witness.cellScale (n+δ)/Q)*J)
    (hlo : lo ≤ a) (hab : a ≤ b) (hhi : b ≤ hi) (hD : hi+1 ≤ n*(n+δ))
    (hx : ((n*(n+δ)-lo:ℕ):ℝ)+(3*n+2*δ+1)/2 ≤ 0.63*Witness.cellScale (n+δ))
    {G : ℝ} (hG : 0 < G) (hGS : G ≤ Witness.cellScale (n+δ)) (A e : ℕ → ℝ)
    (he : ∀ t ∈ positiveModes J, |signedAmplitude n δ (gridFrequency Q t)-A t| ≤ e t)
    (left : ∀ x ∈ Set.Icc (spatialSite n δ a G) (spatialSite n δ lo G),
      spatialDerivative Q J G A 1 x ≤ -(0.00026+spectralAllowance G Q J 1 e))
    (middle : ∀ x ∈ Set.Icc (spatialSite n δ b G) (spatialSite n δ a G),
      spatialDerivative Q J G A 2 x ≤ -(0.95+spectralAllowance G Q J 2 e))
    (right : ∀ x ∈ Set.Icc (spatialSite n δ hi G) (spatialSite n δ b G),
      0.00026+spectralAllowance G Q J 1 e ≤ spatialDerivative Q J G A 1 x) :
    UnimodalOn (rankCount (2*n+δ)) lo hi := by
  have hm := spatial_anti n δ hG.le
  have hg := spatial_derivative_step Q J 0 G A
  rw [spatial_zero] at hg
  apply rank_window_of_fourier_signs hδ hn hmax hNy hQ hJ hlo hab hhi hD hx hG hGS A e he
  · intro j hl hu
    obtain ⟨u,hd,hs⟩ := spatial_first_difference (n := n) (δ := δ) hG A j hg
    rw [hs]
    have h := left u ⟨(hm (show j+1 ≤ a by omega)).trans hd.1.le,hd.2.le.trans (hm hl)⟩
    linarith only [h]
  · intro j hl hu
    obtain ⟨u,hd,hs⟩ := spatial_second_difference (n := n) (δ := δ) hG A j hg (spatial_derivative_step Q J 1 G A)
    rw [hs]
    exact middle u ⟨(hm (show j+2 ≤ b by omega)).trans hd.1.le,hd.2.le.trans (hm hl)⟩
  · intro j hl hu
    obtain ⟨u,hd,hs⟩ := spatial_first_difference (n := n) (δ := δ) hG A j hg
    rw [hs]
    have h := right u ⟨(hm (show j+1 ≤ hi by omega)).trans hd.1.le,hd.2.le.trans (hm hl)⟩
    linarith only [h]

end CentralUnimodality
