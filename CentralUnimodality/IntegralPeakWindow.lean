module

public import CentralUnimodality.IntegralPeakSigns
public import CentralUnimodality.ThreeFifthsReduction

/-! The three fixed spatial intervals from the polynomial certificate
cover exactly the peak obligation used by the all-size induction. -/
@[expose] public section

namespace CentralUnimodality.Witness
open Real Set MarkedExcursion.BinArithmetic

theorem threeFifths_of_integral_signs {n δ : ℕ} (hn : 5000≤n) (hs : δ≤1)
    (left : ∀ x ∈ Icc (0.1359:ℝ) 0.339, 0≤rankIntegralOrder n δ 1 x)
    (middle : ∀ x ∈ Icc (0.333:ℝ) 0.404, rankIntegralOrder n δ 2 x≤0)
    (right : ∀ x ∈ Icc (0.398:ℝ) 0.631, rankIntegralOrder n δ 1 x≤0) :
    ThreeFifthsPeak n δ := by
  let m := 2*n+δ
  let N := n+δ
  let D := n*N
  let H := 3*n+2*δ+1
  let lo := centralStart n m
  let hi := min (D/2) ⌊(3/5)*sizeScale m⌋₊
  have nR : (5000:ℝ)≤n := by exact_mod_cast hn
  have mR : (m:ℝ)≤3*n := by exact_mod_cast (show m≤3*n by dsimp [m]; omega)
  have T : (10000:ℝ)≤2*(N:ℝ) := by exact_mod_cast (show 10000≤2*N by dsimp [N]; omega)
  have dl : (2*(N:ℝ))-1≤m := by
    dsimp [N,m]; push_cast
    have h : (δ:ℝ)≤1 := by exact_mod_cast hs
    linarith only [h]
  have du : (m:ℝ)≤2*(N:ℝ) := by exact_mod_cast (show m≤2*N by dsimp [N,m]; omega)
  have m₀ : 0≤(m:ℝ) := by positivity
  have m₁ : (100:ℝ)≤m := by linarith only [dl,T]
  have rt : (100:ℝ)≤sqrt (2*(N:ℝ)) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith only [T])
  have rs : (999/1000:ℝ)*sqrt (2*(N:ℝ))≤sqrt m := by
    apply (Real.le_sqrt (by positivity) m₀).mpr
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    linarith only [dl,T]
  have near := mul_le_mul (show (999/1000:ℝ)*(2*(N:ℝ))≤m by linarith only [dl,T]) rs
    (by positivity : 0≤(999/1000:ℝ)*sqrt (2*(N:ℝ))) m₀
  have lowerScale : (999/1000:ℝ)^2*cellScale N≤sizeScale m := by
    dsimp [cellScale,sizeScale]; linarith only [near]
  have upperScale : sizeScale m≤cellScale N := mul_le_mul du (Real.sqrt_le_sqrt du) (sqrt_nonneg _) (by positivity)
  have midS : 2*(N:ℝ)*100≤cellScale N := mul_le_mul_of_nonneg_left rt (by positivity)
  have midD : (n:ℝ)^2≤D := by dsimp [D,N]; push_cast; nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (Nat.cast_nonneg (α:=ℝ) δ)]
  have cap : sqrt m≤(n:ℝ)/4 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith only [mR,mul_nonneg (sub_nonneg.mpr nR) (Nat.cast_nonneg (α:=ℝ) n)]
  have growth := mul_le_mul mR cap (sqrt_nonneg _) (by positivity)
  have scale0 : 0≤sizeScale m := by unfold sizeScale; positivity
  have ⟨loLower,loUpper⟩ : 0.1366*sizeScale m-1≤(lo:ℝ) ∧ (lo:ℝ)≤0.1375*sizeScale m+1 := by
    by_cases earlier : n<300000
    · have start : lo=⌊0.1366*sizeScale m⌋₊ := by
        simp [lo,centralStart,show ¬n≤2048 by omega,earlier,sizeScale,mul_assoc]
      rw [start]
      have hi := Nat.floor_le (show 0≤0.1366*sizeScale m by positivity)
      have low := Nat.lt_floor_add_one (0.1366*sizeScale m)
      constructor <;> linarith only [hi,low,scale0]
    · have start : lo=⌈0.1375*sizeScale m⌉₊ := by
        simp [lo,centralStart,show ¬n≤2048 by omega,earlier,sizeScale,mul_assoc]
      rw [start]
      exact ⟨by linarith only [Nat.le_ceil (0.1375*sizeScale m),scale0],
        (Nat.ceil_lt_add_one (by positivity)).le⟩
  have sPos : 100≤sizeScale m := by
    have one : 1≤sqrt m := (Real.le_sqrt (by norm_num) m₀).mpr (by linarith only [m₁])
    simpa [sizeScale] using mul_le_mul m₁ one (by norm_num : (0:ℝ)≤1) m₀
  have capLo : lo≤D/2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    have R : (lo:ℝ)*2≤D := by
      dsimp [sizeScale] at loUpper
      nlinarith only [loUpper,growth,midD,nR,sq_nonneg ((n:ℝ)-1)]
    exact_mod_cast R
  have loHi : lo≤hi := le_min capLo (Nat.le_floor (by linarith only [loUpper,sPos]))
  have hiCap : hi≤D := (min_le_left ..).trans (Nat.div_le_self ..)
  have hiR : (hi:ℝ)≤(3/5)*sizeScale m :=
    (Nat.cast_le.mpr (min_le_right ..)).trans (Nat.floor_le (by unfold sizeScale; positivity))
  have hN : 0<n+δ := by omega
  have hshift : (H:ℝ)/2≤2*(N:ℝ) := by
    dsimp [H,N]; push_cast; linarith only [nR]
  have leftSite : 0.1359≤corankSite n δ lo := by
    change 0.1359≤((lo:ℝ)+(H:ℝ)/2)/cellScale N
    apply (le_div_iff₀ (cellScale_pos hN)).mpr
    have sh : (2:ℝ)≤H := by exact_mod_cast (show 2≤H by dsimp only [H]; omega)
    linarith only [lowerScale,loLower,(cellScale_pos hN).le,sh]
  have rightSite : corankSite n δ hi≤0.631 := by
    change ((hi:ℝ)+(H:ℝ)/2)/cellScale N≤0.631
    apply (div_le_iff₀ (cellScale_pos hN)).mpr
    linarith only [upperScale,hiR,hshift,midS,(cellScale_pos hN).le]
  apply unimodal_of_rank_integral_signs hs hN loHi hiCap (a:=0.339) (b:=0.398)
  · intro x hx; exact left x ⟨leftSite.trans hx.1,hx.2⟩
  · intro x hx; exact middle x ⟨(by norm_num : (0.333:ℝ)≤0.339).trans hx.1,
      hx.2.trans (by norm_num)⟩
  · intro x hx; exact right x ⟨hx.1,hx.2.trans rightSite⟩

end CentralUnimodality.Witness
