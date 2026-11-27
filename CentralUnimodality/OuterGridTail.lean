module

public import CentralUnimodality.OuterGridScale

/-! Outer-grid reserves for the first and second differences. These are
rational upper bounds for every half-length at least 2049. -/
@[expose] public section

namespace CentralUnimodality

def outerCap (lo hi c : ℚ) (L r : ℕ) : ℚ :=
  (32/3.14)*(((hi-lo)*262337+1.257)*(hi*262337)^r)*
    (upperNegExp ((c*(63/64)*4097-c*L)/16))^16

private theorem exp_sixteenths {x : ℚ} (hx : 0 ≤ x) :
    Real.exp (-(x:ℝ)) ≤ (upperNegExp (x/16):ℝ)^16 := by
  apply le_trans _ (pow_le_pow_left₀ (Real.exp_pos _).le (upperNegExp_sound (div_nonneg hx (by norm_num))) 16)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  push_cast
  linarith

theorem outer_grid_cap {N m L r : ℕ} (hN : 2049 ≤ N) (hm : 2*N ≤ m+1) (hr : r ≤ 2)
    {lo hi c : ℚ} (hlo : 0 ≤ lo) (hw : lo ≤ hi) (hc : 0 ≤ c)
    (hdecay : 6 ≤ 2*c*(63/64)*2049) (hexp : 0 ≤ c*(63/64)*4097-c*L)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hstep : Δ ≤ 1.257) (I : Finset ℕ)
    (hpts : ∀ j ∈ I, lo*Witness.cellScale N ≤ Δ*j ∧ Δ*j ≤ hi*Witness.cellScale N)
    (f : ℕ → ℝ) (hf : ∀ j ∈ I, f j ≤ 16*Real.exp (c*L-c*(63/64:ℝ)*m)) :
    (2/Real.pi)*(∑ j ∈ I, Δ*((Δ*j)^r*f j)) ≤ (outerCap lo hi c L r:ℝ) := by
  have hc' : (0:ℝ) ≤ c := by exact_mod_cast hc
  have hi' : (0:ℝ) ≤ hi := by exact_mod_cast hlo.trans hw
  have hdiff : 0 ≤ (hi:ℝ)-lo := sub_nonneg.mpr (by exact_mod_cast hw)
  have hs : 0 ≤ Witness.cellScale N := by unfold Witness.cellScale; positivity
  have h := grid_arc_sum I hΔ hs (by exact_mod_cast hlo) (by exact_mod_cast hw) r hpts f (by positivity) hf
  have hsc := outer_grid_scale (lo := (lo:ℝ)) (hi := (hi:ℝ)) (c := (c:ℝ)) (L := L) hN hm hc'
    (by simpa using (Rat.cast_le (K := ℝ)).mpr hdecay) hr (by exact_mod_cast hlo) (by exact_mod_cast hw) hstep
  have hn := exp_sixteenths hexp
  push_cast at hn
  have he : Real.exp (c*L-c*(63/64:ℝ)*4097) ≤ (upperNegExp ((c*(63/64)*4097-c*L)/16):ℝ)^16 := by
    convert hn using 2
    ring
  have hπ : (32:ℝ)/Real.pi ≤ 32/3.14 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_d2.le
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (2:ℝ)/Real.pi)).trans
  calc
    _ = (32/Real.pi)*(( ((hi:ℝ)-lo)*Witness.cellScale N+Δ)*(hi*Witness.cellScale N)^r*
        Real.exp (c*L-c*(63/64:ℝ)*m)) := by ring
    _ ≤ (32/3.14:ℝ)*((((hi:ℝ)-lo)*262337+1.257)*(hi*262337)^r*
        Real.exp (c*L-c*(63/64:ℝ)*4097)) := mul_le_mul hπ hsc (by positivity) (by norm_num)
    _ ≤ _ := by
      unfold outerCap
      push_cast
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left he (by positivity)

theorem outer_cap_values :
    outerCap 0.008 0.032 0.0078 216 1 ≤ 0.000064 ∧
    outerCap 0.032 3.142 0.0155 112 1 ≤ 0.000000001 ∧
    outerCap 0.008 0.032 0.0078 216 2 ≤ 0.535 ∧
    outerCap 0.032 3.142 0.0155 112 2 ≤ 0.0000001 := by decide +kernel

end CentralUnimodality
