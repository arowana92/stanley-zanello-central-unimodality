module

public import CentralUnimodality.PointMassGaussian

/-! A uniform half-bound on endpoint times point probability. This
strengthens the point bounds used on both inner Fourier arcs. -/
@[expose] public section

namespace CentralUnimodality

private def smallPoint (a : ℕ) : Bool :=
  decide (2*a*Nat.fast_choose (a^2) (a.choose 2) ≤ 2^(a^2))

set_option maxRecDepth 20000 in
private theorem smallPoints : (List.range 64).all smallPoint = true := by decide +kernel

theorem point_half (a d : ℕ) : (a:ℝ)*pointMass a d ≤ 1/2 := by
  apply (mul_le_mul_of_nonneg_left (pointMass_le_square a d) (Nat.cast_nonneg (α := ℝ) a)).trans
  by_cases ha : 64 ≤ a
  · exact point_half_large ha
  · have h := of_decide_eq_true (List.all_eq_true.mp smallPoints a (List.mem_range.mpr (by omega)))
    change 2*a*Nat.fast_choose (a^2) (a.choose 2) ≤ 2^(a^2) at h
    rw [← Nat.choose_eq_fast_choose] at h
    have hr : 2*(a:ℝ)*((a^2).choose (a.choose 2)) ≤ (2:ℝ)^(a^2) := by exact_mod_cast h
    rw [pointMass,peak_time,← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hr]

theorem first_hit_half {a j : ℕ} (ha : 0 < a) (hj : 0 < j) :
    ((hitWords a j).card:ℝ)/(2:ℝ)^j ≤ 1/(2*(j:ℝ)) := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  by_cases hp : ∃ d, m = a+2*d
  · obtain ⟨d,hd⟩ := hp
    rw [fair_first_hit a m d hd]
    have h := point_half (a+1) d
    rw [pointMass,show (a+1)+2*d = m+1 by omega] at h
    push_cast at h ⊢
    calc
      _ = (((a:ℝ)+1)*((m+1).choose d / (2:ℝ)^(m+1)))/(m+1) := by field_simp
      _ ≤ (1/2)/((m:ℝ)+1) := div_le_div_of_nonneg_right h (by positivity)
      _ = _ := by field_simp
  · rw [first_hit_incompatible a m hp]
    simp
    positivity

end CentralUnimodality
