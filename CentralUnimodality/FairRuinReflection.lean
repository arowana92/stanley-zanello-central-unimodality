module

public import CentralUnimodality.OuterPrefixSurvival
public import CentralUnimodality.HitTiltCost

/-! Finite reflection at the absorbing height bounds an inhomogeneous
suffix crossing by two endpoint tails of a fair walk. The exact formula
includes all parities and the starting point on the boundary. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

noncomputable def fairHeightTail : ℕ → ℤ → ℝ
  | 0,z => if z≤0 then 1 else 0
  | n+1,z => (fairHeightTail n (z-1)+fairHeightTail n (z+1))/2

theorem fair_height_anti (n : ℕ) : Antitone (fairHeightTail n) := by
  induction n with
  | zero => intro x y h; dsimp only [fairHeightTail]; split_ifs <;> first | omega | norm_num
  | succ n ih =>
    intro x y h; dsimp only [fairHeightTail]
    exact div_le_div_of_nonneg_right (add_le_add (ih (by omega)) (ih (by omega))) (by norm_num)

theorem fair_height_symmetry (n : ℕ) (z : ℤ) :
    fairHeightTail n z+fairHeightTail n (1-z)=1 := by
  induction n generalizing z with
  | zero => dsimp only [fairHeightTail]; split_ifs <;> first | omega | norm_num
  | succ n ih =>
    dsimp only [fairHeightTail]
    have H := ih (z-1)
    have K := ih (z+1)
    rw [show 1-(z-1)=1-z+1 by ring] at H
    rw [show 1-(z+1)=1-z-1 by ring] at K
    linarith only [H,K]

/-- Reflection formula for a fair walk started a steps above absorption. -/
theorem fair_ruin_identity (n a : ℕ) :
    1-live 0 0 n a = fairHeightTail n a+fairHeightTail n ((a:ℤ)+1) := by
  induction n generalizing a with
  | zero =>
    cases a with
    | zero => norm_num [fairHeightTail]
    | succ a =>
      have hp : ¬((a+1:ℕ):ℤ)≤0 := by omega
      have hq : ¬((a+1:ℕ):ℤ)+1≤0 := by omega
      simp only [live_initial,sub_self,fairHeightTail,ite_eq_right hp,ite_eq_right hq,zero_add]
  | succ n ih =>
    cases a with
    | zero => simpa only [live_dead,sub_zero,Nat.cast_zero,zero_add,sub_zero] using
        (fair_height_symmetry (n+1) 0).symm
    | succ a =>
      rw [live_step]
      simp only [sub_zero,neg_zero,upChance,exp_zero,cosh_zero,mul_one]
      have H := ih (a+2)
      have K := ih a
      simp only [fairHeightTail,Nat.cast_succ,add_sub_cancel_right]
      push_cast at H K
      simp only [show (a:ℤ)+1+1=(a:ℤ)+2 by ring]
      linarith only [H,K]

theorem fair_height_words (n : ℕ) (z : ℤ) :
    fairHeightTail n z=∑ w ∈ words n, if z≤displacement w then signMass 0 0 w else 0 := by
  induction n generalizing z with
  | zero => simp [fairHeightTail,words,signMass,displacement]
  | succ n ih =>
    rw [fairHeightTail,ih,ih,sum_cons_words]
    simp only [div_eq_mul_inv,add_mul,Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro w _
    · have he : displacement (false::w)=1+displacement w := by simp [displacement,step]
      simp only [he,signMass,zero_mul,exp_zero,cosh_zero,mul_one,sub_zero]
      split_ifs <;> first | omega | ring
    · have he : displacement (true::w)= -1+displacement w := by simp [displacement,step]
      simp only [he,signMass,zero_mul,exp_zero,cosh_zero,mul_one,sub_zero]
      split_ifs <;> first | omega | ring

theorem ruin_le_fair_tails {c : ℝ} (hc : 0≤c) (n h : ℕ) :
    ruin c n h ≤ 2*fairHeightTail n ((h:ℤ)+1) := by
  have H : ruin c n h+live c (c*n) n (h+1)=1 := by
    rw [ruin,live,← Finset.sum_add_distrib,← signMass_total c (c*n) n]
    apply Finset.sum_congr rfl
    intro w _; split_ifs <;> simp
  have K := live_parameters 0 0 c (c*n) n (h+1) (by
    intro i hi
    have h : (i:ℝ)≤n := by exact_mod_cast hi.le
    linarith only [mul_le_mul_of_nonneg_left h hc])
  have hsub := fair_ruin_identity n (h+1)
  rw [Nat.cast_add,Nat.cast_one] at hsub
  have hdec := fair_height_anti n (show (h:ℤ)+1≤h+1+1 by omega)
  linarith only [H,K,hsub,hdec]

end CentralUnimodality.MarkedExcursion
