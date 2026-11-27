module

public import CentralUnimodality.StaircasePrefix
public import Mathlib.Data.Finset.NatAntidiagonal

/-! A monomial surviving antisymmetrization has distinct exponent pairs.
This module proves the numerical lower bound for every finite set of such
pairs, independently of the identification of the Dyck character. -/
@[expose] public section

namespace CentralUnimodality

private def degreeTriangle : ℕ → Finset (ℕ × ℕ)
  | 0 => ∅
  | t+1 => degreeTriangle t ∪ Finset.antidiagonal t

private theorem mem_degreeTriangle (p : ℕ × ℕ) (t : ℕ) :
    p ∈ degreeTriangle t ↔ p.1+p.2 < t := by
  induction t with
  | zero => simp [degreeTriangle]
  | succ t ih =>
    rw [degreeTriangle,Finset.mem_union,ih,Finset.mem_antidiagonal]
    omega

private theorem card_degreeTriangle (t : ℕ) : 2*(degreeTriangle t).card = t*(t+1) := by
  induction t with
  | zero => simp [degreeTriangle]
  | succ t ih =>
    have hd : Disjoint (degreeTriangle t) (Finset.antidiagonal t) := by
      apply Finset.disjoint_left.mpr
      intro p hp hq
      have h := (mem_degreeTriangle p t).mp hp
      have h' := Finset.mem_antidiagonal.mp hq
      omega
    rw [degreeTriangle,Finset.card_union_of_disjoint hd,Finset.Nat.card_antidiagonal]
    nlinarith only [ih]

private theorem deficit_bound (S : Finset (ℕ × ℕ)) (t : ℕ) :
    6*(∑ p ∈ S, (t-(p.1+p.2))) ≤ t*(t+1)*(t+2) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he (p : ℕ × ℕ) : t+1-(p.1+p.2) = (t-(p.1+p.2)) + if p.1+p.2 ≤ t then 1 else 0 := by
      split <;> omega
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_boole]
    have ht : (S.filter fun p => p.1+p.2 ≤ t) ⊆ degreeTriangle (t+1) := by
      intro p hp
      exact (mem_degreeTriangle p _).mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
    have hcard := Finset.card_le_card ht
    nlinarith only [ih,hcard,card_degreeTriangle (t+1)]

private theorem triangular_bracket (n : ℕ) :
    ∃ t : ℕ, t*(t+1) ≤ 2*n ∧ 2*n ≤ (t+1)*(t+2) := by
  induction n with
  | zero => exact ⟨0,by decide,by decide⟩
  | succ n ih =>
    obtain ⟨t,ha,hb⟩ := ih
    by_cases h : 2*(n+1) ≤ (t+1)*(t+2)
    · exact ⟨t,by omega,h⟩
    · exact ⟨t+1,by nlinarith only [lt_of_not_ge h],by nlinarith only [hb]⟩

/-- The total degree of an alternant on n distinct planar monomials
is at least (2 sqrt(2)/3) n sqrt(n) - n. -/
theorem degree_sum_lower (S : Finset (ℕ × ℕ)) :
    dyckLower S.card ≤ (∑ p ∈ S, (p.1+p.2):ℕ) := by
  let n := S.card
  obtain ⟨t,ha,hb⟩ := triangular_bracket n
  have hpack : n*(t+1) ≤ (∑ p ∈ S, (p.1+p.2)) + n + ∑ p ∈ S, (t-(p.1+p.2)) := by
    have hp (p : ℕ × ℕ) : t+1 ≤ p.1+p.2+1+(t-(p.1+p.2)) := by omega
    simpa [Finset.sum_add_distrib,n] using Finset.sum_le_sum (s := S) (fun p _ => hp p)
  have hd := deficit_bound S t
  let A : ℝ := (∑ p ∈ S, (p.1+p.2):ℕ)
  let N : ℝ := n
  let T : ℝ := (t:ℝ)+1
  let u := Real.sqrt (2*N)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = 2*N := Real.sq_sqrt (by positivity)
  have h1 : T*(T-1) ≤ u^2 := by
    rw [hu2]
    dsimp [T,N]
    convert (show (t:ℝ)*(t+1) ≤ 2*n by exact_mod_cast ha) using 1
    ring
  have h2 : u^2 ≤ T*(T+1) := by
    rw [hu2]
    dsimp [T,N]
    convert (show 2*(n:ℝ) ≤ (t+1)*(t+2) by exact_mod_cast hb) using 1
    ring
  have hsq : ((u-T)*(u+T))^2 ≤ T^2 := by
    have h₁ : -T ≤ (u-T)*(u+T) := by linarith only [h1]
    have h₂ : (u-T)*(u+T) ≤ T := by linarith only [h2]
    nlinarith only [mul_nonneg (sub_nonneg.mpr h₂) (by linarith only [h₁] : 0 ≤ (u-T)*(u+T)+T)]
  have he : (u-T)^2*(2*u+T) ≤ T := by
    apply (mul_le_mul_iff_right₀ hT).mp
    nlinarith only [hsq,mul_nonneg (sq_nonneg (u-T)) (sq_nonneg u)]
  have hh : 6*n*(t+1) ≤ 6*(∑ p ∈ S, (p.1+p.2)) + 6*n + t*(t+1)*(t+2) := by
    nlinarith only [hpack,hd]
  have hh' : 6*N*T ≤ 6*A+6*N+(T-1)*T*(T+1) := by
    dsimp [N,T,A]
    push_cast
    convert (show 6*(n:ℝ)*(t+1) ≤ 6*((∑ p ∈ S, (p.1+p.2):ℕ):ℝ)+6*n+t*(t+1)*(t+2)
      by exact_mod_cast hh) using 1
    push_cast
    ring
  have hroot : u = Real.sqrt 2 * Real.sqrt N := Real.sqrt_mul (by norm_num) _
  change (2*Real.sqrt 2/3)*N*Real.sqrt N-N ≤ A
  calc
    _ = 2*N*u/3-N := by rw [hroot]; ring
    _ ≤ _ := by nlinarith only [he,hh',hu2,congrArg (·*T) hu2,congrArg (·*u) hu2]

end CentralUnimodality
