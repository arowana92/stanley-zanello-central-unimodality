module

public import CentralUnimodality.BinomialFourthMoment

/-! Fifth and sixth centered moments for the binomial mixture in the
last-return formula. These moments control the error after retaining
the quadratic correction in inverse sample size. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Finset

private theorem centered_succ (n r : ℕ) (x : ℝ) :
    centered (n+1) x r=∑ h ∈ range (r+1), (r.choose h:ℝ)*centered n x h*
      ((1-x)*(-x)^(r-h)+x*(1-x)^(r-h)) := by
  let z (k : ℕ) : ℝ := k-n*x
  let w (h : ℕ) : ℝ := (r.choose h:ℝ)*((1-x)*(-x)^(r-h)+x*(1-x)^(r-h))
  have step (k : ℕ) :
      (1-x)*((k:ℝ)-(n+1:ℕ)*x)^r+x*((k+1:ℕ)-(n+1:ℕ)*x)^r=
      ∑ h ∈ range (r+1), w h*(z k)^h := by
    rw [show (k:ℝ)-(n+1:ℕ)*x=z k+(-x) by dsimp [z]; push_cast; ring,
      show (k+1:ℕ)-(n+1:ℕ)*x=z k+(1-x) by dsimp [z]; push_cast; ring,
      add_pow,add_pow,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro h _
    dsimp only [w]; ring
  rw [centered,countMean_step]
  unfold countMean
  simp_rw [step,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro h _
  unfold centered countMean
  rw [Finset.mul_sum,Finset.sum_mul]
  apply sum_congr rfl
  intro k _
  dsimp only [z,w]; ring

theorem centered_zero_order (n : ℕ) (x : ℝ) : centered n x 0=1 := by
  simp only [centered,pow_zero,mul_one,countMean]
  calc
    _ = (x+(1-x))^n := by
      rw [add_pow]
      apply sum_congr rfl
      intro k _
      unfold splitBasis
      ring
    _ = 1 := by simp

theorem centered_high (n : ℕ) (x : ℝ) :
    let q := x*(1-x)
    centered n x 5=n*q*(1-2*x)*(1-12*q)+10*n^2*q^2*(1-2*x) ∧
    centered n x 6=n*q*(1-30*q+120*q^2)+n^2*q^2*(25-130*q)+15*n^3*q^3 := by
  dsimp only
  induction n with
  | zero => norm_num [centered,countMean,splitBasis]
  | succ n ih =>
    obtain ⟨a,b,c,d⟩ := centered_low n x
    rw [centered_succ n 5,centered_succ n 6]
    simp only [sum_range_succ,sum_range_zero,zero_add]
    norm_num [Nat.choose,centered_zero_order,a,b,c,d,ih.1,ih.2]
    constructor <;> ring

/-- Uniform bounds for the two highest moments needed by quintic Taylor expansion. -/
theorem centered_high_bounds {n : ℕ} (hn : 0<n) (x : unitInterval) :
    |centered n x 5|≤5/8*(n:ℝ)^2 ∧ centered n x 6≤1/2*(n:ℝ)^3 := by
  let N : ℝ := n
  let q := (x:ℝ)*(1-x)
  have hN : 1≤N := by dsimp only [N]; exact_mod_cast (show 1≤n by omega)
  have q0 : 0≤q := mul_nonneg x.2.1 (sub_nonneg.mpr x.2.2)
  have q4 : q≤1/4 := by dsimp [q]; nlinarith only [sq_nonneg ((x:ℝ)-1/2)]
  have c1 : |1-2*(x:ℝ)|≤1 := abs_le.mpr ⟨by linarith only [x.2.2],by linarith only [x.2.1]⟩
  obtain ⟨h5,h6⟩ := centered_high n (x:ℝ)
  change centered n x 5=N*q*(1-2*x)*(1-12*q)+10*N^2*q^2*(1-2*x) at h5
  change centered n x 6=N*q*(1-30*q+120*q^2)+N^2*q^2*(25-130*q)+15*N^3*q^3 at h6
  constructor
  · rw [h5,show N*q*(1-2*x)*(1-12*q)+10*N^2*q^2*(1-2*x)=
      (1-2*x)*(N*q)*(1-2*q+10*(N-1)*q) by ring,abs_mul,abs_mul]
    have nq : 0≤N*q := mul_nonneg (by linarith) q0
    have e0 : 0≤(N-1)*q := mul_nonneg (by linarith) q0
    have e1 := mul_le_mul_of_nonneg_left q4 (sub_nonneg.mpr hN)
    have last : |1-2*q+10*(N-1)*q|≤5/2*N := abs_le.mpr ⟨by linarith,by linarith⟩
    rw [abs_of_nonneg nq]
    calc
      _ ≤ (1*(N*(1/4)))*(5/2*N) := by gcongr
      _ = _ := by change _=5/8*N^2; ring
  · have pairs : 0≤N*(N-1) := mul_nonneg (by linarith) (by linarith)
    have triples : 0≤N*(N-1)*(N-2) := by
      by_cases h : n=1
      · subst n; norm_num [N]
      have h2 : 2≤N := by dsimp only [N]; exact_mod_cast (by omega : 2≤n)
      exact mul_nonneg pairs (by linarith)
    have one : q*(1-5*q+5*q^2)≤1/4 := by
      have qq := mul_nonneg (sq_nonneg q) (show 0≤1-q by linarith)
      nlinarith only [q4,qq]
    have two : q^2*(25-85*q)≤25/16 := by
      have qq := pow_le_pow_left₀ q0 q4 2
      nlinarith only [qq,pow_nonneg q0 3]
    have three : 15*q^3≤15/64 := by
      have qq := pow_le_pow_left₀ q0 q4 3
      linarith only [qq]
    have A := mul_le_mul_of_nonneg_left one (show 0≤N by linarith)
    have B := mul_le_mul_of_nonneg_left two pairs
    have C := mul_le_mul_of_nonneg_left three triples
    have quad : 0≤17*N^2-55*N+54 := by nlinarith only [sq_nonneg (34*N-55)]
    have rest := mul_nonneg (show 0≤N by linarith) quad
    rw [h6]
    change _ ≤ 1/2*N^3
    linarith only [A,B,C,rest]

end CentralUnimodality.ReturnSplit
