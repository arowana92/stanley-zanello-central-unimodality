module

public import CentralUnimodality.ReturnSplitWeights
import Mathlib.Tactic.Positivity

/-! Uniform estimates for replacing the last-return split distribution by
a finite anchor. Conditional deletion preserves the mean success fraction
and has variance at most 1/(4N²). -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

theorem average_congr {N : ℕ} {f g : ℕ → ℝ} (h : ∀ k≤N, f k=g k) :
    average N f = average N g := by
  apply Finset.sum_congr rfl
  intro k hk; rw [h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]

theorem average_mul (N : ℕ) (a : ℝ) (f : ℕ → ℝ) :
    average N (fun k => a*f k) = a*average N f := by
  simp only [average,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _; ring

theorem average_sub (N : ℕ) (f g : ℕ → ℝ) :
    average N (fun k => f k-g k)=average N f-average N g := by
  simp [average,mul_sub,Finset.sum_sub_distrib]

theorem average_abs_le {N : ℕ} {f : ℕ → ℝ} {C : ℝ} (h : ∀ k≤N, |f k|≤C) :
    |average N f|≤C := by
  rw [← average_const N C]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [abs_mul,abs_of_pos (weight_pos _ _)]
  exact mul_le_mul_of_nonneg_left (h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) (weight_pos ..).le

noncomputable def sample (N : ℕ) (g : ℝ → ℝ) : ℝ := average N (fun k => g ((k:ℝ)/N))

private theorem delete_average (N : ℕ) (f : ℕ → ℝ) :
    average N f=average (N+1) (fun k =>
      (1-(k:ℝ)/(N+1))*f k+((k:ℝ)/(N+1))*f (k-1)) := by
  have pos : (N:ℝ)+1≠0 := by positivity
  apply mul_left_cancel₀ pos
  rw [deletion,← average_mul]
  apply average_congr
  intro k _
  field_simp

/-- The quadratic Taylor remainder bound can be supplied directly for a
piecewise polynomial trial function. -/
def QuadraticRemainder (g slope : ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    |g y-g x-(y-x)*slope x| ≤ M/2*(y-x)^2

private theorem two_point_error {g slope : ℝ → ℝ} {M x y z v : ℝ}
    (h : QuadraticRemainder g slope M) (hM : 0≤M)
    (hx : x∈Set.Icc (0:ℝ) 1) (hy : y∈Set.Icc (0:ℝ) 1) (hz : z∈Set.Icc (0:ℝ) 1)
    (hm : (1-x)*(y-x)+x*(z-x)=0) (hv : (1-x)*(y-x)^2+x*(z-x)^2≤v) :
    |(1-x)*g y+x*g z-g x|≤M/2*v := by
  let err := fun t => g t-g x-(t-x)*slope x
  have id : (1-x)*g y+x*g z-g x=(1-x)*err y+x*err z := by
    dsimp only [err]; linear_combination slope x*hm
  rw [id]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hx.2),abs_of_nonneg hx.1]
  have A := mul_le_mul_of_nonneg_left (h x hx y hy) (sub_nonneg.mpr hx.2)
  have B := mul_le_mul_of_nonneg_left (h x hx z hz) hx.1
  have H := mul_le_mul_of_nonneg_left hv (by positivity : 0≤M/2)
  change (1-x)*|g y-g x-(y-x)*slope x|+x*|g z-g x-(z-x)*slope x|≤_
  linarith only [A,B,H]

theorem sample_step {g slope : ℝ → ℝ} {M : ℝ} (hM : 0≤M) (h : QuadraticRemainder g slope M)
    {N : ℕ} (hN : 0<N) : |sample N g-sample (N+1) g|≤M/(8*(N:ℝ)^2) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hn' : (0:ℝ)<(N:ℝ)+1 := by positivity
  rw [sample,sample,delete_average,← average_sub]
  apply average_abs_le
  intro k hk
  push_cast
  by_cases zero : k=0
  · subst k; simp; positivity
  by_cases last : k=N+1
  · subst k; simp [hn.ne',hn'.ne']; positivity
  have hkn : k≤N := by omega
  have hk₀ : 0≤(k:ℝ) := by positivity
  have hk' : (k:ℝ)≤N := by exact_mod_cast hkn
  have hk₁ : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  rw [Nat.cast_sub (by omega : 1≤k),Nat.cast_one]
  let x := (k:ℝ)/(N+1)
  let y := (k:ℝ)/N
  let z := ((k:ℝ)-1)/N
  have hx : x∈Set.Icc (0:ℝ) 1 := ⟨by dsimp [x]; positivity,(div_le_one hn').mpr (by linarith)⟩
  have hy : y∈Set.Icc (0:ℝ) 1 := ⟨by dsimp [y]; positivity,(div_le_one hn).mpr hk'⟩
  have hz : z∈Set.Icc (0:ℝ) 1 := ⟨div_nonneg (by linarith) hn.le,(div_le_one hn).mpr (by linarith)⟩
  have dy : y-x=x/N := by dsimp [x,y]; field_simp; ring
  have dz : z-x=-(1-x)/N := by dsimp [x,z]; field_simp; ring
  have hm : (1-x)*(y-x)+x*(z-x)=0 := by rw [dy,dz]; ring
  have hv : (1-x)*(y-x)^2+x*(z-x)^2≤1/(4*(N:ℝ)^2) := by
    rw [dy,dz]
    field_simp
    nlinarith only [sq_nonneg (2*x-1)]
  exact (two_point_error h hM hx hy hz hm hv).trans_eq (by ring)

/-- Compare every larger half-length to one finite quadrature rule. -/
theorem sample_anchor {g slope : ℝ → ℝ} {C : ℝ} (hC : 0≤C) (h : QuadraticRemainder g slope C)
    {A N : ℕ} (hA : 2≤A) (hN : A≤N) :
    |sample A g-sample N g|≤(C/8)*(1/((A:ℝ)-1)-1/((N:ℝ)-1)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hk' : (2:ℝ)≤k := by exact_mod_cast (hA.trans hk)
    have pos : 0<(k:ℝ) := by linarith
    have pos' : 0<(k:ℝ)-1 := by linarith
    have step := sample_step hC h (by omega : 0<k)
    have inv : 1/(k:ℝ)^2 ≤ 1/((k:ℝ)-1)-1/k := by
      field_simp
      nlinarith only [hk']
    have incr := mul_le_mul_of_nonneg_left inv (by positivity : 0≤C/8)
    have tri := abs_add_le (sample A g-sample k g) (sample k g-sample (k+1) g)
    rw [sub_add_sub_cancel] at tri
    apply tri.trans
    rw [Nat.cast_succ,add_sub_cancel_right]
    rw [show C/(8*(k:ℝ)^2)=(C/8)*(1/(k:ℝ)^2) by ring] at step
    linarith only [ih,step,incr]

end CentralUnimodality.ReturnSplit
