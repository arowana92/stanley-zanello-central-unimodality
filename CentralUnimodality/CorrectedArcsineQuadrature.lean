module

public import CentralUnimodality.BinomialFourthMoment

/-! A first corrected quadrature for the exact last-return weights.
The remaining error has order 1/N² on the entire unit interval. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Set

def CubicRemainder (g d e h : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ x∈Icc (0:ℝ) 1, ∀ y∈Icc (0:ℝ) 1,
    |g y-(g x+d x*(y-x)+(e x/2)*(y-x)^2+(h x/6)*(y-x)^3)|≤K/24*(y-x)^4

private theorem sample_add (n : ℕ) (x : ℝ) (f g : ℝ → ℝ) :
    binomialSample n (fun y => f y+g y) x=binomialSample n f x+binomialSample n g x := by
  simp [binomialSample,add_mul,Finset.sum_add_distrib]

private theorem sample_sub (n : ℕ) (x : ℝ) (f g : ℝ → ℝ) :
    binomialSample n (fun y => f y-g y) x=binomialSample n f x-binomialSample n g x := by
  simp [binomialSample,sub_mul,Finset.sum_sub_distrib]

private theorem sample_scale (n : ℕ) (x c : ℝ) (f : ℝ → ℝ) :
    binomialSample n (fun y => c*f y) x=c*binomialSample n f x := by
  simp [binomialSample,Finset.mul_sum,mul_assoc]

private theorem sample_const (n : ℕ) (x : unitInterval) (c : ℝ) :
    binomialSample n (fun _ => c) x=c := by
  have h : ∑ k : Fin (n+1), splitBasis n k x=1 := by
    simpa only [bernstein_apply,splitBasis] using bernstein.probability n x
  simp only [binomialSample,← Finset.mul_sum,h,mul_one]

theorem binomialSample_corrected {n : ℕ} (hn : 0<n) {g d e h : ℝ → ℝ} {M K : ℝ}
    (hK : 0≤K) (hh : ∀ x∈Icc (0:ℝ) 1, |h x|≤M) (rem : CubicRemainder g d e h K)
    (x : unitInterval) :
    |binomialSample n g x-g x-(x*(1-(x:ℝ)))*e x/(2*n)|≤(M/24+K/128)/n^2 := by
  let q := (x:ℝ)*(1-x)
  let N := (n:ℝ)
  have pos : 0<N := Nat.cast_pos.mpr hn
  have one : 1≤N := by dsimp only [N]; exact_mod_cast (show 1≤n by omega)
  have q0 : 0≤q := mul_nonneg x.2.1 (sub_nonneg.mpr x.2.2)
  have q4 : q≤1/4 := by dsimp [q]; nlinarith only [sq_nonneg ((x:ℝ)-1/2)]
  obtain ⟨a,b,c,f⟩ := centered_low n (x:ℝ)
  let Z := fun (r : ℕ) (y : ℝ) => (y-x)^r
  have z1 : binomialSample n (Z 1) x=0 := by dsimp only [Z]; rw [scaled_centered hn,a,zero_div]
  have z2 : binomialSample n (Z 2) x=q/N := by
    dsimp only [Z]; rw [scaled_centered hn,b]; dsimp [N,q]; field_simp
  have z3 : binomialSample n (Z 3) x=q*(1-2*x)/N^2 := by
    dsimp only [Z]; rw [scaled_centered hn,c]; dsimp [N,q]; field_simp
  have z4 : binomialSample n (Z 4) x≤(3/16)/N^2 := by
    dsimp only [Z]; rw [scaled_centered hn,f]
    change (3*N^2*q^2+N*q*(1-6*q))/N^4≤(3/16)/N^2
    have q2 := pow_le_pow_left₀ q0 q4 2
    have qb : q*(1-3*q)≤3/16 := by nlinarith only [sq_nonneg (q-1/6)]
    have H := mul_le_mul_of_nonneg_left (show 3*q^2≤3/16 by linarith only [q2]) (sub_nonneg.mpr one)
    have V : 3*N*q^2+q*(1-6*q)≤(3/16)*N := by linarith only [H,qb]
    rw [show (3*N^2*q^2+N*q*(1-6*q))/N^4=(3*N*q^2+q*(1-6*q))/N^3 by field_simp,div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right V (sq_nonneg N)]
  let T := fun y => g x+d x*Z 1 y+(e x/2)*Z 2 y+(h x/6)*Z 3 y
  have poly : binomialSample n T x=g x+(e x/2)*(q/N)+(h x/6)*(q*(1-2*x)/N^2) := by
    simp only [T,sample_add,sample_scale,sample_const,z1,z2,z3,mul_zero,add_zero]
  have H : |binomialSample n (fun y => g y-T y) x|≤(K/24)*binomialSample n (Z 4) x := by
    unfold binomialSample
    rw [Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum _)
    intro k _
    have mem := (bernstein.z k).2
    have rr := rem _ x.2 _ mem
    have w : 0≤splitBasis n k x := by
      simpa only [bernstein_apply,splitBasis] using (bernstein_nonneg : 0≤bernstein n k x)
    rw [abs_mul,abs_of_nonneg w,← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ w
    simpa only [T,Z,bernstein.z,pow_one] using rr
  rw [sample_sub,poly] at H
  have mag : |(1:ℝ)-2*x|≤1 := abs_le.mpr ⟨by linarith only [x.2.2],by linarith only [x.2.1]⟩
  have small := mul_le_mul (hh _ x.2) ((mul_le_mul q4 mag (abs_nonneg _) (by norm_num)).trans_eq (mul_one _))
    (mul_nonneg q0 (abs_nonneg _)) ((abs_nonneg _).trans (hh _ x.2))
  have tri := abs_add_le (binomialSample n g x-(g x+e x/2*(q/N)+h x/6*(q*(1-2*x)/N^2)))
    (h x/6*(q*(1-2*x)/N^2))
  change |binomialSample n g x-g x-q*e x/(2*N)|≤_
  rw [show binomialSample n g x-g x-q*e x/(2*N)=
    (binomialSample n g x-(g x+e x/2*(q/N)+h x/6*(q*(1-2*x)/N^2)))+h x/6*(q*(1-2*x)/N^2) by ring]
  apply tri.trans
  apply (add_le_add (H.trans (mul_le_mul_of_nonneg_left z4 (by positivity))) le_rfl).trans
  rw [abs_mul,abs_div,abs_div,abs_mul,abs_of_nonneg q0,abs_of_pos (by norm_num : (0:ℝ)<6),abs_of_pos (sq_pos_of_pos pos)]
  change K/24*(3/16/N^2)+|h x|/6*(q*|1-2*(x:ℝ)|/N^2)≤(M/24+K/128)/N^2
  field_simp [pos.ne']
  linarith only [small]

theorem sample_corrected_arc {n : ℕ} (hn : 0<n) {g d e h : ℝ → ℝ} {M K : ℝ}
    (hg : Continuous g) (he : Continuous e) (hK : 0≤K) (hh : ∀ x∈Icc (0:ℝ) 1, |h x|≤M)
    (rem : CubicRemainder g d e h K) :
    |sample n g-arc g-(1/(2*n))*arc (fun x => x*(1-x)*e x)|≤(M/24+K/128)/n^2 := by
  rw [← arc_binomialSample,← arc_sub (continuous_binomialSample ..) hg,← arc_const_mul,
    ← arc_sub (f:=fun x => binomialSample n g x-g x) ((continuous_binomialSample n g).sub hg) (by fun_prop)]
  apply arc_bound
  intro x hx
  have H := binomialSample_corrected hn hK hh rem ⟨x,hx⟩
  dsimp only at H ⊢
  rw [show 1/(2*(n:ℝ))*(x*(1-x)*e x)=x*(1-x)*e x/(2*n) by ring]
  exact H

end CentralUnimodality.ReturnSplit
