module

public import CentralUnimodality.BinomialSixthMoment
public import CentralUnimodality.SmoothSplitQuadrature
public import CentralUnimodality.SplitDerivativeBounds

/-! The second correction to the arcsine split is obtained by sampling
the quintic Taylor polynomial against the exact binomial law. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Finset Set

private theorem quintic_remainder {g : ℝ → ℝ} (hg : ContDiff ℝ 6 g) {K : ℝ}
    (hK : ∀ t∈Icc (0:ℝ) 1, |iteratedDeriv 6 g t|≤K)
    {x y : ℝ} (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) :
    |g y-∑ h ∈ range 6, iteratedDeriv h g x/(h.factorial:ℝ)*(y-x)^h|≤K/720*(y-x)^6 := by
  by_cases eq : x=y
  · subst y; simp [sum_range_succ]
  let s := uIcc x y
  obtain ⟨t,ht,h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=5) eq (hg.contDiffOn (s:=s))
  have poly : taylorWithinEval g 5 s x y=
      ∑ k ∈ range 6, iteratedDeriv k g x/(k.factorial:ℝ)*(y-x)^k := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro k hk
    have ord : k≤6 := by have := mem_range.mp hk; omega
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc eq)
      ((hg.of_le (by exact_mod_cast ord)).contDiffAt) left_mem_uIcc]
    simp only [smul_eq_mul]
    ring
  change g y-taylorWithinEval g 5 s x y=_ at h
  rw [← poly,h,abs_div,abs_mul,abs_pow]
  have b := hK t (uIcc_subset_Icc hx hy (Ioo_subset_Icc_self ht))
  have nn : 0≤(y-x)^6 := by positivity
  norm_num [Nat.factorial,show |y-x|^6=(y-x)^6 by rw [← abs_pow,abs_of_nonneg nn]]
  linarith only [mul_le_mul_of_nonneg_right b nn]

private theorem sample_quintic {n : ℕ} (hn : 0<n) {g : ℝ → ℝ} (hg : ContDiff ℝ 6 g) {K : ℝ}
    (hK : ∀ t∈Icc (0:ℝ) 1, |iteratedDeriv 6 g t|≤K) (x : unitInterval) :
    |binomialSample n g x-∑ h ∈ range 6,
      iteratedDeriv h g x/(h.factorial:ℝ)*(centered n x h/(n:ℝ)^h)|≤
      K/720*(centered n x 6/(n:ℝ)^6) := by
  let d (h : ℕ) := iteratedDeriv h g x/(h.factorial:ℝ)
  let P (y : ℝ) := ∑ h ∈ range 6, d h*(y-x)^h
  have poly : binomialSample n P x=∑ h ∈ range 6, d h*(centered n x h/(n:ℝ)^h) := by
    simp_rw [← scaled_centered hn]
    simp only [binomialSample,P,Finset.sum_mul,Finset.mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro h _
    apply sum_congr rfl
    intro k _
    ring
  change |binomialSample n g x-∑ h ∈ range 6, d h*(centered n x h/(n:ℝ)^h)|≤_
  rw [← poly,← scaled_centered hn]
  simp only [binomialSample,← sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum _)
  intro k _
  have mem := (bernstein.z k).2
  have rem := quintic_remainder hg hK x.2 mem
  have w : 0≤splitBasis n k x := by
    simpa only [bernstein_apply,splitBasis] using (bernstein_nonneg : 0≤bernstein n k x)
  rw [← sub_mul,abs_mul,abs_of_nonneg w,← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ w
  simpa only [P,d,bernstein.z] using rem

/-- The first two finite-size corrections retain their signs. The error is
uniform over the unit interval at every positive sample size. -/
theorem binomial_second_correction {n : ℕ} (hn : 0<n) {g : ℝ → ℝ} (hg : ContDiff ℝ 6 g)
    {K₄ K₅ K₆ : ℝ} (h₄ : ∀ t∈Icc (0:ℝ) 1, |iteratedDeriv 4 g t|≤K₄)
    (h₅ : ∀ t∈Icc (0:ℝ) 1, |iteratedDeriv 5 g t|≤K₅)
    (h₆ : ∀ t∈Icc (0:ℝ) 1, |iteratedDeriv 6 g t|≤K₆) (x : unitInterval) :
    let q := (x:ℝ)*(1-x)
    |binomialSample n g x-g x-q*iteratedDeriv 2 g x/(2*n)-
      (q*(1-2*x)*iteratedDeriv 3 g x/6+q^2*iteratedDeriv 4 g x/8)/(n:ℝ)^2|≤
      (K₄/96+K₅/192+K₆/1440)/(n:ℝ)^3 := by
  let N : ℝ := n
  let q := (x:ℝ)*(1-x)
  let d (r : ℕ) := iteratedDeriv r g x
  let A := g x+q*d 2/(2*N)+(q*(1-2*x)*d 3/6+q^2*d 4/8)/N^2
  let U := (d 4/24)*(q*(1-6*q))/N^3
  let V := d 5/120*(centered n x 5/N^5)
  have pos : 0<N := Nat.cast_pos.mpr hn
  have q0 : 0≤q := mul_nonneg x.2.1 (sub_nonneg.mpr x.2.2)
  have q4 : q≤1/4 := by dsimp [q]; nlinarith only [sq_nonneg ((x:ℝ)-1/2)]
  obtain ⟨z1,z2,z3,z4⟩ := centered_low n (x:ℝ)
  obtain ⟨z5,z6⟩ := centered_high_bounds hn x
  have poly : (∑ r ∈ range 6, d r/(r.factorial:ℝ)*(centered n x r/N^r))=A+U+V := by
    simp only [sum_range_succ,sum_range_zero,zero_add,centered_zero_order,z1,z2,z3,z4]
    dsimp only [d,A,U,V,q,N]
    norm_num [Nat.factorial,iteratedDeriv_zero]
    field_simp [show (n:ℝ)≠0 by exact_mod_cast hn.ne']
    ring
  have H := sample_quintic hn hg h₆ x
  change |binomialSample n g x-∑ r ∈ range 6, d r/(r.factorial:ℝ)*(centered n x r/N^r)|≤_ at H
  rw [poly] at H
  have tail : |binomialSample n g x-(A+U+V)|≤K₆/1440/N^3 := by
    apply H.trans
    change K₆/720*(centered n x 6/N^6)≤_
    calc
      _ ≤ K₆/720*((1/2*N^3)/N^6) := by
        have nn := (abs_nonneg _).trans (h₆ x x.2)
        gcongr
      _ = _ := by field_simp; ring
  have mag : |1-6*q|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have fourth : |U|≤K₄/96/N^3 := by
    dsimp only [U]
    rw [abs_div,abs_mul,abs_div,abs_mul,abs_of_nonneg q0,abs_of_pos (by norm_num : (0:ℝ)<24),
      abs_of_pos (by positivity : 0<N^3)]
    calc
      _ ≤ (K₄/24)*(1/4*1)/N^3 := by
        have h : |d 4|≤K₄ := h₄ x x.2
        have nn := (abs_nonneg _).trans h
        gcongr
      _ = _ := by ring
  have fifth : |V|≤K₅/192/N^3 := by
    dsimp only [V]
    rw [abs_mul,abs_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<120),abs_of_pos (by positivity : 0<N^5)]
    calc
      _ ≤ (K₅/120)*((5/8*N^2)/N^5) := by
        have h : |d 5|≤K₅ := h₅ x x.2
        have nn := (abs_nonneg _).trans h
        gcongr
      _ = _ := by field_simp; ring
  have tri := abs_add_le (binomialSample n g x-(A+U+V)) U
  have tri' := abs_add_le (binomialSample n g x-(A+U+V)+U) V
  rw [show binomialSample n g x-(A+U+V)+U+V=binomialSample n g x-A by ring] at tri'
  change |binomialSample n g x-g x-q*d 2/(2*N)-(q*(1-2*x)*d 3/6+q^2*d 4/8)/N^2|≤_
  rw [show binomialSample n g x-g x-q*d 2/(2*N)-(q*(1-2*x)*d 3/6+q^2*d 4/8)/N^2=
    binomialSample n g x-A by dsimp only [A]; ring]
  change _≤(K₄/96+K₅/192+K₆/1440)/N^3
  rw [add_div,add_div]
  linarith only [tail,fourth,fifth,tri,tri']

theorem sample_second_correction {n : ℕ} (hn : 0<n) {g : ℝ → ℝ} (hg : ContDiff ℝ 6 g)
    {K₄ K₅ K₆ : ℝ} (h₄ : ∀ t∈Icc (0:ℝ) 1, |iteratedDeriv 4 g t|≤K₄)
    (h₅ : ∀ t∈Icc (0:ℝ) 1, |iteratedDeriv 5 g t|≤K₅)
    (h₆ : ∀ t∈Icc (0:ℝ) 1, |iteratedDeriv 6 g t|≤K₆) :
    |sample n g-arc (fun x =>
      let q := x*(1-x)
      g x+q*iteratedDeriv 2 g x/(2*n)+
        (q*(1-2*x)*iteratedDeriv 3 g x/6+q^2*iteratedDeriv 4 g x/8)/(n:ℝ)^2)|≤
      (K₄/96+K₅/192+K₆/1440)/(n:ℝ)^3 := by
  have c2 := hg.continuous_iteratedDeriv 2 (by norm_num)
  have c3 := hg.continuous_iteratedDeriv 3 (by norm_num)
  have c4 := hg.continuous_iteratedDeriv 4 (by norm_num)
  have c0 := hg.continuous
  rw [← arc_binomialSample,← arc_sub (continuous_binomialSample ..) (by dsimp only; fun_prop)]
  apply arc_bound
  intro x hx
  have H := binomial_second_correction hn hg h₄ h₅ h₆ ⟨x,hx⟩
  dsimp only at H ⊢
  simpa only [sub_add_eq_sub_sub] using H

/-- Lattice form with time step `τ`, retaining both signed corrections.
The three derivative bounds need only hold at the splits of this time. -/
theorem sample_split_second {A B : ℝ → ℝ} (ha : ContDiff ℝ 6 A) (hb : ContDiff ℝ 6 B)
    {j : ℕ} (hj : 0<j) {τ v D₄ D₅ D₆ : ℝ} (hτ : 0≤τ) (hv : v=j*τ)
    (b₄ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 4 A B v x≤D₄)
    (b₅ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 5 A B v x≤D₅)
    (b₆ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 6 A B v x≤D₆) :
    |sample j (splitPair A B v)-arc (fun x =>
      let q := x*(1-x)
      splitPair A B v x+τ*(q*v*splitJet 2 A B v x/2)+
        τ^2*(q*(1-2*x)*v*splitJet 3 A B v x/6+q^2*v^2*splitJet 4 A B v x/8))|≤
      τ^3*(v*D₄/96+v^2*D₅/192+v^3*D₆/1440) := by
  have jp : (j:ℝ)≠0 := Nat.cast_ne_zero.mpr hj.ne'
  have v0 : 0≤v := hv ▸ mul_nonneg (Nat.cast_nonneg _) hτ
  have bound (r : ℕ) (hr : r≤6) (D : ℝ) (b : ∀ x∈Icc (0:ℝ) 1, splitJetBound r A B v x≤D)
      (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
      |iteratedDeriv r (splitPair A B v) x|≤v^r*D :=
    (splitPair_derivative_bound (ha.of_le (by exact_mod_cast hr)) (hb.of_le (by exact_mod_cast hr)) v0 x).trans
      (mul_le_mul_of_nonneg_left (b x hx) (pow_nonneg v0 _))
  have H := sample_second_correction hj (splitPair_smooth ha hb v)
    (bound 4 (by decide) _ b₄) (bound 5 (by decide) _ b₅) (bound 6 (by decide) _ b₆)
  convert H using 2
  · congr 1
    apply arc_congr
    intro x _
    dsimp only
    rw [splitPair_derivative (ha.of_le (by norm_num)) (hb.of_le (by norm_num)) (r:=2),
      splitPair_derivative (ha.of_le (by norm_num)) (hb.of_le (by norm_num)) (r:=3),
      splitPair_derivative (ha.of_le (by norm_num)) (hb.of_le (by norm_num)) (r:=4),hv]
    field_simp
  · rw [hv]
    field_simp

end CentralUnimodality.ReturnSplit
