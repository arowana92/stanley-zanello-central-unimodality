module

public import CentralUnimodality.QuadraticResidualPolynomial

/-! Error propagation for replacing Gaussian inputs in the signed quadratic
residual. The bounds use the binomial weights of the split derivatives. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Finset Set

noncomputable def jetMajorant (r : ℕ) (a b : ℕ → ℝ) :=
  ∑ i ∈ range (r+1), (r.choose i:ℝ)*a i*b (r-i)

theorem jet_product_majorant {A B : ℝ → ℝ} {r : ℕ} {v x : ℝ} {a b : ℕ → ℝ}
    (ha : ∀ i≤r, |iteratedDeriv i A (v*x)|≤a i)
    (hb : ∀ i≤r, |iteratedDeriv i B (v*(1-x))|≤b i) :
    |splitJet r A B v x|≤jetMajorant r a b := by
  apply (splitJet_abs ..).trans
  apply sum_le_sum
  intro i hi
  have il : i≤r := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have c := ha i il
  exact mul_le_mul (mul_le_mul_of_nonneg_left c (Nat.cast_nonneg _)) (hb _ (Nat.sub_le ..))
    (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ((abs_nonneg _).trans c))

private theorem splitJet_sub_left {r : ℕ} {P Q : ℝ → ℝ} (p : ContDiff ℝ r P) (q : ContDiff ℝ r Q)
    (F : ℝ → ℝ) (v x : ℝ) : splitJet r (P-Q) F v x=splitJet r P F v x-splitJet r Q F v x := by
  unfold splitJet
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  have il : i≤r := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [iteratedDeriv_sub (p.of_le (by exact_mod_cast il)).contDiffAt (q.of_le (by exact_mod_cast il)).contDiffAt]
  ring

private theorem pair_arc_sub {P Q : ℝ → ℝ} (p : Continuous P) (q : Continuous Q) {F : ℝ → ℝ}
    (f : Continuous F) (v : ℝ) : arc (splitPair (P-Q) F v)=arc (splitPair P F v)-arc (splitPair Q F v) := by
  have cp : Continuous (splitPair P F v) := by unfold splitPair; fun_prop
  have cq : Continuous (splitPair Q F v) := by unfold splitPair; fun_prop
  rw [← arc_sub cp cq]
  apply arc_congr
  intro x _
  simp [splitPair,sub_mul]

private theorem linear_mean_sub {P Q F : ℝ → ℝ} (p : ContDiff ℝ 2 P) (q : ContDiff ℝ 2 Q)
    (f : ContDiff ℝ 2 F) (v : ℝ) : linearJetMean (P-Q) F v=linearJetMean P F v-linearJetMean Q F v := by
  have jp := splitJet_continuous p f v
  have jq := splitJet_continuous q f v
  rw [linearJetMean,linearJetMean,linearJetMean,← arc_sub (by fun_prop) (by fun_prop)]
  apply arc_congr
  intro x _
  rw [splitJet_sub_left p q]
  ring

private theorem second_mean_sub {P Q F : ℝ → ℝ} (p : ContDiff ℝ 4 P) (q : ContDiff ℝ 4 Q)
    (f : ContDiff ℝ 4 F) (v : ℝ) : areaSplitSecond (P-Q) F v=areaSplitSecond P F v-areaSplitSecond Q F v := by
  have cont {A : ℝ → ℝ} (a : ContDiff ℝ 4 A) (r : ℕ) (hr : r≤4) :=
    splitJet_continuous (a.of_le (by exact_mod_cast hr)) (f.of_le (by exact_mod_cast hr)) v
  have p₃ := cont p 3 (by decide)
  have p₄ := cont p 4 (by decide)
  have q₃ := cont q 3 (by decide)
  have q₄ := cont q 4 (by decide)
  simp only [areaSplitSecond]
  rw [← arc_sub (by fun_prop) (by fun_prop)]
  apply arc_congr
  intro x _
  rw [splitJet_sub_left (r:=3) (p.of_le (by norm_num)) (q.of_le (by norm_num)),splitJet_sub_left p q]
  ring

theorem quadratic_form_sub {P P' B₂ C₂ B₁ C₁ B C F G : ℝ → ℝ}
    (b₂ : Continuous B₂) (c₂ : Continuous C₂) (b₁ : ContDiff ℝ 2 B₁) (c₁ : ContDiff ℝ 2 C₁)
    (b : ContDiff ℝ 4 B) (c : ContDiff ℝ 4 C) (f : ContDiff ℝ 4 F) (g : ContDiff ℝ 2 G) (v : ℝ) :
    quadraticResidualForm P B₂ B₁ B F G v-quadraticResidualForm P' C₂ C₁ C F G v=
      quadraticResidualForm (P-P') (B₂-C₂) (B₁-C₁) (B-C) F G v := by
  simp only [quadraticResidualForm,Pi.sub_apply,pair_arc_sub b₂ c₂ f.continuous,
    pair_arc_sub b₁.continuous c₁.continuous g.continuous,
    linear_mean_sub b₁ c₁ (f.of_le (by norm_num)),linear_mean_sub (b.of_le (by norm_num)) (c.of_le (by norm_num)) g,
    second_mean_sub b c f]
  ring

private theorem split_nodes {v x : ℝ} (v0 : 0≤v) (hx : x∈Icc (0:ℝ) 1) :
    v*x∈Icc 0 v ∧ v*(1-x)∈Icc 0 v := by
  have part {t : ℝ} (lo : 0≤t) (hi : t≤1) : v*t∈Icc 0 v :=
    ⟨mul_nonneg v0 lo,(mul_le_mul_of_nonneg_left hi v0).trans_eq (mul_one _)⟩
  exact ⟨part hx.1 hx.2,part (by linarith only [hx.2]) (by linarith only [hx.1])⟩

theorem quadratic_form_bound {P B₂ B₁ B F G : ℝ → ℝ} {v p b₂ : ℝ} (v0 : 0≤v)
    (b₁ b f g : ℕ → ℝ) (hp : |P v|≤p) (h₂ : ∀ t∈Icc 0 v, |B₂ t|≤b₂)
    (h₁ : ∀ i≤2, ∀ t∈Icc 0 v, |iteratedDeriv i B₁ t|≤b₁ i)
    (hb : ∀ i≤4, ∀ t∈Icc 0 v, |iteratedDeriv i B t|≤b i)
    (hf : ∀ i≤4, ∀ t∈Icc 0 v, |iteratedDeriv i F t|≤f i)
    (hg : ∀ i≤2, ∀ t∈Icc 0 v, |iteratedDeriv i G t|≤g i) :
    |quadraticResidualForm P B₂ B₁ B F G v|≤p+b₂*f 0+b₁ 0*g 0+
      v/8*(jetMajorant 2 b₁ f+jetMajorant 2 b g)+v/24*jetMajorant 3 b f+v^2/128*jetMajorant 4 b f := by
  have absprod {x y a c : ℝ} (h : |x|≤a) (k : |y|≤c) : |x*y|≤a*c := by
    rw [abs_mul]; exact mul_le_mul h k (abs_nonneg _) ((abs_nonneg _).trans h)
  have pair {A H : ℝ → ℝ} {a d : ℝ} (l : ∀ t∈Icc 0 v, |A t|≤a) (u : ∀ t∈Icc 0 v, |H t|≤d) :
      |arc (splitPair A H v)|≤a*d := by
    apply arc_bound
    intro x hx
    obtain ⟨s,t⟩ := split_nodes v0 hx
    exact absprod (l _ s) (u _ t)
  have jet {r l k : ℕ} {A H : ℝ → ℝ} {a d : ℕ → ℝ} (rl : r≤l) (rk : r≤k)
      (L : ∀ i≤l, ∀ t∈Icc 0 v, |iteratedDeriv i A t|≤a i)
      (R : ∀ i≤k, ∀ t∈Icc 0 v, |iteratedDeriv i H t|≤d i) (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
      |splitJet r A H v x|≤jetMajorant r a d := by
    obtain ⟨s,t⟩ := split_nodes v0 hx
    exact jet_product_majorant (fun i hi => L _ (hi.trans rl) _ s) (fun i hi => R _ (hi.trans rk) _ t)
  have qw (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : |x*(1-x)|≤1/4 := by
    rw [abs_of_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2))]
    nlinarith only [sq_nonneg (x-1/2)]
  have lin {A H : ℝ → ℝ} {M : ℝ} (bound : ∀ x∈Icc (0:ℝ) 1, |splitJet 2 A H v x|≤M) :
      |linearJetMean A H v|≤v/8*M := by
    apply arc_bound
    intro x hx
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have T := absprod (absprod (qw x hx) (le_of_eq (abs_of_nonneg v0))) (bound x hx)
    linarith only [T]
  have s : |areaSplitSecond B F v|≤v/24*jetMajorant 3 b f+v^2/128*jetMajorant 4 b f := by
    apply arc_bound
    intro x hx
    dsimp only
    have unit : |1-2*x|≤1 := abs_le.mpr ⟨by linarith only [hx.2],by linarith only [hx.1]⟩
    have q := qw x hx
    have q2 : |(x*(1-x))^2|≤(1/4:ℝ)^2 := (abs_pow _ _).trans_le (pow_le_pow_left₀ (abs_nonneg _) q 2)
    have h := absprod (absprod (absprod q unit) (le_of_eq (abs_of_nonneg v0)))
      (jet (by decide : 3≤4) (by decide : 3≤4) hb hf x hx)
    have h' := absprod (absprod q2 (le_of_eq (abs_of_nonneg (sq_nonneg v))))
      (jet le_rfl le_rfl hb hf x hx)
    apply (abs_add_le ..).trans
    rw [abs_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<6),abs_of_pos (by norm_num : (0:ℝ)<8)]
    linarith only [h,h']
  have a := pair h₂ (fun t ht => by simpa using hf 0 (by decide) t ht)
  have e := pair (fun t ht => by simpa using h₁ 0 (by decide) t ht) (fun t ht => by simpa using hg 0 (by decide) t ht)
  have l := lin (jet le_rfl (by decide : 2≤4) h₁ hf)
  have m := lin (jet (by decide : 2≤4) le_rfl hb hg)
  unfold quadraticResidualForm
  apply (abs_sub ..).trans
  apply (add_le_add (abs_sub ..) s).trans
  apply (add_le_add (add_le_add (abs_sub ..) m) le_rfl).trans
  apply (add_le_add (add_le_add (add_le_add (abs_sub ..) l) le_rfl) le_rfl).trans
  apply (add_le_add (add_le_add (add_le_add (add_le_add (abs_sub ..) e) le_rfl) le_rfl) le_rfl).trans
  linarith only [hp,a]

end CentralUnimodality.ReturnSplit
