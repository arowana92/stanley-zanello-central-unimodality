module

public import CentralUnimodality.QuadraticLatticeResidual
public import CentralUnimodality.SecondOrderQuadrature

/-! The signed quadratic coefficient in the last-return residual and the five
cell costs for its cubic remainder. Bounds on sums of product jets can be
applied at the same spatial split before taking their maximum. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Set

theorem splitJet_continuous {A B : ℝ → ℝ} {r : ℕ} (ha : ContDiff ℝ r A) (hb : ContDiff ℝ r B) (v : ℝ) :
    Continuous (splitJet r A B v) := by
  unfold splitJet
  apply continuous_finsetSum
  intro i hi
  have il : i≤r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have l := ha.continuous_iteratedDeriv i (by exact_mod_cast il)
  have h := hb.continuous_iteratedDeriv (r-i) (by exact_mod_cast (Nat.sub_le r i))
  fun_prop

noncomputable def areaSplitSecond (A B : ℝ → ℝ) (v : ℝ) :=
  arc (fun x => let q := x*(1-x)
    q*(1-2*x)*v*splitJet 3 A B v x/6+q^2*v^2*splitJet 4 A B v x/8)

noncomputable def secondCurveResidual (F G : ℝ → ℝ) (σ : ℕ) (v : ℝ) :=
  freeSecond σ v-arc (secondMixedCurve F G v)-
    (v/2)*arc (fun x => x*(1-x)*(splitJet 2 bridgeFirst F v x+splitJet 2 bridgeCurve G v x))-
    areaSplitSecond bridgeCurve F v

private theorem split_second_separated {A B : ℝ → ℝ} (ha : ContDiff ℝ 6 A) (hb : ContDiff ℝ 6 B)
    {j : ℕ} (hj : 0<j) {τ v D₄ D₅ D₆ : ℝ} (hτ : 0≤τ) (hv : v=j*τ)
    (b₄ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 4 A B v x≤D₄)
    (b₅ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 5 A B v x≤D₅)
    (b₆ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 6 A B v x≤D₆) :
    |sample j (splitPair A B v)-(arc (splitPair A B v)+
      τ*((v/2)*arc (fun x => x*(1-x)*splitJet 2 A B v x))+τ^2*areaSplitSecond A B v)|≤
      τ^3*(v*D₄/96+v^2*D₅/192+v^3*D₆/1440) := by
  have cf := (splitPair_smooth ha hb v).continuous
  have cj (r : ℕ) (hr : r≤6) := splitJet_continuous (ha.of_le (by exact_mod_cast hr)) (hb.of_le (by exact_mod_cast hr)) v
  have two := cj 2 (by decide)
  have three := cj 3 (by decide)
  have four := cj 4 (by decide)
  have H := sample_split_second ha hb hj hτ hv b₄ b₅ b₆
  dsimp only at H
  rw [areaSplitSecond,← arc_const_mul,← arc_const_mul,← arc_const_mul,
    ← arc_add cf (by fun_prop),← arc_add (by fun_prop) (by fun_prop)]
  convert H using 3
  apply arc_congr
  intro x _
  dsimp only
  ring

private theorem pair_sum_bound {A B C D : ℝ → ℝ} {r : ℕ} (a : ContDiff ℝ r A)
    (b : ContDiff ℝ r B) (c : ContDiff ℝ r C) (d : ContDiff ℝ r D) {v : ℝ} (v0 : 0≤v) (x : ℝ) :
    |iteratedDeriv r (splitPair A B v+splitPair C D v) x|≤
      v^r*(splitJetBound r A B v x+splitJetBound r C D v x) := by
  rw [iteratedDeriv_add (splitPair_smooth a b v).contDiffAt (splitPair_smooth c d v).contDiffAt,mul_add]
  exact (abs_add_le ..).trans (add_le_add (splitPair_derivative_bound a b v0 x)
    (splitPair_derivative_bound c d v0 x))

private theorem sample_combine (j : ℕ) (g m s : ℝ → ℝ) (τ : ℝ) :
    sample j (fun x => g x+τ*m x+τ^2*s x)=sample j g+τ*sample j (fun x => m x+τ*s x) := by
  simp only [sample,average,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem quadratic_split_residual {ω τ : ℝ} {j N σ : ℕ} (hs : σ≤1) (hτ : 0≤τ) (hω : ω^2=τ^3/32)
    (hj : j≤N) (hN : 10000≤N) (hu : (N:ℝ)*τ≤114) (F G : ℝ → ℝ)
    (hF : ContDiff ℝ 6 F) (hG : ContDiff ℝ 4 G) (v : ℝ) (hv : v=j*τ)
    {K D₂ D₃ D₄ M₄ M₅ M₆ : ℝ}
    (cost : ∀ k≤j, let a := (k:ℝ)*τ; let b := ((j-k:ℕ):ℝ)*τ
      bridgeQuadraticCost a τ*(|F b|+τ*|G b|)+|bridgeSecond a| *|G b|≤K)
    (two : ∀ x∈Icc (0:ℝ) 1, splitJetBound 2 bridgeSecond F v x+splitJetBound 2 bridgeFirst G v x≤D₂)
    (three : ∀ x∈Icc (0:ℝ) 1, splitJetBound 3 bridgeFirst F v x+splitJetBound 3 bridgeCurve G v x≤D₃)
    (four : ∀ x∈Icc (0:ℝ) 1, splitJetBound 4 bridgeFirst F v x+splitJetBound 4 bridgeCurve G v x≤D₄)
    (base₄ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 4 bridgeCurve F v x≤M₄)
    (base₅ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 5 bridgeCurve F v x≤M₅)
    (base₆ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 6 bridgeCurve F v x≤M₆) :
    ‖parityResidual ω (trialSeries (fun k => F ((k:ℝ)*τ)+τ*G ((k:ℝ)*τ))) σ j-
      ((curveResidual F v+τ*firstCurveResidual F G σ v+τ^2*secondCurveResidual F G σ v:ℝ):ℂ)‖≤
      τ^3*(freeQuadraticCost σ v τ+K+v*D₂/8+v*D₃/24+v^2*D₄/128+v*M₄/96+v^2*M₅/192+v^3*M₆/1440) := by
  let g := splitCurve F v
  let m := mixedCurve F G v
  let s := secondMixedCurve F G v
  let e := fun x => splitJet 2 bridgeFirst F v x+splitJet 2 bridgeCurve G v x
  let d := fun x => x*(1-x)*splitJet 2 bridgeCurve F v x
  let Q := arc g+τ*(v/2*arc d)+τ^2*areaSplitSecond bridgeCurve F v+
    τ*(arc m+τ*(arc s+(v/2)*arc (fun x => x*(1-x)*e x)))
  let M := v*D₂/8+v*D₃/24+v^2*D₄/128
  let U := v*M₄/96+v^2*M₅/192+v^3*M₆/1440
  have v0 : 0≤v := hv ▸ mul_nonneg (Nat.cast_nonneg _) hτ
  have hb (r : ℕ) : ContDiff ℝ r bridgeCurve := by unfold bridgeCurve; fun_prop
  have h₁ (r : ℕ) : ContDiff ℝ r bridgeFirst := by unfold bridgeFirst bridgeCurve bridgeLogCorrection; fun_prop
  have h₂ (r : ℕ) : ContDiff ℝ r bridgeSecond := by
    unfold bridgeSecond bridgeCurve bridgeLogCorrection bridgeSecondLog; fun_prop
  have hf (r : ℕ) (hr : r≤6) : ContDiff ℝ r F := hF.of_le (by exact_mod_cast hr)
  have ht (r : ℕ) (hr : r≤4) : ContDiff ℝ r G := hG.of_le (by exact_mod_cast hr)
  have quad : |sample j (fun x => g x+τ*m x+τ^2*s x)-Q|≤τ^3*(M+U) := by
    by_cases zero : j=0
    · subst j
      have vz : v=0 := by simpa using hv
      subst v
      have ga : splitCurve F 0=fun _ => bridgeCurve 0*F 0 := by funext x; simp [splitCurve]
      have ma : mixedCurve F G 0=fun _ => bridgeFirst 0*F 0+bridgeCurve 0*G 0 := by funext x; simp [mixedCurve]
      have sa : secondMixedCurve F G 0=fun _ => bridgeSecond 0*F 0+bridgeFirst 0*G 0 := by
        funext x; simp [secondMixedCurve,splitPair]
      simp [Q,g,m,s,M,U,ga,ma,sa,areaSplitSecond,
        sample,average,weight,survival,arc_const]
      ring
    have jp := Nat.pos_of_ne_zero zero
    have base := split_second_separated (hb 6) hF jp hτ hv base₄ base₅ base₆
    have positive (r : ℕ) (A B : ℝ → ℝ) : 0≤splitJetBound r A B v 0 := by unfold splitJetBound; positivity
    have mem : (0:ℝ)∈Icc 0 1 := by norm_num
    have mixed := direct_split_error (g:=m) (m:=s) (e:=e) jp hv hτ
      ((add_nonneg (positive 2 _ _) (positive 2 _ _)).trans (two 0 mem))
      ((add_nonneg (positive 4 _ _) (positive 4 _ _)).trans (four 0 mem))
      ((splitPair_smooth (h₁ 4) (hf 4 (by decide)) v).add (splitPair_smooth (hb 4) hG v))
      ((splitPair_smooth (h₂ 2) (hf 2 (by decide)) v).add (splitPair_smooth (h₁ 2) (ht 2 (by decide)) v))
      (by intro x
          change iteratedDeriv 2 (splitPair bridgeFirst F v+splitPair bridgeCurve G v) x=_
          rw [iteratedDeriv_add (splitPair_smooth (h₁ 2) (hf 2 (by decide)) v).contDiffAt
            (splitPair_smooth (hb 2) (ht 2 (by decide)) v).contDiffAt,
            splitPair_derivative (h₁ 2) (hf 2 (by decide)),splitPair_derivative (hb 2) (ht 2 (by decide)),mul_add])
      (fun x hx => (pair_sum_bound (h₂ 2) (hf 2 (by decide)) (h₁ 2) (ht 2 (by decide)) v0 x).trans
        (mul_le_mul_of_nonneg_left (two x hx) (pow_nonneg v0 _)))
      (fun x hx => (pair_sum_bound (h₁ 3) (hf 3 (by decide)) (hb 3) (ht 3 (by decide)) v0 x).trans
        (mul_le_mul_of_nonneg_left (three x hx) (pow_nonneg v0 _)))
      (fun x hx => (pair_sum_bound (h₁ 4) (hf 4 (by decide)) (hb 4) hG v0 x).trans
        (mul_le_mul_of_nonneg_left (four x hx) (pow_nonneg v0 _)))
    change |sample j g-(arc g+τ*(v/2*arc d)+τ^2*areaSplitSecond bridgeCurve F v)|≤τ^3*U at base
    rw [sample_combine]
    dsimp only [Q]
    rw [show sample j g+τ*sample j (fun x => m x+τ*s x)-
      (arc g+τ*(v/2*arc d)+τ^2*areaSplitSecond bridgeCurve F v+τ*(arc m+τ*(arc s+v/2*arc (fun x => x*(1-x)*e x))))=
      (sample j g-(arc g+τ*(v/2*arc d)+τ^2*areaSplitSecond bridgeCurve F v))+
      τ*(sample j (fun x => m x+τ*s x)-(arc m+τ*(arc s+v/2*arc (fun x => x*(1-x)*e x)))) by ring]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_of_nonneg hτ]
    exact (add_le_add base (mul_le_mul_of_nonneg_left mixed hτ)).trans_eq (by dsimp [U,M]; ring)
  let S := sample j (fun x => g x+τ*m x+τ^2*s x)
  let P := freeCurve v*(1-τ*freeLogCorrection σ v)+τ^2*freeSecond σ v-S
  let R := curveResidual F v+τ*firstCurveResidual F G σ v+τ^2*secondCurveResidual F G σ v
  have eq : P-R= -(S-Q) := by
    dsimp only [P,R,Q,g,m,s,d,e,curveResidual,firstCurveResidual,secondCurveResidual]; ring
  have approx : ‖(P:ℂ)-(R:ℂ)‖≤τ^3*(M+U) := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,eq,abs_neg]; exact quad
  have H := quadratic_lattice_residual hs hτ hω hj hN hu F G v hv cost
  calc
    _ ≤ ‖parityResidual ω _ σ j-(P:ℂ)‖+‖(P:ℂ)-(R:ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ _ := (add_le_add H approx).trans_eq (by dsimp [M,U]; ring)

end CentralUnimodality.ReturnSplit
