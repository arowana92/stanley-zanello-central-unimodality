module

public import CentralUnimodality.SplitCellInputs

/-! Integer allowances for one split. The lattice term has denominator
`25000·10⁶⁰`, the mixed second derivative `4·10⁶⁰`, and the third
and fourth derivatives `10⁶⁰`. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit Real Set

set_option maxRecDepth 10000

def jetProduct (r : ℕ) (a b : List ℕ) : ℕ :=
  ∑ k ∈ Finset.range (r+1), r.choose k*jetNum a k*jetNum b (r-k)

structure PairBudget where
  lattice : ℕ
  second : ℕ
  third : ℕ
  fourth : ℕ
  deriving Inhabited, DecidableEq, Lean.ToExpr

def pairBudget (a b : CellInputs) : PairBudget := ⟨
  a.bridgeNoise*(25000*jetNum b.trial 0+5*jetNum b.correction 0)+6250*jetNum a.firstBridge 0*jetNum b.correction 0,
  4*jetProduct 2 a.firstBridge b.trial+jetProduct 2 a.bridge b.correction,
  jetProduct 3 a.bridge b.trial,jetProduct 4 a.bridge b.trial⟩

private theorem jet_product_bound (r : ℕ) (A B : ℝ → ℝ) (a b : List ℕ) {s t v x : ℝ}
    (sp : 0<s) (hA : ∀ k≤r, |iteratedDeriv k A (v*x)|≤(jetNum a k:ℝ)/s)
    (hB : ∀ k≤r, |iteratedDeriv k B (v*(1-x))|≤(jetNum b k:ℝ)/t) :
    splitJetBound r A B v x≤(jetProduct r a b:ℝ)/(s*t) := by
  simp only [splitJetBound,jetProduct,Nat.cast_sum,Nat.cast_mul,Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  have ka : k≤r := by simpa using Finset.mem_range.mp hk
  have prod := mul_le_mul (hA k ka) (hB (r-k) (Nat.sub_le ..)) (abs_nonneg _) (by positivity)
  calc
    _≤(r.choose k:ℝ)*((jetNum a k:ℝ)/s*((jetNum b (r-k):ℝ)/t)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left prod (Nat.cast_nonneg (r.choose k))
    _=_ := by ring

theorem split_pair_jets {p q σ : ℕ} (hs : σ≤1) (hp : p<288) (hq : q<288) {v x : ℝ}
    (ha : v*x∈halfInterval p) (hb : v*(1-x)∈halfInterval q) :
    let c := pairBudget (splitInputs p) (splitInputs q)
    splitJetBound 2 bridgeFirst (value candidate) v x+splitJetBound 2 bridgeCurve (correctedValue σ) v x≤
      (c.second:ℝ)/(4*10^60) ∧
    splitJetBound 3 bridgeCurve (value candidate) v x≤(c.third:ℝ)/10^60 ∧
    splitJetBound 4 bridgeCurve (value candidate) v x≤(c.fourth:ℝ)/10^60 := by
  have F (k) (h : k<5) := cell_trial hq h hb
  have G (k) (h : k<3) := cell_correction hs hq h hb
  have B (k) (h : k<5) := cell_bridge hp h ha
  have T (k) (h : k<3) := cell_bridge_first hp h ha
  have two := jet_product_bound 2 _ _ _ _ (by norm_num : (0:ℝ)<10^30) (t:=10^30)
    (fun k h => T k (by omega)) (fun k h => F k (by omega))
  have mix := jet_product_bound 2 _ _ _ _ (by norm_num : (0:ℝ)<10^30) (t:=4*10^30)
    (fun k h => B k (by omega)) (fun k h => G k (by omega))
  have pure (r : ℕ) (hr : r≤4) := jet_product_bound r _ _ _ _ (by norm_num : (0:ℝ)<10^30) (t:=10^30)
    (fun k h => B k (by omega)) (fun k h => F k (by omega))
  refine ⟨(add_le_add two mix).trans_eq ?_,(pure 3 (by decide)).trans_eq ?_,(pure 4 (by decide)).trans_eq ?_⟩
  all_goals simp only [pairBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]; ring

theorem split_pair_lattice {p q σ : ℕ} (hs : σ≤1) (hp : p<288) (hq : q<288) {a b τ : ℝ}
    (ha : a∈halfInterval p) (hb : b∈halfInterval q) (t0 : 0≤τ) (ht : τ≤(maxStep:ℝ)) :
    bridgeLocalCost a τ*(|value candidate b|+τ*|correctedValue σ b|)+|bridgeFirst a| *|correctedValue σ b|≤
      ((pairBudget (splitInputs p) (splitInputs q)).lattice:ℝ)/(25000*10^60) := by
  have noise := (cell_noise hp hs ha t0 ht).2
  have F := cell_trial hq (by decide : 0<5) hb
  have G := cell_correction hs hq (by decide : 0<3) hb
  have T := cell_bridge_first hp (by decide : 0<3) ha
  simp only [iteratedDeriv_zero] at F G T
  have mix := mul_le_mul ht G (abs_nonneg _) (t0.trans ht)
  have l := mul_le_mul noise (add_le_add F mix) (by positivity) (by positivity)
  have r := mul_le_mul T G (abs_nonneg _) (by positivity)
  apply (add_le_add l r).trans_eq
  simp only [pairBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  norm_num [maxStep]; ring

end CentralUnimodality.PolynomialTrial
