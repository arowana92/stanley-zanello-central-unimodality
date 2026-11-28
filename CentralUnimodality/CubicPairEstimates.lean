module

public import CentralUnimodality.CubicPairMaxima

/-! Pointwise meaning of the seven independent maxima. Both factors in
each derivative product are evaluated at the same split. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit Set

structure CubicInputs.Sound (c : CubicInputs) (i : ℕ) : Prop where
  main : ∀ {r : ℕ}, r<7 → ∀ {v : ℝ}, v∈halfInterval i → |iteratedDeriv r bridgeCurve v|≤(jetNum c.main r:ℝ)/10^30
  first : ∀ {r : ℕ}, r<5 → ∀ {v : ℝ}, v∈halfInterval i → |iteratedDeriv r bridgeFirst v|≤(jetNum c.first r:ℝ)/10^30
  second : ∀ {r : ℕ}, r<3 → ∀ {v : ℝ}, v∈halfInterval i → |iteratedDeriv r bridgeSecond v|≤(jetNum c.second r:ℝ)/10^30
  trial : ∀ {r : ℕ}, r<7 → ∀ {v : ℝ}, v∈halfInterval i → |iteratedDeriv r (value candidate) v|≤(jetNum c.trial r:ℝ)/10^30
  signed : ∀ {σ r : ℕ}, σ≤1 → r<5 → ∀ {v : ℝ}, v∈halfInterval i →
    |iteratedDeriv r (correctedValue σ) v|≤(jetNum c.signed r:ℝ)/10^30
  noise : ∀ {σ : ℕ}, σ≤1 → ∀ {v τ : ℝ}, v∈halfInterval i → 0≤τ → τ≤57/5000 →
    freeQuadraticCost σ v τ≤(c.freeNoise:ℝ)/10^30 ∧ bridgeQuadraticCost v τ≤(c.bridgeNoise:ℝ)/10^30

private theorem product_bound (r : ℕ) (A B : ℝ → ℝ) (a b : List ℕ) {v x : ℝ}
    (ha : ∀ k≤r, |iteratedDeriv k A (v*x)|≤(jetNum a k:ℝ)/10^30)
    (hb : ∀ k≤r, |iteratedDeriv k B (v*(1-x))|≤(jetNum b k:ℝ)/10^30) :
    splitJetBound r A B v x≤(jetProduct r a b:ℝ)/10^60 := by
  simp only [splitJetBound,jetProduct,Nat.cast_sum,Nat.cast_mul,Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  have kl : k≤r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have prod := mul_le_mul (ha k kl) (hb (r-k) (Nat.sub_le ..)) (abs_nonneg _) (by positivity)
  calc
    _≤(r.choose k:ℝ)*((jetNum a k:ℝ)/10^30*((jetNum b (r-k):ℝ)/10^30)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left prod (Nat.cast_nonneg (r.choose k))
    _=_ := by ring

theorem cubic_pair_jets {p q σ : ℕ} (hs : σ≤1) {a b : CubicInputs} (A : a.Sound p) (B : b.Sound q)
    {v x : ℝ} (hp : v*x∈halfInterval p) (hq : v*(1-x)∈halfInterval q) :
    let F := value candidate; let G := correctedValue σ
    (splitJetBound 2 bridgeSecond F v x+splitJetBound 2 bridgeFirst G v x≤(cubicPairEntry a b 1:ℝ)/10^60) ∧
    (splitJetBound 3 bridgeFirst F v x+splitJetBound 3 bridgeCurve G v x≤(cubicPairEntry a b 2:ℝ)/10^60) ∧
    (splitJetBound 4 bridgeFirst F v x+splitJetBound 4 bridgeCurve G v x≤(cubicPairEntry a b 3:ℝ)/10^60) ∧
    (splitJetBound 4 bridgeCurve F v x≤(cubicPairEntry a b 4:ℝ)/10^60) ∧
    (splitJetBound 5 bridgeCurve F v x≤(cubicPairEntry a b 5:ℝ)/10^60) ∧
    (splitJetBound 6 bridgeCurve F v x≤(cubicPairEntry a b 6:ℝ)/10^60) := by
  have f (r : ℕ) (h : r<7) := B.trial h hq
  have g (r : ℕ) (h : r<5) := B.signed hs h hq
  have a0 (r : ℕ) (h : r<7) := A.main h hp
  have a1 (r : ℕ) (h : r<5) := A.first h hp
  have a2 (r : ℕ) (h : r<3) := A.second h hp
  dsimp only
  simp only [cubicPairEntry,Nat.cast_add,add_div]
  refine ⟨add_le_add ?_ ?_,add_le_add ?_ ?_,add_le_add ?_ ?_,?_,?_,?_⟩
  all_goals apply product_bound
  all_goals intro k hk
  all_goals first | exact a0 k (by omega) | exact a1 k (by omega) | exact a2 k (by omega) |
      exact f k (by omega) | exact g k (by omega)

theorem cubic_pair_lattice {p q σ : ℕ} (hs : σ≤1) {a b : CubicInputs} (A : a.Sound p) (B : b.Sound q)
    {v w τ : ℝ} (hp : v∈halfInterval p) (hq : w∈halfInterval q) (t0 : 0≤τ) (ht : τ≤57/5000) :
    bridgeQuadraticCost v τ*(|value candidate w|+τ*|correctedValue σ w|)+|bridgeSecond v| * |correctedValue σ w|≤
      (cubicPairEntry a b 0:ℝ)/(5000*10^60) := by
  have z := (A.noise hs hp t0 ht).2
  have f := B.trial (by decide : 0<7) hq
  have g := B.signed hs (by decide : 0<5) hq
  have s := A.second (by decide : 0<3) hp
  simp only [iteratedDeriv_zero] at f g s
  have tg := mul_le_mul ht g (abs_nonneg _) (by norm_num)
  have l := mul_le_mul z (add_le_add f tg) (add_nonneg (abs_nonneg _) (mul_nonneg t0 (abs_nonneg _))) (by positivity)
  have right := mul_le_mul s g (abs_nonneg _) (by positivity)
  apply (add_le_add l right).trans_eq
  simp only [cubicPairEntry,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

end CentralUnimodality.PolynomialTrial
