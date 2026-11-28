module

public import CentralUnimodality.HalfIntervalDerivatives
public import CentralUnimodality.VerifiedCorrectionPowers

/-! Integer upper bounds in units of 10⁻³⁰. One shift of the original
polynomial supplies all requested derivative orders for the cell. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit

def ceilQuotient (u d : ℕ) := (u+d-1)/d

private theorem ceilQuotient_upper (u : ℕ) {d : ℕ} (hd : 0<d) : u≤ceilQuotient u d*d := by
  have h := Nat.mod_lt (u+d-1) hd
  have e := Nat.mod_add_div (u+d-1) d
  unfold ceilQuotient
  rw [Nat.mul_comm] at e
  omega

def jetDen (a : List ℤ) : ℕ := 1024^a.length*2^120

def jetEntries (d k : ℕ) : ℕ → List ℤ → List ℕ
  | 0, _ => []
  | n+1, a => ceilQuotient (10^30*4^k*coefficientMass a) d :: jetEntries d (k+1) n (powerDerivative a)

def localJetTable (a : List ℤ) (i orders : ℕ) :=
  jetEntries (jetDen a) 0 orders (packedAffineRow 5376 (2*i+1) a)

private theorem jet_entry (a : List ℤ) (d k r orders : ℕ) (hr : r<orders) :
    (jetEntries d k orders a)[r]?=some (ceilQuotient (10^30*4^(k+r)*coefficientMass (powerDerivative^[r] a)) d) := by
  induction orders generalizing a k r with
  | zero => omega
  | succ n ih =>
    cases r with
    | zero => simp [jetEntries]
    | succ r =>
      rw [jetEntries,List.getElem?_cons_succ,ih _ _ _ (by omega),Function.iterate_succ_apply,
        show k+1+r=k+(r+1) by omega]

theorem localJetTable_bound {f : ℝ → ℝ} (a : List ℤ)
    (rep : ∀ v, f v=(realDense a).eval (v/256)/2^120)
    (cap : coefficientMass a*1024^a.length<2^5376) {i orders r b : ℕ} (hi : i<288) (hr : r<orders)
    (tab : (localJetTable a i orders)[r]?=some b) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r f v|≤(b:ℝ)/10^30 := by
  unfold localJetTable at tab
  rw [jet_entry _ _ _ _ _ hr,Nat.zero_add,Option.some_inj] at tab
  have dpos : 0<jetDen a := by unfold jetDen; positivity
  have up := ceilQuotient_upper (10^30*4^r*coefficientMass
    (powerDerivative^[r] (packedAffineRow 5376 (2*i+1) a))) dpos
  rw [tab] at up
  have bound : 10^30*binJetInteger 5376 i r a≤b*jetDen a := by simpa only [binJetInteger,Nat.mul_assoc] using up
  apply (binJet_bound a rep 5376 i r hi cap hv).trans
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
  rw [mul_comm (binJetInteger .. : ℝ)]
  exact_mod_cast bound

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem local_trial_bound {i r b : ℕ} (hi : i<288) (hr : r<5)
    (tab : (localJetTable rawTrial i 5)[r]?=some b) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r (value candidate) v|≤(b:ℝ)/10^30 := by
  apply localJetTable_bound rawTrial _ (by decide +kernel) hi hr tab hv
  intro x
  rw [← rawTrial_exact]
  exact normalized_input 1536 _ (by decide +kernel) x

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem local_correction_bound {σ i r b : ℕ} (hs : σ≤1) (hi : i<288) (hr : r<3)
    (tab : (localJetTable (if σ=0 then evenRawM else oddRawM) i 3)[r]?=some b)
    {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r (value (correctionCandidate σ)) v|≤(b:ℝ)/10^30 := by
  rcases (show σ=0 ∨ σ=1 by omega) with rfl|rfl
  · apply localJetTable_bound evenRawM _ (by decide +kernel) hi hr tab hv
    intro x
    rw [← evenRawM_exact]
    exact normalized_input 1536 _ (by decide +kernel) x
  · apply localJetTable_bound oddRawM _ (by decide +kernel) hi hr tab hv
    intro x
    rw [← oddRawM_exact]
    exact normalized_input 1536 _ (by decide +kernel) x

end CentralUnimodality.PolynomialTrial
