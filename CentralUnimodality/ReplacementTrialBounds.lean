module

public import CentralUnimodality.GaussianReplacementJets
public import CentralUnimodality.CorrectedLocalDerivatives

/-! Whole-interval bounds for the main polynomial through order four and
for the corrected trial through order two. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Set Finset

def trialJetCap (r : ℕ) : ℕ := if r≤2 then 2 else 10

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem cap_budgets :
    (∀ r∈range 5, rowBudget (valueJetRow candidate r)≤2*2^120*128^r*trialJetCap r) ∧
    (∀ r∈range 3, rowBudget (valueJetRow (correctionCandidate 0) r)≤2*2^120*128^r*64) ∧
    (∀ r∈range 3, rowBudget (valueJetRow (correctionCandidate 1) r)≤2*2^120*128^r*64) := by
  decide +kernel

private theorem from_budget (p : List ℤ) (r C : ℕ) {v : ℝ} (hv : v∈Icc (0:ℝ) 144)
    (K : rowBudget (valueJetRow p r)≤2*2^120*128^r*C) :
    |iteratedDeriv r (value p) v|≤C := by
  apply (iterated_value_row_bound p r ⟨hv.1,by linarith only [hv.2]⟩).trans
  apply (div_le_iff₀ (by positivity)).mpr
  have b : (rowBudget (valueJetRow p r):ℝ)≤2*2^120*128^r*C := by exact_mod_cast K
  linarith only [b]

theorem trial_replacement_jets {r : ℕ} (hr : r≤4) {v : ℝ} (hv : v∈Icc (0:ℝ) 144) :
    |iteratedDeriv r (value candidate) v|≤trialJetCap r :=
  from_budget _ _ _ hv (cap_budgets.1 r (mem_range.mpr (by omega)))

theorem correction_replacement_jets {σ r : ℕ} (hs : σ≤1) (hr : r≤2) {v : ℝ} (hv : v∈Icc (0:ℝ) 144) :
    |iteratedDeriv r (correctedValue σ) v|≤1024 := by
  have index : r∈range 3 := mem_range.mpr (by omega)
  have mass : rowBudget (valueJetRow (correctionCandidate σ) r)≤2*2^120*128^r*64 := by
    interval_cases σ
    · exact cap_budgets.2.1 _ index
    · exact cap_budgets.2.2 _ index
  have m := from_budget _ _ _ hv mass
  have cap (k : ℕ) (hk : k≤4) : |iteratedDeriv k (value candidate) v|≤10 := by
    apply (trial_replacement_jets hk hv).trans
    unfold trialJetCap; split <;> norm_num
  have t := cap (r+2) (by omega)
  have s := cap (r+1) (by omega)
  have r0 : 0≤(r:ℝ)+1 := by positivity
  have rc : (r:ℝ)+1≤3 := by exact_mod_cast (show r+1≤3 by omega)
  have t₁ := mul_le_mul rc s (abs_nonneg _) (by norm_num : (0:ℝ)≤3)
  have t₂ := mul_le_mul hv.2 t (abs_nonneg _) (by norm_num : (0:ℝ)≤144)
  rw [corrected_jet]
  apply (abs_add_le ..).trans
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have inner := abs_add_le (((r:ℝ)+1)*iteratedDeriv (r+1) (value candidate) v)
    (v*iteratedDeriv (r+2) (value candidate) v)
  rw [abs_mul,abs_mul,abs_of_nonneg r0,abs_of_nonneg hv.1] at inner
  norm_num only [Nat.cast_ofNat] at m
  linarith only [m,inner,t₁,t₂]

end CentralUnimodality.PolynomialTrial
