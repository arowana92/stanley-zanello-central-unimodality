module

public import CentralUnimodality.LocalJetBlock0
public import CentralUnimodality.LocalJetBlock1
public import CentralUnimodality.LocalJetBlock2
public import CentralUnimodality.LocalJetBlock3
public import CentralUnimodality.CorrectedLocalDerivatives

/-! Checked pointwise derivatives for the trial and its corrected
physical amplitude in every retained half-unit bin. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit

theorem all_jet_blocks {b : ℕ} (hb : b<72) : jetsCheck b=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hj' := List.mem_range.mp hj
  let i := 4*b+j
  change (jetWitnesses[i]? == some (jetBoundsAt i))=true
  apply beq_iff_eq.mpr
  by_cases a : i<72
  · simpa only [Nat.zero_add] using jet_block_0 i a
  by_cases c : i<144
  · simpa only [show 72+(i-72)=i by omega] using jet_block_1 (i-72) (by omega)
  by_cases d : i<216
  · simpa only [show 144+(i-144)=i by omega] using jet_block_2 (i-144) (by omega)
  have endpt : i<288 := by dsimp [i]; omega
  simpa only [show 216+(i-216)=i by omega] using jet_block_3 (i-216) (by omega)

def trialJetNum (i r : ℕ) := ((jetWitnesses[i]?.getD default).1[r]?).getD 0

def correctionJetNum (i r : ℕ) : ℕ :=
  let t := jetWitnesses[i]?.getD default
  4*max ((t.2.1[r]?).getD 0) ((t.2.2[r]?).getD 0)+2*(r+1)*trialJetNum i (r+1)+(i+1)*trialJetNum i (r+2)

private theorem local_get (a : List ℤ) (i n r : ℕ) (hr : r<n) :
    (localJetTable a i n)[r]?=some (((localJetTable a i n)[r]?).getD 0) := by
  have len (d k count : ℕ) (p : List ℤ) : (jetEntries d k count p).length=count := by
    induction count generalizing k p with
    | zero => rfl
    | succ c ih => simp [jetEntries,ih]
  have inRange : r<(localJetTable a i n).length := by simpa [localJetTable,len] using hr
  simp [List.getElem?_eq_getElem inRange]

theorem certified_trial_jet {i r : ℕ} (hi : i<288) (hr : r<5) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r (value candidate) v|≤(trialJetNum i r:ℝ)/10^30 := by
  have eq := jets_from_blocks (fun _ h => all_jet_blocks h) hi
  apply local_trial_bound hi hr _ hv
  simp only [trialJetNum,eq,Option.getD_some,jetBoundsAt]
  exact local_get _ _ _ _ hr

set_option maxRecDepth 10000 in
theorem certified_correction_jet {σ i r : ℕ} (hs : σ≤1) (hi : i<288) (hr : r<3) {v : ℝ}
    (hv : v∈halfInterval i) : |iteratedDeriv r (correctedValue σ) v|≤(correctionJetNum i r:ℝ)/(4*10^30) := by
  let t := jetWitnesses[i]?.getD default
  let e := (t.2.1[r]?).getD 0
  let o := (t.2.2[r]?).getD 0
  have eq := jets_from_blocks (fun _ h => all_jet_blocks h) hi
  have lookup : (localJetTable (if σ=0 then evenRawM else oddRawM) i 3)[r]?=some (if σ=0 then e else o) := by
    dsimp only [e,o,t]
    rw [eq]; simp only [Option.getD_some,jetBoundsAt]
    split <;> exact local_get _ _ _ _ hr
  have one := local_correction_bound hs hi hr lookup hv
  have both : |iteratedDeriv r (value (correctionCandidate σ)) v|≤(max e o:ℕ)/(10^30:ℝ) := by
    apply one.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (show (if σ=0 then e else o)≤max e o by split <;> simp)
  have bound := corrected_jet_bound hv both (certified_trial_jet hi (by omega : r+1<5) hv)
    (certified_trial_jet hi (by omega : r+2<5) hv)
  apply bound.trans_eq
  change _=(((4*max e o+2*(r+1)*trialJetNum i (r+1)+(i+1)*trialJetNum i (r+2)):ℕ):ℝ)/(4*10^30)
  push_cast; ring

end CentralUnimodality.PolynomialTrial
