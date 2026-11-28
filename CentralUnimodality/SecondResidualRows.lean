module

public import CentralUnimodality.RationalPolynomialRows
public import CentralUnimodality.FirstPackedCertificate

/-! Exact evaluator for the signed second coefficient of each dyadic trial.
The output polynomial is expressed in physical time, with one common
positive denominator. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit

namespace RationalPolyRow

def physicalNumer : List ℤ → List ℤ
  | [] => []
  | x::xs => (x*256^(xs.length+1))::physicalNumer xs

def physicalRow (a : List ℤ) : RationalPolyRow :=
  ⟨physicalNumer a,⟨2^120*256^a.length,by positivity⟩⟩

private theorem physical_numer_eval (a : List ℤ) (v : ℝ) :
    (realDense (physicalNumer a)).eval v=256^a.length*(realDense a).eval (v/256) := by
  have cons (x : ℤ) (a : List ℤ) (t : ℝ) :
      (realDense (x::a)).eval t=(x:ℝ)+t*(realDense a).eval t := by simp [realDense,densePoly]
  induction a with
  | nil => simp [physicalNumer,realDense,densePoly]
  | cons x a ih => simp only [physicalNumer,cons,ih,List.length_cons,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,pow_succ]; ring

theorem physical_row_model (a : List ℤ) (b : ℕ) (small : (coefficientMass a:ℤ)*7^a.length<2^b) :
    (physicalRow (unpackCheb b a)).model=physicalPoly (doubleHead a) := by
  apply Polynomial.funext; intro v
  simp only [physicalRow,model,eval_mul,eval_C,physical_numer_eval,physical_eval,normalized_input b a small]
  let p := unpackCheb b a
  change 1/((2^120*256^p.length:ℕ):ℝ)*(256^p.length*(realDense p).eval (v/256))=_
  push_cast
  field_simp
  ring

def weightedJetRow (r a b : ℕ) (p q : RationalPolyRow) :=
  sumRows (fun i => scale ((r.choose i:ℤ)*(-1)^(r-i)) 1
    (weighted a b (diff i p) (diff (r-i) q))) (r+1)

theorem model_weighted_jet (r a b : ℕ) (p q : RationalPolyRow) :
    (weightedJetRow r a b p q).model=weightedSplitJet r a b p.model q.model := by
  simp [weightedJetRow,model_sum,model_scale,model_weighted,model_diff,weightedSplitJet]

def splitFirst (p q : RationalPolyRow) := scale 1 2 (shift 1 (weightedJetRow 2 1 1 p q))

def splitSecond (p q : RationalPolyRow) :=
  linear 1 1 (scale 1 6 (shift 1 (linear 1 (-1) (weightedJetRow 3 1 2 p q) (weightedJetRow 3 2 1 p q))))
    (scale 1 8 (shift 2 (weightedJetRow 4 2 2 p q)))

theorem model_split_first (p q : RationalPolyRow) : (splitFirst p q).model=splitFirstPoly p.model q.model := by
  simp [splitFirst,model_scale,model_shift,model_weighted_jet,splitFirstPoly,mul_assoc]

theorem model_split_second (p q : RationalPolyRow) : (splitSecond p q).model=splitSecondPoly p.model q.model := by
  simp only [splitSecond,model_linear,model_scale,model_shift,model_weighted_jet,splitSecondPoly]
  norm_num
  ring

def residual (p₂ b₂ b₁ b f g : RationalPolyRow) :=
  let leading := linear 1 (-1) (linear 1 (-1) p₂ (beta b₂ f)) (beta b₁ g)
  let first := linear 1 1 (splitFirst b₁ f) (splitFirst b g)
  linear 1 (-1) (linear 1 (-1) leading first) (splitSecond b f)

theorem model_residual (p₂ b₂ b₁ b f g : RationalPolyRow) :
    (residual p₂ b₂ b₁ b f g).model=secondResidualPoly p₂.model b₂.model b₁.model b.model f.model g.model := by
  simp [residual,model_linear,model_beta,model_split_first,model_split_second,secondResidualPoly]
  ring

def halfDriftRow (p : RationalPolyRow) := scale 1 2 (linear 1 1 (diff 1 p) (shift 1 (diff 2 p)))

theorem model_half_drift (p : RationalPolyRow) : (halfDriftRow p).model=halfDrift p.model := by
  simp [halfDriftRow,model_scale,model_linear,model_diff,model_shift,halfDrift,Function.iterate_succ_apply']

def freeLogRow (σ : ℕ) := linear 1 1 (term 2 (2*σ+1) 32) (term 5 1 1920)
def bridgeLogRow := linear 1 1 (term 2 1 192) (term 5 1 30720)
def freeLogSecondRow (σ : ℕ) :=
  linear 1 1 (linear 1 1 (term 1 (12*σ+1) 192) (term 4 (2*σ+1) 1536)) (term 7 1 80640)
def bridgeLogSecondRow := linear 1 1 (term 4 7 184320) (term 7 1 5160960)

private theorem log_models (σ : ℕ) :
    (freeLogRow σ).model=freeLogPoly σ ∧ bridgeLogRow.model=bridgeLogPoly ∧
      (freeLogSecondRow σ).model=freeSecondLogPoly σ ∧ bridgeLogSecondRow.model=bridgeSecondLogPoly := by
  norm_num [freeLogRow,bridgeLogRow,freeLogSecondRow,bridgeLogSecondRow,
    model_linear,model_term,freeLogPoly,bridgeLogPoly,freeSecondLogPoly,bridgeSecondLogPoly]

def secondMultiplierRow (a b : RationalPolyRow) := linear 1 (-1) (scale 1 2 (mul a a)) b

private theorem model_multiplier (a b : RationalPolyRow) :
    (secondMultiplierRow a b).model=secondMultiplier a.model b.model := by
  simp [secondMultiplierRow,model_linear,model_scale,model_mul,secondMultiplier,pow_two,sub_eq_add_neg]

def fromTrials (σ : ℕ) (p b f m : RationalPolyRow) :=
  residual (mul p (secondMultiplierRow (freeLogRow σ) (freeLogSecondRow σ)))
    (mul b (secondMultiplierRow bridgeLogRow bridgeLogSecondRow)) (scale (-1) 1 (mul b bridgeLogRow))
    b f (linear 1 1 m (halfDriftRow f))

end RationalPolyRow

open RationalPolyRow

def quadraticResidualRow (σ : ℕ) :=
  fromTrials σ (physicalRow rawFree) (physicalRow rawBridge) (physicalRow rawTrial)
    (physicalRow (if σ=0 then evenRawM else oddRawM))

theorem quadratic_residual_row_model {σ : ℕ} (hs : σ≤1) : (quadraticResidualRow σ).model=secondPoly σ := by
  have p : (physicalRow rawFree).model=physicalPoly freeCandidate := by
    rw [← rawFree_exact]; exact physical_row_model _ _ input_pack_bounds.1
  have b : (physicalRow rawBridge).model=physicalPoly bridgeCandidate := by
    rw [← rawBridge_exact]; exact physical_row_model _ _ input_pack_bounds.2.1
  have f : (physicalRow rawTrial).model=physicalPoly candidate := by
    rw [← rawTrial_exact]; exact physical_row_model _ _ input_pack_bounds.2.2.1
  have m : (physicalRow (if σ=0 then evenRawM else oddRawM)).model=physicalPoly (correctionCandidate σ) := by
    have selector : (if σ=0 then evenRawM else oddRawM)=correctionPower σ := by
      rcases (show σ=0 ∨ σ=1 by omega) with rfl|rfl
      · exact evenRawM_exact.symm
      · exact oddRawM_exact.symm
    rw [selector]
    exact physical_row_model _ _ (first_residual_inputs hs).2.2.2
  obtain ⟨lp,lb,lpp,lbb⟩ := RationalPolyRow.log_models σ
  simp only [quadraticResidualRow,fromTrials,model_residual,model_mul,model_scale,model_multiplier,
    p,b,f,m,model_linear,model_half_drift,lp,lb,lpp,lbb,secondPoly,correctedPoly]
  norm_num

end CentralUnimodality.PolynomialTrial
