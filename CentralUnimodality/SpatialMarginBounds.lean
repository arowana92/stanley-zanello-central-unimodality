module

public import CentralUnimodality.PackedIntervalSigns
public import CentralUnimodality.PackedBaseResidual
public import CentralUnimodality.IntegratedTaylorRow

/-! Convert a packed certificate to a margin for the actual Taylor
integral on every point of a closed spatial interval. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

def spatialCapacity (r : ℕ) : Prop :=
  coefficientMass (integratedRow r 1024 trialPower)≤2^16500 ∧ integralDen r 1024 trialPower≤2^16000

instance (r : ℕ) : Decidable (spatialCapacity r) := by unfold spatialCapacity; infer_instance

private theorem room : (8*2^16500+256*2^16000)*20000^1025<2^32768 := by decide +kernel

set_option maxRecDepth 15000 in
set_option exponentiation.threshold 50000 in
theorem spatial_margin (r : ℕ) (l h m k : ℤ) (hl : l<h) (size : l.natAbs+h.natAbs≤20000)
    (hm : m.natAbs≤8) (hk : k.natAbs≤256) (cap : spatialCapacity r)
    (test : packedDigitsTest 32768 1026 m (k*integralDen r 1024 trialPower)
      (homogeneousPack 32769 l h 10000 (integratedRow r 1024 trialPower))=true)
    {x : ℝ} (hx : x∈Set.Icc ((l:ℝ)/10000) ((h:ℝ)/10000)) : (k:ℝ)≤m*integratedTaylor r 1024 trialPower x := by
  let a := integratedRow r 1024 trialPower
  let d := integralDen r 1024 trialPower
  have len : a.length=1025 := by simp [a,integratedRow]
  have bound : rowTest m (k*(d:ℤ)) (projectiveRows l h 10000 a)=true := by
    apply rowTest_of_packed (B:=20000) size (by decide) (n:=1026) (by change a.length+1≤1026; rw [len]) _ test
    rw [Int.natAbs_mul,Int.natAbs_natCast,len]
    apply (Nat.mul_le_mul_right _ (Nat.add_le_add (Nat.mul_le_mul hm cap.1) (Nat.mul_le_mul hk cap.2))).trans_lt
    exact room
  have H := projective_bound l h 10000 m (k*(d:ℤ)) a hl (by decide) bound hx
  change ((k*(d:ℤ):ℤ):ℝ)≤(m:ℝ)*(realDense (integratedRow r 1024 trialPower)).eval x at H
  rw [integratedTaylor_exact] at H
  push_cast at H
  have pos : 0<(d:ℝ) := by exact_mod_cast integralDen_pos r 1024 trialPower
  apply le_of_mul_le_mul_left (a:=(d:ℝ)) _ pos
  change (d:ℝ)*k≤d*(m*integratedTaylor r 1024 trialPower x)
  dsimp only [d] at *; linarith only [H]

end CentralUnimodality.PolynomialTrial
