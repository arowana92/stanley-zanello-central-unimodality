module

public import CentralUnimodality.RoundedPeakCheck
public import CentralUnimodality.MidpointInduction
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! In the finite-size induction, the start of the central interval is
computable by integer square root. This connects the packed test directly
to the two staircase hypotheses. -/
@[expose] public section

namespace CentralUnimodality.EndpointDeficit

theorem finite_start {n : ℕ} (hn : n≤2048) (m : ℕ) :
    centralStart n m = (m^3).sqrt/10 := by
  rw [centralStart,ite_eq_left hn]
  have hs : Real.sqrt ((m^3:ℕ):ℝ) = m*Real.sqrt m := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    push_cast
    ring
  rw [show (0.1:ℝ)*m*Real.sqrt m = Real.sqrt ((m^3:ℕ):ℝ)/10 by rw [hs]; ring,
    Nat.floor_div_ofNat,Real.nat_floor_real_sqrt_eq_nat_sqrt]

def checkFinitePeak (w u m p : ℕ) : Bool :=
  let D := m*m/4
  let hi := D/2
  let n := hi+1
  let row := roundedLayers w n u m
  checkCorankPeak w m ((m^3).sqrt/10) p hi (combine w n m D row)

theorem finitePeak_sound {w u n δ p : ℕ} (hn : n≤2048) (hδ : δ≤1)
    (hu : u+rankReserve (2*n+δ)<2^w)
    (hl : ((2*n+δ)^3).sqrt/10≤p) (hp : p≤(2*n+δ)*(2*n+δ)/4/2)
    (hc : checkFinitePeak w u (2*n+δ) p=true) : CentralToMidpoint n δ := by
  have hdeg : (2*n+δ)*(2*n+δ)/4=n*(n+δ) := by
    rcases (show δ=0 ∨ δ=1 by omega) with rfl|rfl
    · simpa using odd_degree n
    · exact even_degree n
  rw [CentralToMidpoint,finite_start hn,← hdeg]
  exact checkCorankPeak_sound hu hl hp (Nat.lt_succ_self _) (Nat.div_le_self _ _) hc

end CentralUnimodality.EndpointDeficit
