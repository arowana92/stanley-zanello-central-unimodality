module

public import CentralUnimodality.RankBinNumbers

/-! Outward rational enclosures for the prefix survival, variance and
one-sided Gaussian slope in the seven inner growth bins. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real

def lowerGrid (x : ℚ) : ℚ := (⌊(scale:ℚ)*x⌋:ℚ)/scale

theorem lowerGrid_le (x : ℚ) : lowerGrid x≤x := by
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℚ)<scale)).mpr
  simpa only [mul_comm] using Int.floor_le ((scale:ℚ)*x)

def lowerExp (x : ℚ) : ℚ := lowerGrid ((1-x/256)^256)

theorem lowerExp_le {x : ℚ} (h : x≤256) : (lowerExp x:ℝ)≤exp (-(x:ℝ)) := by
  apply ((Rat.cast_le (K:=ℝ)).mpr (lowerGrid_le _)).trans
  have hx : (x:ℝ)≤256 := by exact_mod_cast h
  have H : 1-(x:ℝ)/256≤exp (-(x:ℝ)/256) := by linarith only [add_one_le_exp (-(x:ℝ)/256)]
  have K := pow_le_pow_left₀ (by linarith only [hx] : 0≤1-(x:ℝ)/256) H 256
  rw [← exp_nat_mul] at K
  push_cast
  exact K.trans_eq (by congr 1; push_cast; ring)

def firstCut : ℚ := 3/40
def finalCut : ℚ := 37/40

def edge (i : ℕ) : ℚ :=
  let g : ℚ := (1199/100)*(3/5)
  match i with
  | 0 => g
  | 1 => g+1/16
  | 2 => g+1/4
  | 3 => g+1/2
  | 4 => g+3/4
  | 5 => g+1
  | 6 => g+3/2
  | _ => (1199/100)*(3/4)

def prefixU (g : ℚ) := g*(1-(firstCut+epsilon))/2
def prefixK : ℚ := lowerGrid ((79/100)/rootHi (firstCut+epsilon))
def survivalExponent (g : ℚ) := let U := prefixU g; U/64+U/prefixK+(firstCut+epsilon)*U^2/2

def bin (i : ℕ) : SaddleBin :=
  let g := edge i
  let G := edge (i+1)
  let f := firstCut+epsilon
  let z := rootLo ((1-(G/128)^2)*(1-f)^3/12)
  let hi := rootHi ((1-firstCut+epsilon)^3/12)
  let κ := g/2*(1-g^2*epsilon/12)
  let U := prefixU g
  let den := lowerGrid (2*U*(1-U/64)+prefixK*lowerExp (survivalExponent g))
  let V := charge ((f*G+1/κ)/(4*z^2*den))
  ⟨g,G,firstCut,z,hi,κ,den,V,lowerExp (V/2)⟩

def prefixMargin (B : SaddleBin) : ℚ := lowerGrid ((999/1000)*B.lower*B.zlo*
  ((3989/10000)*B.gaussian-5/1000)-(399/1000)*(406/1000+(293/1000)*B.variance)-7/1000)

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
