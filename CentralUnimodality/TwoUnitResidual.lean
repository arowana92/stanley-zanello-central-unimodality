module

public import CentralUnimodality.QuadraticDyadicInputs
public import CentralUnimodality.QuadraticRowLengths

/-! A signed residual prefix is bounded on four adjacent half-unit bins by
one Taylor shift. At the group's center the shifted variable has radius four. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit Set Polynomial

def radiusMass (w : ℕ) : List ℤ → ℕ
  | [] => 0
  | x::a => x.natAbs+w*radiusMass w a

private theorem radius_bound (a : List ℤ) (w : ℕ) {t : ℝ} (ht : |t|≤w) :
    |(realDense a).eval t|≤radiusMass w a := by
  induction a with
  | nil => simp [realDense,densePoly,radiusMass]
  | cons x a ih =>
    have e : (realDense (x::a)).eval t=(x:ℝ)+t*(realDense a).eval t := by simp [realDense,densePoly]
    rw [e]
    apply (abs_add_le ..).trans
    rw [abs_mul]
    simpa [radiusMass] using add_le_add_left (mul_le_mul ht ih (abs_nonneg _) (by positivity)) |(x:ℝ)|

def twoUnitNum (a : List ℤ) (g : ℕ) :=
  ceilQuotient (10^30*radiusMass 4 (packedAffineRow 5376 (8*g+4) a)) (jetDen a)

theorem two_unit_bound (a : List ℤ) (cap : coefficientMass a*1024^a.length<2^5376)
    {i : ℕ} (hi : i<228) {v : ℝ} (hv : v∈halfInterval i) :
    |(realDense a).eval (v/256)/2^120|≤(twoUnitNum a (i/4):ℝ)/10^30 := by
  let g := i/4
  let l : ℤ := 8*(g:ℤ)+4
  have lnat : l=((8*g+4:ℕ):ℤ) := by simp [l]
  have gl : 4*g≤ i := by dsimp [g]; omega
  have gh : i+1≤4*g+4 := by dsimp [g]; omega
  have hl : l.natAbs+1≤1024 := by rw [lnat,Int.natAbs_natCast]; omega
  have gl' : 4*(g:ℝ)≤ i := by exact_mod_cast gl
  have gh' : (i:ℝ)+1≤4*g+4 := by exact_mod_cast gh
  have left := hv.1
  have right := hv.2
  change (i:ℝ)/2≤v at left
  change v≤((i+1:ℕ):ℝ)/2 at right
  push_cast at right
  have rad : |4*v-l|≤(4:ℕ) := by
    dsimp only [l]; push_cast; rw [abs_le]; constructor <;> linarith only [left,right,gl',gh']
  let a' := packedAffineRow 5376 l a
  have b := radius_bound a' 4 rad
  have e : (realDense a').eval (4*v-l)=1024^a.length*(realDense a).eval (v/256) := by
    rw [show a'=affineRow l a from packedAffineRow_exact 5376 l hl a cap,affine_real]
    congr 2
    ring
  rw [e,abs_mul,abs_of_pos (by positivity : (0:ℝ)<1024^a.length)] at b
  let n := twoUnitNum a g
  have den : 0<jetDen a := by unfold jetDen; positivity
  have up : 10^30*radiusMass 4 a'≤n*jetDen a := by
    change 10^30*radiusMass 4 a'≤ceilQuotient (10^30*radiusMass 4 a') (jetDen a)*jetDen a
    have rem := Nat.mod_lt (10^30*radiusMass 4 a'+jetDen a-1) den
    have eq := Nat.mod_add_div (10^30*radiusMass 4 a'+jetDen a-1) (jetDen a)
    unfold ceilQuotient
    rw [Nat.mul_comm (jetDen a) ((10^30*radiusMass 4 a'+jetDen a-1)/jetDen a)] at eq
    omega
  have up' : (10:ℝ)^30*radiusMass 4 a'≤n*(1024^a.length*2^120) := by exact_mod_cast up
  rw [abs_div,abs_of_pos (by positivity : (0:ℝ)<2^120),div_le_div_iff₀ (by positivity) (by positivity)]
  change _≤(n:ℝ)*2^120
  apply le_of_mul_le_mul_left (a:=(1024:ℝ)^a.length) _ (by positivity)
  linarith only [mul_le_mul_of_nonneg_left b (by positivity : (0:ℝ)≤10^30),up']

theorem quadratic_residual_from_prefix {σ i : ℕ} (hs : σ≤1) (hi : i<228)
    (eq : quadraticChebRow σ=dyadicQuadratic σ) {v : ℝ} (hv : v∈halfInterval i) :
    |secondCurveResidual (value candidate) (correctedValue σ) σ v|≤
      (twoUnitNum (powerQuadratic σ) (i/4):ℝ)/10^30+303/10^9 := by
  have v0 : 0≤v := (show (0:ℝ) ≤ (i:ℝ)/2 by positivity).trans hv.1
  have vmax : v≤144 := by
    have j : ((i+1:ℕ):ℝ)≤228 := by exact_mod_cast (by omega : i+1≤228)
    linarith only [hv.2,j]
  have range : v∈Icc (0:ℝ) 256 := ⟨v0,by linarith only [vmax]⟩
  obtain ⟨_,mass,small,cap⟩ := quadratic_prefix_bounds σ
  have mass' : (coefficientMass ((dyadicQuadratic σ).drop 256):ℝ)*10^9≤2*2^120 := by exact_mod_cast mass.le
  have gauss := second_residual_transfer hs (show v∈Icc (0:ℝ) 144 from ⟨v0,vmax⟩)
  have rounding := quadratic_cheb_row_sound hs range
  rw [quadratic_residual_length hs,eq] at rounding
  have tail := take_cheb_value (dyadicQuadratic σ) 256 range
  have cell := two_unit_bound (powerQuadratic σ) cap hi hv
  rw [normalized_input 1024 _ small,prefix_quadratic_power] at tail
  rw [abs_le] at gauss rounding tail cell ⊢
  constructor <;> linarith only [gauss.1,gauss.2,rounding.1,rounding.2,tail.1,tail.2,cell.1,cell.2,mass']

end CentralUnimodality.PolynomialTrial
