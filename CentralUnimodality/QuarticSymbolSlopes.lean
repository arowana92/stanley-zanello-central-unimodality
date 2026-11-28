module

public import CentralUnimodality.FourierPhaseTaylor
public import CentralUnimodality.IntervalPolynomialSigns
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds

/-! Polynomial bounds for the differentiated quartic log losses. The
sign tests use small exact integer rows on 0 ≤ x² ≤ 4/3. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open PolynomialTrial Real Set

private noncomputable def cosPoly (z : ℝ) := 1-z/2+z^2/24-z^3/720+z^4/40320
private noncomputable def sincPoly (z : ℝ) := 1-z/6+z^2/120-z^3/5040+z^4/362880

private theorem bracket_signs {z : ℝ} (hz : z∈Icc (0:ℝ) (4/3)) :
    (1+z/3)*(cosPoly z+z^5/3628800)≤sincPoly z-z^5/39916800 ∧
    sincPoly z+z^5/39916800≤(1+z/3+3*z^2/10)*(cosPoly z-z^5/3628800) ∧
    cosPoly z+z^5/3628800≤(1-z/3-z^2/45)*(sincPoly z-z^5/39916800) ∧
    (1-z/3-z^2/45-3*z^3/500)*(sincPoly z+z^5/39916800)≤cosPoly z-z^5/3628800 ∧
    0≤1-z/3-z^2/45-3*z^3/500 := by
  have sound (a : List ℤ) (h : rowTest 1 0 (projectiveRows 0 4 3 a)=true) :
      0≤(realDense a).eval z := by
    simpa using projective_bound 0 4 3 1 0 a (by decide) (by decide) h (x:=z) (by simpa using hz)
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := sound [0,0,15966720,-1520640,52800,-1026,-11] (by decide)
    norm_num [realDense,densePoly,Polynomial.eval_add,Polynomial.eval_mul] at h
    dsimp only [cosPoly,sincPoly]; linarith only [h]
  · have h := sound [0,0,199584000,-164419200,14440800,-489420,8800,-99] (by decide)
    norm_num [realDense,densePoly,Polynomial.eval_add,Polynomial.eval_mul] at h
    dsimp only [cosPoly,sincPoly]; linarith only [h]
  · have h := sound [0,0,0,3801600,-253440,5730,-95,1] (by decide)
    norm_num [realDense,densePoly,Polynomial.eval_add,Polynomial.eval_mul] at h
    dsimp only [cosPoly,sincPoly]; linarith only [h]
  · have h := sound [0,0,0,697593600,-154281600,8300280,-201340,3070,27] (by decide)
    norm_num [realDense,densePoly,Polynomial.eval_add,Polynomial.eval_mul] at h
    dsimp only [cosPoly,sincPoly]; linarith only [h]
  · have h := sound [4500,-1500,-100,-27] (by decide)
    norm_num [realDense,densePoly,Polynomial.eval_add,Polynomial.eval_mul] at h
    linarith only [h]

private theorem trig_polynomials {x : ℝ} (hx : 0<x) :
    |cos x-cosPoly (x^2)|≤(x^2)^5/3628800 ∧ |sinc x-sincPoly (x^2)|≤(x^2)^5/39916800 := by
  have c := phase_remainder 0 9 x
  have s := phase_remainder 1 10 x
  rw [abs_of_pos hx] at c s
  norm_num [phaseTaylor,phaseInt,phase,Finset.sum_range_succ,Nat.factorial,cos_add_pi_div_two] at c s
  constructor
  · apply (abs_le.mpr ⟨?_,?_⟩) <;> dsimp only [cosPoly] <;> linarith only [(abs_le.mp c).1,(abs_le.mp c).2]
  · rw [sinc_of_ne_zero hx.ne',abs_le]
    constructor
    · apply le_sub_iff_add_le.mpr
      apply (le_div_iff₀ hx).mpr
      dsimp only [sincPoly]; linarith only [(abs_le.mp s).2]
    · apply sub_le_iff_le_add.mpr
      apply (div_le_iff₀ hx).mpr
      dsimp only [sincPoly]; linarith only [(abs_le.mp s).1]

theorem trig_quartic_slopes {x : ℝ} (hx : 0<x) (h : x≤9/8) :
    (1+x^2/3)*cos x≤sinc x ∧ sinc x≤(1+x^2/3+3*x^4/10)*cos x ∧
    cos x≤(1-x^2/3-x^4/45)*sinc x ∧ (1-x^2/3-x^4/45-3*x^6/500)*sinc x≤cos x := by
  let z := x^2
  have zn : 0≤z := sq_nonneg _
  have zlim : z≤4/3 := (pow_le_pow_left₀ hx.le h 2).trans (by norm_num)
  obtain ⟨a,b,c,d,e⟩ := bracket_signs ⟨zn,zlim⟩
  obtain ⟨C,S⟩ := trig_polynomials hx
  have cc := abs_le.mp C
  have ss := abs_le.mp S
  change -(z^5/3628800)≤cos x-cosPoly z ∧ _≤z^5/3628800 at cc
  change -(z^5/39916800)≤sinc x-sincPoly z ∧ _≤z^5/39916800 at ss
  have t : 0≤1-z/3-z^2/45 := by linarith only [e,pow_nonneg zn 3]
  have lo := mul_le_mul_of_nonneg_left (show cos x≤cosPoly z+z^5/3628800 by linarith only [cc.2]) (show 0≤1+z/3 by positivity)
  have hi := mul_le_mul_of_nonneg_left (show cosPoly z-z^5/3628800≤cos x by linarith only [cc.1]) (show 0≤1+z/3+3*z^2/10 by positivity)
  have sl := mul_le_mul_of_nonneg_left (show sincPoly z-z^5/39916800≤sinc x by linarith only [ss.1]) t
  have su := mul_le_mul_of_nonneg_left (show sinc x≤sincPoly z+z^5/39916800 by linarith only [ss.2]) e
  have zz : x^4=z^2 := by dsimp [z]; ring
  have zzz : x^6=z^3 := by dsimp [z]; ring
  rw [zz,zzz]
  exact ⟨lo.trans (a.trans (by linarith only [ss.1])),(show sinc x≤_ by linarith only [ss.2]).trans (b.trans hi),
    (show cos x≤_ by linarith only [cc.2]).trans (c.trans sl),su.trans (d.trans (by linarith only [cc.1]))⟩

private theorem sextic_brackets {z : ℝ} (hz : z∈Icc (0:ℝ) (81/64)) :
    (1+z/3+2*z^2/15)*(cosPoly z+z^5/3628800)≤sincPoly z-z^5/39916800 ∧
    sincPoly z+z^5/39916800≤(1+z/3+2*z^2/15+4*z^3/35)*(cosPoly z-z^5/3628800) ∧
    cosPoly z+z^5/3628800≤(1-z/3-z^2/45-2*z^3/945)*(sincPoly z-z^5/39916800) ∧
    (1-z/3-z^2/45-2*z^3/945-z^4/4000)*(sincPoly z+z^5/39916800)≤cosPoly z-z^5/3628800 ∧
    0≤1-z/3-z^2/45-2*z^3/945-z^4/4000 := by
  have sound (a : List ℤ) (h : rowTest 1 0 (projectiveRows 0 81 64 a)=true) :
      0≤(realDense a).eval z := by
    simpa using projective_bound 0 81 64 1 0 a (by decide) (by decide) h (x:=z) (by simpa using hz)
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := sound [0,0,0,32313600,-3062400,105750,-2035,-22] (by decide)
    norm_num [realDense,densePoly,Polynomial.eval_add,Polynomial.eval_mul] at h
    dsimp only [cosPoly,sincPoly]; linarith only [h]
  · have h := sound [0,0,0,252806400,-218064000,19215630,-651805,11726,-132] (by decide)
    norm_num [realDense,densePoly,Polynomial.eval_add,Polynomial.eval_mul] at h
    dsimp only [cosPoly,sincPoly]; linarith only [h]
  · have h := sound [0,0,0,0,7983360,-544950,13845,-199,2] (by decide)
    norm_num [realDense,densePoly,Polynomial.eval_add,Polynomial.eval_mul] at h
    dsimp only [cosPoly,sincPoly]; linarith only [h]
  · have h := sound [0,0,0,0,1157587200,-839563200,52296960,-1304080,22390,189] (by decide)
    norm_num [realDense,densePoly,Polynomial.eval_add,Polynomial.eval_mul] at h
    dsimp only [cosPoly,sincPoly]; linarith only [h]
  · have h := sound [756000,-252000,-16800,-1600,-189] (by decide)
    norm_num [realDense,densePoly,Polynomial.eval_add,Polynomial.eval_mul] at h
    linarith only [h]

theorem trig_sextic_slopes {x : ℝ} (hx : 0<x) (h : x≤9/8) :
    (1+x^2/3+2*x^4/15)*cos x≤sinc x ∧ sinc x≤(1+x^2/3+2*x^4/15+4*x^6/35)*cos x ∧
    cos x≤(1-x^2/3-x^4/45-2*x^6/945)*sinc x ∧
    (1-x^2/3-x^4/45-2*x^6/945-x^8/4000)*sinc x≤cos x := by
  let z := x^2
  have zn : 0≤z := sq_nonneg _
  have zlim : z≤81/64 := (pow_le_pow_left₀ hx.le h 2).trans (by norm_num)
  obtain ⟨a,b,c,d,e⟩ := sextic_brackets ⟨zn,zlim⟩
  obtain ⟨C,S⟩ := trig_polynomials hx
  have cc := abs_le.mp C
  have ss := abs_le.mp S
  change -(z^5/3628800)≤cos x-cosPoly z ∧ _≤z^5/3628800 at cc
  change -(z^5/39916800)≤sinc x-sincPoly z ∧ _≤z^5/39916800 at ss
  have t : 0≤1-z/3-z^2/45-2*z^3/945 := by linarith only [e,pow_nonneg zn 4]
  have lo := mul_le_mul_of_nonneg_left (show cos x≤cosPoly z+z^5/3628800 by linarith only [cc.2])
    (show 0≤1+z/3+2*z^2/15 by positivity)
  have hi := mul_le_mul_of_nonneg_left (show cosPoly z-z^5/3628800≤cos x by linarith only [cc.1])
    (show 0≤1+z/3+2*z^2/15+4*z^3/35 by positivity)
  have sl := mul_le_mul_of_nonneg_left (show sincPoly z-z^5/39916800≤sinc x by linarith only [ss.1]) t
  have su := mul_le_mul_of_nonneg_left (show sinc x≤sincPoly z+z^5/39916800 by linarith only [ss.2]) e
  rw [show x^4=z^2 by dsimp [z]; ring,show x^6=z^3 by dsimp [z]; ring,show x^8=z^4 by dsimp [z]; ring]
  exact ⟨lo.trans (a.trans (by linarith only [ss.1])),(show sinc x≤_ by linarith only [ss.2]).trans (b.trans hi),
    (show cos x≤_ by linarith only [cc.2]).trans (c.trans sl),su.trans (d.trans (by linarith only [cc.1]))⟩

end CentralUnimodality.ReturnSplit
