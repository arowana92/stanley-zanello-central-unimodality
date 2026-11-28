module

public import CentralUnimodality.PhysicalChebyshevRows

/-! Round the exact quadratic residual to a dyadic Chebyshev polynomial.
The uniform error grows only with the number of coefficients, even when
the powers of physical time have very large coefficients. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial Finset Set ReturnSplit

def nearestDyadic (d : ℕ+) (c : ℤ) : ℤ := (2*c*2^120+(d:ℤ))/(2*(d:ℤ))

def roundSymmetric (d : ℕ+) (a : List ℤ) : List ℤ := a.map (nearestDyadic d)

def ordinaryRow : List ℤ → List ℤ
  | [] => []
  | c::a => c::a.map (2*·)

private theorem realRow_scale (c : ℤ) (a : List ℤ) : realRow (a.map (c*·))=C (c:ℝ)*realRow a := by
  have ent (i : ℕ) : entry (a.map (c*·)) i=c*entry a i := by
    by_cases h : i<a.length
    · simp [entry,h]
    · simp [entry,List.getElem?_eq_none (le_of_not_gt h)]
  simp only [realRow,List.length_map,ent,Int.cast_mul,weightedSeries,map_mul,mul_assoc,← Finset.mul_sum]
  ring

theorem ordinary_value (a : List ℤ) (v : ℝ) :
    value (doubleHead (ordinaryRow a)) v=(realRow a).eval (1-v/128)/2^120 := by
  have eq : doubleHead (ordinaryRow a)=a.map (2*·) := by cases a <;> rfl
  rw [eq,value,realRow_scale,eval_mul,eval_C]
  norm_num
  ring

private theorem rounded_entry (d : ℕ+) (a : List ℤ) (i : ℕ) :
    |(entry a i:ℝ)/(d:ℝ)-(entry (roundSymmetric d a) i:ℝ)/2^120|≤1/2^120 := by
  by_cases h : i<a.length
  case neg => simp [entry,roundSymmetric,List.getElem?_eq_none (le_of_not_gt h)]
  have eq : entry (roundSymmetric d a) i=nearestDyadic d (entry a i) := by
    simp [entry,roundSymmetric,h]
  rw [eq]
  let z := 2*entry a i*2^120+(d:ℤ)
  let den := 2*(d:ℤ)
  have dp : 0<den := by dsimp [den]; positivity
  have dr : (0:ℝ)<(d:ℝ) := by exact_mod_cast d.pos
  have ident : (↑(z%den):ℝ)+2*(d:ℝ)*(↑(z/den):ℝ)=2*(entry a i:ℝ)*2^120+d := by
    exact_mod_cast Int.emod_add_mul_ediv z den
  have lo : 0≤(↑(z%den):ℝ) := by exact_mod_cast Int.emod_nonneg z dp.ne'
  have hi : (↑(z%den):ℝ)<2*(d:ℝ) := by exact_mod_cast Int.emod_lt_of_pos z dp
  change |(entry a i:ℝ)/d-(↑(z/den):ℝ)/2^120|≤_
  rw [abs_le]
  constructor <;> field_simp <;> linarith only [ident,lo,hi,dr]

theorem symmetric_round_bound (a : List ℤ) (d : ℕ+) {v : ℝ} (hv : v∈Icc (0:ℝ) 256) :
    |(realRow a).eval (1-v/128)/d-value (doubleHead (ordinaryRow (roundSymmetric d a))) v|≤
      (2*(a.length:ℝ)+1)/2^120 := by
  let b := roundSymmetric d a
  let e := fun i => (1/(d:ℝ))*(entry a i:ℝ)+(-1/2^120)*(entry b i:ℝ)
  have err (i : ℕ) : |e i|≤1/2^120 := by
    have eq : e i=(entry a i:ℝ)/d-(entry b i:ℝ)/2^120 := by dsimp only [e]; ring
    rw [eq]; exact rounded_entry d a i
  have hx : |1-v/128|≤1 := abs_le.mpr ⟨by linarith only [hv.2],by linarith only [hv.1]⟩
  have bound := weightedSeries_bound a.length e hx
  have count := sum_le_sum (s:=range a.length) (fun i _ => err i)
  simp only [sum_const,card_range,nsmul_eq_mul] at count
  have len : b.length=a.length := by simp [b,roundSymmetric]
  have series : weightedSeries a.length e=C (1/(d:ℝ))*realRow a+C (-1/2^120:ℝ)*realRow b := by
    rw [show realRow b=weightedSeries a.length (fun i => (entry b i:ℝ)) by simp only [realRow,len]]
    exact weightedSeries_linear ..
  rw [series,eval_add,eval_mul,eval_mul,eval_C,eval_C] at bound
  rw [ordinary_value]
  change |(realRow a).eval (1-v/128)/d-(realRow b).eval (1-v/128)/2^120|≤_
  rw [show (realRow a).eval (1-v/128)/d-(realRow b).eval (1-v/128)/2^120=
    1/(d:ℝ)*(realRow a).eval (1-v/128)+(-1/2^120)*(realRow b).eval (1-v/128) by ring]
  linarith only [bound,count,err 0]

/-- Remove only trailing zero coefficients, preserving every Chebyshev index. -/
def trimCheb : List ℤ → List ℤ
  | [] => []
  | c::a =>
    match trimCheb a with
    | [] => if c=0 then [] else [c]
    | e::b => c::e::b

private theorem trim_polynomial (a : List ℤ) (j : ℕ) :
    integerChebyshev (trimCheb a) j=integerChebyshev a j := by
  induction a generalizing j with
  | nil => rfl
  | cons c a ih =>
    rw [integerChebyshev,← ih (j+1),trimCheb]
    cases h : trimCheb a with
    | nil => by_cases hc : c=0 <;> simp [hc,integerChebyshev]
    | cons e b => rfl

theorem ordinary_eval (a : List ℤ) (v : ℝ) :
    value (doubleHead a) v=((integerChebyshev a 0).map (Int.castRingHom ℝ)).eval (v/256)/2^120 := by
  let b := (coefficientMass a*7^a.length).log2+1
  have small : (coefficientMass a:ℤ)*7^a.length<2^b := by
    exact_mod_cast (Nat.lt_log2_self (n:=coefficientMass a*7^a.length))
  rw [normalized_input b a small,realDense,unpackCheb_poly b a small]

theorem trim_value (a : List ℤ) (v : ℝ) :
    value (doubleHead (trimCheb a)) v=value (doubleHead a) v := by
  rw [ordinary_eval,ordinary_eval,trim_polynomial]

private theorem append_integer_series (a b : List ℤ) (j : ℕ) :
    integerChebyshev (a++b) j=integerChebyshev a j+integerChebyshev b (j+a.length) := by
  induction a generalizing j with
  | nil => simp [integerChebyshev]
  | cons c a ih => simp [integerChebyshev,ih,show j+1+a.length=j+(a.length+1) by omega,add_assoc]

private theorem absolute_integer_series (a : List ℤ) (j : ℕ) {z : ℝ} (hz : |1-2*z|≤1) :
    |((integerChebyshev a j).map (Int.castRingHom ℝ)).eval z|≤(coefficientMass a:ℝ) := by
  induction a generalizing j with
  | nil => simp [integerChebyshev,coefficientMass]
  | cons c a ih =>
    simp only [integerChebyshev,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,shiftedT,
      Polynomial.map_comp,Chebyshev.map_T,Polynomial.map_sub,Polynomial.map_one,Polynomial.map_ofNat,
      map_X,eval_add,eval_mul,eval_C,eval_comp,eval_sub,eval_one,eval_ofNat,eval_X,Int.coe_castRingHom]
    apply (abs_add_le ..).trans
    rw [abs_mul]
    have term := mul_le_mul_of_nonneg_left (Chebyshev.abs_eval_T_real_le_one (j:ℤ) hz) (abs_nonneg (c:ℝ))
    simpa [coefficientMass,mul_one] using add_le_add term (ih (j+1))

theorem take_cheb_value (a : List ℤ) (k : ℕ) {v : ℝ} (hv : v∈Icc (0:ℝ) 256) :
    |value (doubleHead a) v-value (doubleHead (a.take k)) v|≤(coefficientMass (a.drop k):ℝ)/2^120 := by
  rw [ordinary_eval,ordinary_eval,← sub_div,abs_div,abs_of_pos (by positivity : 0<(2:ℝ)^120)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have parts := append_integer_series (a.take k) (a.drop k) 0
  rw [List.take_append_drop] at parts
  rw [parts,Polynomial.map_add,eval_add,add_sub_cancel_left]
  apply absolute_integer_series
  rw [abs_le]
  constructor <;> linarith only [hv.1,hv.2]

def quadraticChebRow (σ : ℕ) :=
  let p := quadraticResidualRow σ
  trimCheb (ordinaryRow (roundSymmetric p.denom (physicalCheb p.numer)))

theorem quadratic_cheb_row_sound {σ : ℕ} (hs : σ≤1) {v : ℝ} (hv : v∈Icc (0:ℝ) 256) :
    |(secondPoly σ).eval v-value (doubleHead (quadraticChebRow σ)) v|≤
      (2*((quadraticResidualRow σ).numer.length:ℝ)+1)/2^120 := by
  let p := quadraticResidualRow σ
  have bound := symmetric_round_bound (physicalCheb p.numer) p.denom hv
  rw [physical_cheb_eval,physicalCheb_length] at bound
  rw [← quadratic_residual_row_model hs,RationalPolyRow.model,eval_mul,eval_C]
  change |1/(p.denom:ℝ)*(realDense p.numer).eval v-value _ v|≤_
  simpa only [div_eq_inv_mul,mul_one,quadraticChebRow,trim_value,p] using bound

end CentralUnimodality.PolynomialTrial
