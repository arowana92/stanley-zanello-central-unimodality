module

public import CentralUnimodality.CorrectedLatticeSymbols
import CentralUnimodality.ScaledPrefixSurvival

/-! Transfer a signed quadratic logarithmic expansion to the lattice symbol.
A one-sided cubic log remainder gives a two-sided cubic amplitude remainder. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Real Set

private theorem exp_negative_cubic {x : ℝ} (hx : 0≤x) :
    1-x+x^2/2-x^3/6≤exp (-x) := by
  let f := fun t : ℝ => exp (-t)-(1-t+t^2/2-t^3/6)
  have df (t : ℝ) : HasDerivAt f (1-t+t^2/2-exp (-t)) t := by
    unfold f
    convert (((hasDerivAt_id t).neg.exp).sub (((((hasDerivAt_const t (1:ℝ)).sub
      (hasDerivAt_id t)).add ((hasDerivAt_pow 2 t).div_const 2)).sub ((hasDerivAt_pow 3 t).div_const 6)))) using 1
    · rfl
    · norm_num; ring
  have h := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
    (f:=f) (f':=fun t => 1-t+t^2/2-exp (-t)) (by dsimp only [f]; fun_prop)
    (fun t _ => (df t).hasDerivWithinAt)
    (fun t ht => sub_nonneg.mpr (MarkedExcursion.negative_exp_quadratic (interior_subset ht)))
  have v := h (show (0:ℝ)∈Ici 0 from le_rfl) hx hx
  simpa [f] using v

private theorem exponential_quadratic_noise {t s d : ℝ} (ht : 0≤t) (hs : 0≤s) (hd : 0≤d) :
    |exp (-t-s-d)-(1-t+t^2/2-s)|≤d+t^3/6+t*s+s^2/2 := by
  have et : exp (-t)≤1 := (exp_le_one_iff).mpr (neg_nonpos.mpr ht)
  have lt : 1-t≤exp (-t) := by linarith only [add_one_le_exp (-t)]
  have ls : 1-(s+d)≤exp (-(s+d)) := by linarith only [add_one_le_exp (-(s+d))]
  have lo : 1-t+t^2/2-t^3/6-s-d≤exp (-t-s-d) := by
    rw [show -t-s-d= -t+(-(s+d)) by ring,exp_add]
    have p := mul_le_mul_of_nonneg_left ls (exp_pos (-t)).le
    have m := mul_le_mul_of_nonneg_right et (add_nonneg hs hd)
    linarith only [exp_negative_cubic ht,p,m]
  have hi : exp (-t-s-d)≤1-t+t^2/2-s+t*s+s^2/2 := by
    apply (exp_le_exp.mpr (show -t-s-d≤ -t+(-s) by linarith only [hd])).trans
    rw [exp_add]
    have p := mul_le_mul_of_nonneg_left (MarkedExcursion.negative_exp_quadratic hs) (exp_pos (-t)).le
    have m := mul_le_mul_of_nonneg_right lt hs
    have q := mul_le_mul_of_nonneg_right et (sq_nonneg s)
    linarith only [MarkedExcursion.negative_exp_quadratic ht,p,m,q]
  rw [abs_le]
  constructor <;> linarith only [lo,hi,hd,pow_nonneg ht 3,mul_nonneg ht hs,sq_nonneg s]

theorem exponential_transfer_second {L a t A B C : ℝ} (ht : 0≤t) (hA : 0≤A) (hB : 0≤B)
    (lo : 0≤ -L-a-t*A-t^2*B) (hi : -L-a-t*A-t^2*B≤t^3*C) :
    |exp L-exp (-a)*(1-t*A+t^2*(A^2/2-B))|≤
      t^3*exp (-a)*(C+A^3/6+A*B+t*B^2/2) := by
  let d := -L-a-t*A-t^2*B
  have H := exponential_quadratic_noise (d:=d) (mul_nonneg ht hA) (mul_nonneg (sq_nonneg t) hB) lo
  have eq : L= -a+(-(t*A)-t^2*B-d) := by dsimp only [d]; ring
  rw [eq,exp_add,← mul_sub,abs_mul,abs_of_pos (exp_pos _)]
  rw [show 1-t*A+t^2*(A^2/2-B)=1-t*A+(t*A)^2/2-t^2*B by ring]
  apply (mul_le_mul_of_nonneg_left H (exp_pos _).le).trans
  change d≤t^3*C at hi
  have K := mul_le_mul_of_nonneg_left hi (exp_pos (-a)).le
  linarith only [K]

end CentralUnimodality.ReturnSplit
