module

public import CentralUnimodality.ExactMoments

/-! Average a corank monomial over the unit cell centered at its shifted
corank. Taking the difference of the two endpoint primitives makes the
highest raw moment cancel, so a degree-r test needs only r raw moments. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

private theorem ratioSum_eq (n : ℕ) (p : Laurent) :
    ratioSum n p = coeff n (eval p) / (n.centralBinom:ℚ) := by
  apply (eq_div_iff (by exact_mod_cast Nat.centralBinom_ne_zero n)).mpr
  rw [coeff_eval,mul_comm]

theorem ratioSum_scale (n : ℕ) (c : ℚ) (p : Laurent) :
    ratioSum n (scaleShift c 0 p) = c*ratioSum n p := by
  simp only [ratioSum_eq,eval_scaleShift,rootPower_zero,mul_one,coeff_C_mul]
  ring

theorem ratioSum_add (n : ℕ) (p q : Laurent) :
    ratioSum n (add p q) = ratioSum n p + ratioSum n q := by
  simp only [ratioSum_eq,eval_add,map_add,add_div]

theorem ratioSum_sumRange (n : ℕ) (p : ℕ → Laurent) (r : ℕ) :
    ratioSum n (sumRange p r) = ∑ j ∈ Finset.range r, ratioSum n (p j) := by
  induction r with
  | zero => simp [sumRange,ratioSum]
  | succ r ih => rw [sumRange,ratioSum_add,ih,Finset.sum_range_succ]

/-- Multiplication by (3N/2+b)^k at size N. -/
def translate (b : ℚ) (p : Laurent) : ℕ → Laurent
  | 0 => p
  | k+1 =>
    let q := translate b p k
    add (scaleShift (3/2) 0 (euler q)) (scaleShift b 0 q)

theorem ratioSum_translate (n : ℕ) (b : ℚ) (p : Laurent) (k : ℕ) :
    ratioSum n (translate b p k) = (3*(n:ℚ)/2+b)^k * ratioSum n p := by
  induction k with
  | zero => simp [translate]
  | succ k ih =>
    have he (q : Laurent) : ratioSum n (euler q) = n*ratioSum n q := by
      simp only [ratioSum_eq,eval_euler,coeff_sizeEuler]
      ring
    rw [translate,ratioSum_add,ratioSum_scale,ratioSum_scale,he,ih,pow_succ]
    ring

def rawNumerator (A B : ℕ → Laurent) (δ r : ℕ) : Laurent :=
  scaleShift r.factorial 0
    (if δ = 0 then evenNumerator (B r) else oddNumerator (oddRhs A B r))

def massFactor (n δ : ℕ) : ℚ := ((n+δ).centralBinom:ℚ)/((δ:ℚ)+1)

theorem rawNumerator_exact (m n δ j : ℕ) (hδ : δ ≤ 1) (hj : j ≤ m) :
    (rankMoment n δ j : ℚ) = massFactor n δ *
      ratioSum (n+δ) (rawNumerator (lookup (tables m).1) (lookup (tables m).2) δ j) := by
  rcases (by omega : δ = 0 ∨ δ = 1) with rfl|rfl
  · have h := extracted_even (tables_exact m).2.1 n j hj
    simp only [rawNumerator,ite_true,ratioSum_scale,massFactor,Nat.add_zero,Nat.cast_zero,zero_add,div_one]
    rw [h]
    ring
  · have h := extracted_odd (tables_exact m).2.2 n j hj
    simp only [rawNumerator,one_ne_zero,ite_false,ratioSum_scale,massFactor,Nat.cast_one]
    linarith only [h]

/-- At fixed N the endpoints are K+3N/2+b and K+3N/2+b+1. -/
def cellNumerator (b : ℚ) (P : ℕ → Laurent) (r : ℕ) : Laurent :=
  scaleShift (1/((r:ℚ)+1)) 0 (sumRange (fun j =>
    scaleShift ((r+1).choose j) 0 (add (translate (b+1) (P j) (r+1-j))
      (scaleShift (-1) 0 (translate b (P j) (r+1-j)))) ) (r+1))

def cellPower {R : Type*} [Field R] (x : R) (r : ℕ) : R :=
  ((x+1)^(r+1)-x^(r+1))/((r:R)+1)

private theorem endpoint_difference (x a b : ℚ) (r : ℕ) :
    (x+a)^(r+1)-(x+b)^(r+1) =
      ∑ j ∈ Finset.range (r+1), ((r+1).choose j:ℚ)*x^j*(a^(r+1-j)-b^(r+1-j)) := by
  rw [add_pow,add_pow,← Finset.sum_sub_distrib,Finset.sum_range_succ]
  simp only [Nat.sub_self,pow_zero,mul_one,sub_self,add_zero]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem cellNumerator_exact {n δ r : ℕ} {P : ℕ → Laurent}
    (h : ∀ j ≤ r, (rankMoment n δ j : ℚ) = massFactor n δ * ratioSum (n+δ) (P j))
    (b : ℚ) :
    massFactor n δ * ratioSum (n+δ) (cellNumerator b P r) =
      ∑ i ∈ Finset.range (n*(n+δ)+1), (rankCount (2*n+δ) i:ℚ) *
        cellPower (((n*(n+δ)-i:ℕ):ℚ)+(3*((n+δ:ℕ):ℚ)/2+b)) r := by
  let f (j : ℕ) := ((r+1).choose j:ℚ) *
    ((3*((n+δ:ℕ):ℚ)/2+(b+1))^(r+1-j) - (3*((n+δ:ℕ):ℚ)/2+b)^(r+1-j))
  have hh : ratioSum (n+δ) (cellNumerator b P r) =
      (1/((r:ℚ)+1))* ∑ j ∈ Finset.range (r+1), f j * ratioSum (n+δ) (P j) := by
    simp only [cellNumerator,ratioSum_scale,ratioSum_sumRange,ratioSum_add,ratioSum_translate]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    ring
  rw [hh]
  have hcell (x : ℚ) :
      cellPower (x+(3*((n+δ:ℕ):ℚ)/2+b)) r =
      (∑ j ∈ Finset.range (r+1), f j*x^j)/((r:ℚ)+1) := by
    unfold cellPower
    rw [show x+(3*((n+δ:ℕ):ℚ)/2+b)+1 = x+(3*((n+δ:ℕ):ℚ)/2+(b+1)) by ring,
      endpoint_difference]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    ring
  simp_rw [hcell]
  simp only [div_eq_mul_inv,one_mul,Finset.sum_mul,Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := h j (by simpa using (Finset.mem_range.mp hj))
  simp only [rankMoment,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow] at hm
  calc
    _ = (f j*((r:ℚ)+1)⁻¹)*(massFactor n δ*ratioSum (n+δ) (P j)) := by ring
    _ = _ := by
      rw [← hm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end CentralUnimodality.Laurent
