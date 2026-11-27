module

public import CentralUnimodality.WitnessEvaluation

/-! Relate the computed reciprocal-size polynomials to the actual moments
of the scaled staircase cells, including their common irrational scalar. -/
@[expose] public section

namespace CentralUnimodality.Witness

open Laurent

def rawCell (n δ r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n*(n+δ)+1), (rankCount (2*n+δ) i:ℚ) *
    cellPower (((n*(n+δ)-i:ℕ):ℚ)+(3*((n+δ:ℕ):ℚ)/2+(-(δ:ℚ)/2))) r

noncomputable def cellScale (N : ℕ) : ℝ := (2*N)*Real.sqrt (2*N)

noncomputable def normalizedCell (n δ r : ℕ) : ℝ :=
  (rawCell n δ r:ℝ) / ((massFactor n δ:ℝ)*(cellScale (n+δ))^r)

theorem massFactor_pos (n δ : ℕ) : 0 < massFactor n δ := by
  unfold massFactor
  have h := Nat.centralBinom_pos (n+δ)
  positivity

theorem cellScale_pos {N : ℕ} (hN : 0 < N) : 0 < cellScale N := by
  unfold cellScale
  positivity

private theorem scale_even (N k : ℕ) :
    cellScale N^(2*k) = (2*(N:ℝ))^(3*k) := by
  rw [cellScale,pow_mul,pow_mul,mul_pow,Real.sq_sqrt (by positivity)]
  ring

private theorem scale_odd (N k : ℕ) :
    cellScale N^(2*k+1) = (2*(N:ℝ))^(3*k+1)*Real.sqrt (2*N) := by
  rw [pow_succ,scale_even,pow_succ,cellScale]
  ring

private theorem root_two_wallis {N : ℕ} (hN : 0 < N) :
    ((rootRatio (-2) N:ℚ):ℝ) / Real.sqrt (2*N) = wallisFactor N := by
  have hq := rootRatio_neg_two N
  have h : (N.centralBinom:ℝ)*(rootRatio (-2) N:ℚ) = 4^N := by exact_mod_cast hq
  have hc : (N.centralBinom:ℝ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero N
  have hs : Real.sqrt (2*(N:ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [wallisFactor,survival]
  field_simp
  linear_combination h

theorem horner_rat_real (x : ℚ) (p : List ℚ) : ((horner x p:ℚ):ℝ) = horner (x:ℝ) p := by
  induction p with
  | nil => simp [horner]
  | cons c p ih => simp [horner,ih]

private theorem normalized_factor (N r : ℕ) (hN : 0 < N) :
    (rootRatio (-((1+r%2:ℕ):ℤ)) N:ℝ) * (N:ℝ)^(3*r/2) / (cellScale N)^r =
      (if r%2 = 0 then 1 else wallisFactor N) / (2:ℝ)^(3*r/2) := by
  have hn : (N:ℝ) ≠ 0 := by positivity
  let k := r/2
  rcases (by omega : r = 2*k ∨ r = 2*k+1) with he | ho
  · have hd : 3*r/2 = 3*k := by omega
    have hpar : r%2 = 0 := by omega
    rw [hd,ite_eq_left hpar,hpar]
    norm_num only [Nat.add_zero,Nat.cast_one]
    rw [rootRatio_neg_one, Rat.cast_one,one_mul,he,scale_even,mul_pow]
    field_simp
  · have hd : 3*r/2 = 3*k+1 := by omega
    have hpar : r%2 = 1 := by omega
    rw [hd,hpar]
    norm_num only [Nat.reduceAdd,Nat.cast_ofNat,reduceCtorEq,ite_false]
    rw [ho,scale_odd,mul_pow,← root_two_wallis hN]
    have hs : Real.sqrt (2*(N:ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp

def polynomialFromCell (T : Laurent) (r : ℕ) : Option (List ℚ) := do
  let v ← extractPolynomial (1+r%2) (3*r/2) T
  return v.map ((1/(2:ℚ)^(3*r/2))*·)

theorem normalizedCell_from_numerator {n δ r : ℕ} (hn : 0 < n+δ) (T : Laurent)
    (hh : rawCell n δ r = massFactor n δ*ratioSum (n+δ) T)
    {q : List ℚ} (hq : polynomialFromCell T r = some q) :
    normalizedCell n δ r = (if r%2 = 0 then 1 else wallisFactor (n+δ)) *
      horner ((n+δ:ℕ):ℝ)⁻¹ q := by
  change (do let v ← extractPolynomial (1+r%2) (3*r/2) T; pure (v.map ((1/(2:ℚ)^(3*r/2))*·))) = some q at hq
  cases ht : extractPolynomial (1+r%2) (3*r/2) T with
  | none => rw [ht] at hq; cases hq
  | some v =>
    obtain rfl : v.map ((1/(2:ℚ)^(3*r/2))*·) = q := by
      rw [ht] at hq
      exact Option.some.inj hq
    have he := extractPolynomial_exact (by omega : 0 < 1+r%2) hn T ht
    rw [he] at hh
    have hr := congrArg (fun a : ℚ => (a:ℝ)) hh
    simp only [Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,horner_rat_real,Rat.cast_inv] at hr
    rw [normalizedCell,hr,horner_scale]
    simp only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one]
    have hm : (massFactor n δ:ℝ) ≠ 0 := by exact_mod_cast (massFactor_pos n δ).ne'
    have hf := normalized_factor (n+δ) r hn
    generalize horner ((n+δ:ℕ):ℝ)⁻¹ v = y
    field_simp at hf ⊢
    linear_combination y * hf

theorem normalizedCell_exact {n δ r : ℕ} (hn : 0 < n+δ) {P : ℕ → Laurent}
    (h : ∀ j ≤ r, (rankMoment n δ j:ℚ) = massFactor n δ * ratioSum (n+δ) (P j))
    {q : List ℚ} (hq : momentPolynomial P δ r = some q) :
    normalizedCell n δ r = (if r%2 = 0 then 1 else wallisFactor (n+δ)) *
      horner ((n+δ:ℕ):ℝ)⁻¹ q :=
  normalizedCell_from_numerator hn _ (cellNumerator_exact h _).symm hq

end CentralUnimodality.Witness
