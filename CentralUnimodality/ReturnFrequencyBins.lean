module

public import CentralUnimodality.FirstReturnInnerArc
public import CentralUnimodality.CorrectedTimeBins

/-! A rational discount for the first-return Fourier symbol. The difference
between the full time bin and the remaining time bin gives a lower bound
on the elapsed time in the excursion. Each ten complete half-unit bins
provide another factor of two. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real

def returnDiscount (i k : ℕ) : ℚ := min 1 (125/(2:ℚ)^((i-(k+1))/10))

theorem discount_bounds (i k : ℕ) : 0≤returnDiscount i k ∧ returnDiscount i k≤1 :=
  ⟨le_min (by norm_num) (by positivity),min_le_left ..⟩

@[simp] theorem discount_self (i : ℕ) : returnDiscount i i=1 := by
  simp [returnDiscount]

private theorem small_j_bound {z : ℝ} (hz : 0≤z) (hZ : z≤0.1) {j : ℕ} (hj : j≤40) :
    1≤125*exp (-(0.30*(j:ℝ)*z^2)) := by
  have jr : (j:ℝ)≤40 := by exact_mod_cast hj
  have bound := mul_le_mul jr (pow_le_pow_left₀ hz hZ 2) (sq_nonneg z) (by norm_num : (0:ℝ)≤40)
  linarith only [Real.add_one_le_exp (-(0.30*(j:ℝ)*z^2)),bound]

private theorem one_half_step : exp (-(3/4)) ≤ 1/2 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤3/4) 3
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rw [Real.exp_neg,inv_eq_one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  linarith only [h]

private theorem return_symbol_discount_of_nonneg {N i j : ℕ} (n0 : 0<N) (jl : j≤N)
    {ω u : ℝ} (w0 : 0≤ω) (hu : u∈halfInterval i)
    (step : u/N≤0.02) (phase : ω^2=(u/N)^3/32) :
    let k := cappedBin i (((N-j:ℕ):ℝ)*(u/N))
    ‖returnSymbol ω j‖ ≤ returnMass j*(returnDiscount i k:ℝ) := by
  let k := cappedBin i (((N-j:ℕ):ℝ)*(u/N))
  let z := sqrt ((u/N)/2)
  have lo : (i:ℝ)/2≤u := hu.1
  have u0 : 0≤u := (by positivity : 0≤(i:ℝ)/2).trans lo
  have np : (0:ℝ)<N := by exact_mod_cast n0
  have z0 : 0≤z := sqrt_nonneg _
  have z2 : z^2=(u/N)/2 := sq_sqrt (by positivity)
  have zmax : z≤0.1 := by
    apply (sq_le_sq₀ z0 (by norm_num : (0:ℝ)≤0.1)).mp
    linarith only [z2,step]
  have m0 := (norm_nonneg (returnSymbol ω j)).trans (norm_returnSymbol_le ω j)
  have mass := norm_returnSymbol_le ω j
  have hw : z^3/2=ω := by
    apply (sq_eq_sq₀ (by positivity) w0).mp
    rw [phase,show (z^3/2)^2=(z^2)^3/4 by ring,z2]; ring
  have full : ‖returnSymbol ω j‖≤returnMass j*(125*exp (-(0.30*(j:ℝ)*z^2))) := by
    by_cases pos : 0<z
    · by_cases large : 41≤j
      · simpa only [hw] using returnSymbol_inner_001 pos zmax large
      · exact mass.trans (le_mul_of_one_le_right m0 (small_j_bound z0 zmax (by omega)))
    · have e : z=0 := le_antisymm (le_of_not_gt pos) z0
      simp only [e,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero,neg_zero,exp_zero,mul_one]
      exact mass.trans (le_mul_of_one_le_right m0 (by norm_num))
  change _≤returnMass j*(returnDiscount i k:ℝ)
  simp only [returnDiscount,Rat.cast_min,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow]
  rw [mul_min_of_nonneg _ _ m0]
  refine le_min (by simpa using mass) (full.trans (mul_le_mul_of_nonneg_left ?_ m0))
  let b := (i-(k+1))/10
  have dist : 10*(b:ℝ) ≤ (j:ℝ)*(u/N)*2 := by
    have nonneg : 0≤(j:ℝ)*(u/N) := by positivity
    by_cases sep : k + 1 ≤ i
    · have count : 10*b+k+1 ≤ i := by dsimp [b]; omega
      have cast : 10*(b:ℝ)+k+1 ≤ i := by exact_mod_cast count
      have h := (return_bin_index n0 jl hu).1.2
      change ((N-j:ℕ):ℝ)*(u/N)≤((k+1:ℕ):ℝ)/2 at h
      rw [Nat.cast_sub jl,Nat.cast_succ,sub_mul,show (N:ℝ)*(u/N)=u by field_simp] at h
      linarith only [h,cast,lo]
    · have eb : b=0 := by dsimp only [b]; omega
      rw [eb,Nat.cast_zero,mul_zero]; linarith only [nonneg]
  have ex : exp (-(0.30*(j:ℝ)*z^2))≤(1/2:ℝ)^b := by
    apply le_trans _ (pow_le_pow_left₀ (exp_pos _).le one_half_step b)
    rw [← Real.exp_nat_mul,Real.exp_le_exp,z2]
    linarith only [dist]
  change 125*exp _≤125/2^b
  simpa only [div_pow,one_pow,mul_one_div] using mul_le_mul_of_nonneg_left ex (by norm_num : (0:ℝ)≤125)

theorem norm_return_symbol_neg (ω : ℝ) (j : ℕ) :
    ‖returnSymbol (-ω) j‖=‖returnSymbol ω j‖ := by
  have conj (x : ℤ) : areaCharacter (-ω) x=(starRingEnd ℂ) (areaCharacter ω x) := by
    rw [areaCharacter,areaCharacter,← Complex.exp_conj]
    congr 1
    simp
  have sym : returnSymbol (-ω) j=(starRingEnd ℂ) (returnSymbol ω j) := by
    simp only [returnSymbol,coeff_walkSeries,fairSeries,map_mul,map_pow,map_inv₀,map_ofNat,map_sum,conj]
  rw [sym,Complex.norm_conj]

theorem return_symbol_discount {N i j : ℕ} (n0 : 0<N) (jl : j≤N)
    {ω u : ℝ} (hu : u∈halfInterval i) (step : u/N≤0.02) (phase : ω^2=(u/N)^3/32) :
    let k := cappedBin i (((N-j:ℕ):ℝ)*(u/N))
    ‖returnSymbol ω j‖ ≤ returnMass j*(returnDiscount i k:ℝ) := by
  by_cases pos : 0≤ω
  · exact return_symbol_discount_of_nonneg n0 jl pos hu step phase
  · have w : 0≤-ω := by linarith
    have h := return_symbol_discount_of_nonneg n0 jl w hu step (by rwa [neg_sq])
    rwa [norm_return_symbol_neg] at h

end CentralUnimodality.ReturnSplit
