module

public import CentralUnimodality.MeshPhases

/-! A spatial derivative on the production mesh is a scaled integer
dot product with an explicit rounding allowance for the phase table. -/
@[expose] public section

namespace CentralUnimodality.MeshPhase

def dot (d k i r J : ℕ) (a : ℕ → ℤ) : ℤ :=
  ∑ t ∈ positiveModes J, a t*(t:ℤ)^r*sample d (k+1) (t*i+r*2^k)

private noncomputable def exactDot (k i r J : ℕ) (a : ℕ → ℤ) : ℝ :=
  ∑ t ∈ positiveModes J, (a t:ℝ)*t^r*Real.cos (2*Real.pi*((t*i+r*2^k:ℕ):ℝ)/2^(k+2))

private theorem raw_error {d k e : ℕ} (hd : 0 < d) (hp : radiusCheck d (k+1) e = true)
    (i r J : ℕ) (a : ℕ → ℤ) :
    |exactDot k i r J a-(dot d k i r J a:ℝ)/d| ≤
      ((e:ℝ)/d)*∑ t ∈ positiveModes J, |(a t:ℝ)| * (t:ℝ)^r := by
  unfold exactDot dot
  push_cast only [Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
  rw [Finset.sum_div,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro t _
  have hh := uniform_sample_error hd hp (t*i+r*2^k)
  rw [mul_div_assoc ((a t:ℝ)*t^r) (sample d (k+1) (t*i+r*2^k):ℝ) d,← mul_sub,abs_mul,abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (t:ℝ)^r),mul_comm ((e:ℝ)/d)]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

private theorem spatial_mesh_factor {Q : ℕ} (hQ : 0 < Q) {G : ℝ} (hG : 0 < G)
    (k i r J b : ℕ) (a : ℕ → ℤ) :
    spatialDerivative Q J G (fun t => (a t:ℝ)/b) r (i*(Q/(2^(k+2)*G))) =
      ((4*G/Q)*(2*Real.pi*G/Q)^r/b)*exactDot k i r J a := by
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have he (t : ℕ) : G*gridFrequency Q t*(i*(Q/(2^(k+2)*G)))+r*(Real.pi/2) =
      2*Real.pi*((t*i+r*2^k:ℕ):ℝ)/2^(k+2) := by
    dsimp [gridFrequency]
    push_cast
    rw [pow_add]
    field_simp
  have hom (t : ℕ) : G*gridFrequency Q t = (2*Real.pi*G/Q)*t := by unfold gridFrequency; ring
  unfold spatialDerivative exactDot
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [he,hom,mul_pow]
  ring

theorem derivative_dot_error {d k e Q b : ℕ} (hd : 0 < d) (hp : radiusCheck d (k+1) e = true)
    (hQ : 0 < Q) {G : ℝ} (hG : 0 < G) (i r J : ℕ) (a : ℕ → ℤ) :
    let factor := (4*G/Q)*(2*Real.pi*G/Q)^r/b
    |spatialDerivative Q J G (fun t => (a t:ℝ)/b) r (i*(Q/(2^(k+2)*G))) -
      factor*((dot d k i r J a:ℝ)/d)| ≤
      factor*((e:ℝ)/d)*(∑ t ∈ positiveModes J, |(a t:ℝ)| * (t:ℝ)^r) := by
  dsimp only
  let c := (4*G/Q)*(2*Real.pi*G/Q)^r/b
  have hc : 0 ≤ c := by dsimp [c]; positivity
  rw [spatial_mesh_factor hQ hG,← mul_sub,abs_mul,abs_of_nonneg hc,mul_assoc c]
  exact mul_le_mul_of_nonneg_left (raw_error hd hp i r J a) hc

end CentralUnimodality.MeshPhase
