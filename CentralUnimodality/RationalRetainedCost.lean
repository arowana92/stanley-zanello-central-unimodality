module

public import CentralUnimodality.RationalCellWeights
public import CentralUnimodality.ReturnFrequencyBins
public import CentralUnimodality.SplitCellMaxima

/-! Rational frequency-cell allowances evaluated at half-length
150,000. Early returns use a maximum; later returns use the local
first-return mass and the Fourier discount for the elapsed excursion time. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real ReturnSplit

def qCost (i : ℕ) : ℚ := (costUnits i:ℚ)/10^30
def earlyUnits (i : ℕ) := ((Finset.range (i+1)).filter fun j => 19*i/20≤j).sup costUnits
def qEarly (i : ℕ) : ℚ := (earlyUnits i:ℚ)/10^30

def discountedCost (i k : ℕ) := returnDiscount i k*qCost k

theorem discountedCost_nonneg (i k : ℕ) : 0≤discountedCost i k :=
  mul_nonneg (discount_bounds i k).1 (by unfold qCost; positivity)

theorem discountedCost_le (i k : ℕ) : discountedCost i k≤qCost k :=
  mul_le_of_le_one_left (by unfold qCost; positivity) (discount_bounds i k).2

def qLate (i : ℕ) : ℚ :=
  if i=0 then 0 else ∑ k ∈ Finset.range (19*(i+1)/20+1), roundUpper (lateWeight i k*discountedCost i k)

def topTime (i : ℕ) : ℚ := ((i:ℚ)+1)/2
def topFrequency (i : ℕ) := topTime i*rootHigh (topTime i)

def splitFrequencyAllowance (i : ℕ) : ℚ :=
  let H := topTime i
  let t := H/150000
  let e := rootHigh 150000
  (1+topFrequency i/2)*(15/10^16)+(36/10^14)*H+4*e*t*(3/10^12)+
    t^2*(2*e*(qCost i+qEarly i)+qLate i)+t*(correctionJetNum i 0:ℚ)/(4*10^30)

def outerCellAllowance (i : ℕ) : ℚ := 100*scaledNegExp (0.186*(i:ℚ)/2)+1/10^14

def frequencyAllowance (i : ℕ) : ℚ :=
  if i<228 then splitFrequencyAllowance i else outerCellAllowance i

def frequencyCharge (i r : ℕ) : ℚ :=
  roundUpper (3/4*rootHigh (topTime i)*(topFrequency i)^r*frequencyAllowance i)

theorem qCost_early {i k : ℕ} (lo : 19*i/20≤k) (hi : k≤ i) : qCost k≤qEarly i := by
  have mem : k∈(Finset.range (i+1)).filter (fun j => 19*i/20≤j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),lo⟩
  have u : costUnits k≤earlyUnits i := Finset.le_sup mem
  unfold qCost qEarly
  exact div_le_div_of_nonneg_right (by exact_mod_cast u) (by positivity)

theorem late_price {N i : ℕ} (hn : 150000≤N) (ip : 0< i) :
    lateAllowance N i (fun k => (discountedCost i k:ℝ))≤(qLate i:ℝ) := by
  simp only [qLate,Nat.ne_of_gt ip,ite_false,lateAllowance,Rat.cast_sum]
  apply Finset.sum_le_sum
  intro k _
  have c : 0≤(discountedCost i k:ℝ) := by exact_mod_cast discountedCost_nonneg i k
  have w := mul_le_mul_of_nonneg_right (late_weight_bound hn ip k) c
  have ru := (Rat.cast_le (K:=ℝ)).mpr (round_upper (lateWeight i k*discountedCost i k))
  rw [Rat.cast_mul] at ru
  exact w.trans ru

theorem qLate_nonneg (i : ℕ) : 0≤qLate i := by
  unfold qLate
  split
  · exact le_rfl
  · apply Finset.sum_nonneg
    intro k _; unfold roundUpper; positivity

theorem frequencyAllowance_nonneg (i : ℕ) : 0≤frequencyAllowance i := by
  have l := qLate_nonneg i
  unfold frequencyAllowance
  split
  · unfold splitFrequencyAllowance topFrequency topTime qCost qEarly rootHigh
    positivity
  · have cap := scaledNegExp_sound (x:=0.186*(i:ℚ)/2) (by positivity)
    have nonneg : 0≤scaledNegExp (0.186*(i:ℚ)/2) := by exact_mod_cast (exp_nonneg _).trans cap
    unfold outerCellAllowance
    positivity

theorem scaled_steps {N : ℕ} (hn : 150000≤N) {u H : ℝ} (hu : 0≤u) (uh : u≤H) :
    u/N≤H/150000 ∧ sqrt N*(u/N)≤(rootHigh 150000:ℝ)*(H/150000) ∧
      sqrt N*(u/N)^2≤(rootHigh 150000:ℝ)*(H/150000)^2 := by
  have nr : (150000:ℝ)≤N := by exact_mod_cast hn
  have np : 0<(N:ℝ) := by linarith
  have nsp := sqrt_pos_of_pos np
  have bp : (0:ℝ)<sqrt 150000 := by positivity
  have rh := (root_brackets (x:=150000) (by norm_num)).2
  norm_num only [Rat.cast_ofNat] at rh
  have step := div_le_div₀ (hu.trans uh) uh (by norm_num : (0:ℝ)<150000) nr
  have sn (n v : ℝ) (hp : 0<n) : sqrt n*(v/n)=v/sqrt n := by
    have h := sq_sqrt hp.le
    field_simp [(sqrt_pos_of_pos hp).ne',hp.ne']; nlinarith only [congrArg (v*·) h]
  have first : sqrt N*(u/N)≤(rootHigh 150000:ℝ)*(H/150000) := by
    rw [sn _ _ np]
    apply (div_le_div₀ (hu.trans uh) uh bp (sqrt_le_sqrt nr)).trans
    rw [← sn 150000 H (by norm_num)]
    exact mul_le_mul_of_nonneg_right rh (div_nonneg (hu.trans uh) (by norm_num))
  refine ⟨step,first,?_⟩
  rw [pow_two,pow_two,← mul_assoc,← mul_assoc]
  apply mul_le_mul first step (div_nonneg hu np.le)
  exact mul_nonneg ((sqrt_nonneg _).trans rh) (div_nonneg (hu.trans uh) (by norm_num))

end CentralUnimodality.PolynomialTrial
