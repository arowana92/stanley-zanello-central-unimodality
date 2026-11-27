module

public import CentralUnimodality.LaurentColumns
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! A finite Laurent-polynomial certificate for the first M corank moments
in both families, valid at every size. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

def alpha : Laurent := [(0,1/2),(1,1/2)]
def beta : Laurent := [(0,1/2),(1,-1/2)]

theorem alpha_identity : dyckBase * eval alpha = 1 := by
  simp only [alpha,eval,rootPower_zero,rootPower_one, mul_one, add_zero]
  have half : C ((1:ℚ)/2) * 2 = (1:PowerSeries ℚ) := by
    rw [← map_ofNat (C (R := ℚ)) 2, ← map_mul]; norm_num
  linear_combination C ((1:ℚ)/2)*dyckBase_mul_root + half

theorem beta_identity : eval beta = X*dyckBase := by
  simp only [beta,eval,rootPower_zero,rootPower_one, mul_one, add_zero, neg_div, map_neg, catalanRoot]
  have half : C ((1:ℚ)/2) * 2 = (1:PowerSeries ℚ) := by
    rw [← map_ofNat (C (R := ℚ)) 2, ← map_mul]; norm_num
  linear_combination X*dyckBase*half

def unitColumn (p : Laurent) (r : ℕ) : Laurent := if r = 0 then p else []

def stripped (D : ℕ → Laurent) (r : ℕ) : Laurent := add (D r) (scaleShift (-1) 0 (unitColumn alpha r))

def dyckRhs (D : ℕ → Laurent) (r : ℕ) : Laurent :=
  add (unitColumn alpha r) (mul beta (convolution D (shifted .dyck 1 D) r))

def ballotRhs (D B : ℕ → Laurent) (r : ℕ) : Laurent :=
  add (scaleShift 1 1 (D r)) (exponential (convolution (stripped D) (shifted .ballot 2 B)) r)

def oddRhs (D B : ℕ → Laurent) (r : ℕ) : Laurent :=
  convolution D (shifted .ballot 1 B) r

noncomputable def model (a : PowerSeries ℚ) (A : ℕ → Laurent) :=
  fromColumns fun j => a * eval (A j)

private theorem model_column (a : PowerSeries ℚ) (A : ℕ → Laurent) (r : ℕ) :
    momentColumn r (model a A) = a*eval (A r) := momentColumn_fromColumns ..

private theorem unit_column (r : ℕ) :
    dyckBase * eval (unitColumn alpha r) = momentColumn r 1 := by
  rw [momentColumn_one, unitColumn]
  split <;> simp [alpha_identity, eval]

private theorem stripped_column (D : ℕ → Laurent) (r : ℕ) :
    momentColumn r (model dyckBase D - 1) = dyckBase * eval (stripped D r) := by
  rw [momentColumn_sub, model_column, ← unit_column, stripped, eval_add, eval_scaleShift, rootPower_zero]
  simp
  ring

private theorem model_shifted (b : MomentBase) (d : ℕ) (A : ℕ → Laurent) (r : ℕ) :
    momentColumn r (rescale ((exp ℚ)^d) (model b.value A)) = b.value * eval (shifted b d A r) :=
  shifted_columns b d _ A r (fun j _ => model_column _ _ j)

/-- Each hypothesis is a finite Laurent identity through order M. Together
they certify all three tables against the literal Dyck and staircase areas. -/
theorem certify_columns (M : ℕ) (D B O : ℕ → Laurent)
    (hd : ∀ r ≤ M, eval (D r) = eval (dyckRhs D r))
    (hb : ∀ r ≤ M, eval (mul alpha (B r)) = eval (ballotRhs D B r))
    (ho : ∀ r ≤ M, eval (O r) = eval (oddRhs D B r)) :
    SameColumns M (model dyckBase D) (dyckSeries (exp ℚ)) ∧
    SameColumns M (model ballotBase B) (evenBallotSeries (exp ℚ)) ∧
    SameColumns M (model (dyckBase*ballotBase) O) (oddBallotSeries (exp ℚ)) := by
  apply certify_stump_moments
  · intro r hr
    rw [model_column, hd r hr, dyckRhs, eval_add, eval_mul, beta_identity, mul_add, unit_column,
      momentColumn_add, momentColumn_X_mul]
    congr 1
    have H := product_columns (model dyckBase D) (rescale (exp ℚ) (model dyckBase D)) dyckBase dyckBase
      D (shifted .dyck 1 D) r (fun i _ => model_column _ _ i)
      (fun i _ => by simpa only [pow_one, MomentBase.value] using model_shifted .dyck 1 D i)
    rw [H]
    ac_rfl
  · intro r hr
    have hdB (j : ℕ) : momentColumn j ((model dyckBase D-1)*rescale ((exp ℚ)^2) (model ballotBase B)) =
        (dyckBase*ballotBase)*eval (convolution (stripped D) (shifted .ballot 2 B) j) :=
      product_columns _ _ _ _ _ _ j (fun i _ => stripped_column _ i) (fun i _ => model_shifted .ballot 2 B i)
    rw [model_column, momentColumn_add, model_column, exp_columns _ (dyckBase*ballotBase) _ r (fun i _ => hdB i)]
    have h := hb r hr
    rw [eval_mul, ballotRhs, eval_add, eval_scaleShift, map_one, one_mul, rootPower_one] at h
    calc
      _ = (dyckBase*ballotBase)*(eval alpha*eval (B r)) := by
        rw [mul_mul_mul_comm, alpha_identity, one_mul]
      _ = _ := by
        rw [h, mul_add]
        congr 1
        calc
          _ = dyckBase*(catalanRoot*ballotBase)*eval (D r) := by ac_rfl
          _ = _ := by rw [catalanRoot_mul_ballotBase, mul_one]
  · intro r hr
    rw [model_column, ho r hr]
    exact (product_columns _ _ _ _ D (shifted .ballot 1 B) r (fun i _ => model_column _ _ i)
      (fun i _ => by simpa only [pow_one, MomentBase.value] using model_shifted .ballot 1 B i)).symm

end CentralUnimodality.Laurent
