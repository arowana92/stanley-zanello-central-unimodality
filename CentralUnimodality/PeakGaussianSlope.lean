module

public import CentralUnimodality.PrefixDifferenceBounds

/-! Upper bound the Gaussian slope by an affine function of squared
displacement. Averaging this inequality retains the actual prefix variance. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- The tangent at |y|=7/10 to x/(1+x²/2+x⁴/8), as a function of x²,
has positive residual after removing its double zero. -/
theorem gaussian_slope_quadratic (y : ℝ) :
    |y| * bell y ≤ 406/1000+(293/1000)*y^2 := by
  let x := |y|
  let s : ℝ := 7/10
  let a : ℝ := 4222540000/10404204001
  let b : ℝ := 21278800000/72829428007
  let D := 1+x^2/2+x^4/8
  have hx : 0≤x := abs_nonneg _
  have he := Real.sum_le_exp_of_nonneg (by positivity : 0≤x^2/2) 3
  norm_num [Finset.sum_range_succ,Nat.factorial] at he
  have hD : D≤exp (x^2/2) := by dsimp [D]; linarith only [he]
  have ha : 0≤a+b*x^2 := by dsimp [a,b]; positivity
  have H : x≤(a+b*x^2)*D := by
    have factor : (a+b*x^2)*D-x=(x-s)^2*(a/s^2+
        (2*s*(a/8+b/2)+4*s^3*b/8)*x+
        (a/8+b/2+3*s^2*b/8)*x^2+(2*s*b/8)*x^3+b/8*x^4) := by dsimp [D,s,a,b]; ring
    apply sub_nonneg.mp
    rw [factor]; dsimp [a,b,s]; positivity
  have K := H.trans (mul_le_mul_of_nonneg_left hD ha)
  change x*exp (-y^2/2)≤_
  rw [show -y^2/2= -(x^2/2) by dsimp [x]; rw [sq_abs]; ring,exp_neg,← div_eq_mul_inv]
  apply ((div_le_iff₀ (exp_pos _)).mpr K).trans
  have hs : x^2=y^2 := sq_abs _
  rw [hs]; unfold a b
  nlinarith only [sq_nonneg y]

private theorem bell_lower (V y : ℝ) :
    exp (-V/2)*(1+V/2-y^2/2)≤bell y := by
  have H := mul_le_mul_of_nonneg_left (add_one_le_exp ((V-y^2)/2)) (exp_pos (-V/2)).le
  rw [← exp_add,show -V/2+(V-y^2)/2= -y^2/2 by ring] at H
  dsimp only [bell]; linarith only [H]

/-- Any upper bound V for the actual normalized conditional second moment
controls both terms used for the forward sign at the saddle. -/
theorem prefix_growth_gaussian {m L : ℕ} (ht : L≤m) {c σ V : ℝ} (hσ : 0<σ)
    (hP : 0<live c (c*m) L 1)
    (hV : (∑ w∈ballots L, signMass c (c*m) w*(centeredRank c (c*m) m w)^2)/
      (live c (c*m) L 1*σ^2)≤V)
    (hs : FreeSuffixApproximation c (m-L) σ) {j : ℤ} (hj : meanRank c m=j) :
    let P := live c (c*m) L 1
    let A := prefixSiteMass c m L
    P*(normalHeight*exp (-V/2)-5/1000) ≤ σ*A j ∧
      -P*(normalHeight*(406/1000+293/1000*V)+7/1000) ≤ σ^2*(A (j+1)-A j) := by
  let P := live c (c*m) L 1
  let p (w : List Bool) := signMass c (c*m) w
  let k (w : List Bool) := j-shiftedPrefixRank (m-L) w
  let y (w : List Bool) := ((k w:ℝ)-meanRank c (m-L))/σ
  let S := freeRankMass c (m-L)
  let A := prefixSiteMass c m L
  let av (X : List Bool→ℝ) := ∑ w ∈ ballots L, p w*X w
  have hN : 0≤normalHeight := by unfold normalHeight; positivity
  have hprob : ∑ w ∈ ballots L,p w=P := (live_ballots ..).symm
  have hY : av (fun w => (y w)^2)≤P*V := by
    have he (w : List Bool) (hw : w∈ballots L) : p w*(y w)^2=
        signMass c (c*m) w*(centeredRank c (c*m) m w)^2/σ^2 := by
      rw [show y w= -centeredRank c (c*m) m w/σ by dsimp only [y,k]; rw [saddle_suffix_site c ht hj hw],div_pow,neg_sq,mul_div_assoc']
    dsimp only [av]; rw [Finset.sum_congr rfl he,← Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
    have H := (div_le_iff₀ (mul_pos hP (sq_pos_of_pos hσ))).mp hV
    dsimp only [P]; linarith only [H]
  have affine (F : List Bool→ℝ) (a b : ℝ) (hb : b≤0)
      (H : ∀ w∈ballots L, a+b*(y w)^2≤F w) : P*(a+b*V)≤av F := by
    have h := Finset.sum_le_sum (s:=ballots L) (fun w hw => mul_le_mul_of_nonneg_left (H w hw) (signMass_pos c (c*m) w).le)
    have hh (w : List Bool) : p w*(a+b*(y w)^2)=p w*a+b*(p w*(y w)^2) := by ring
    change _≤∑ w∈ballots L,p w*F w
    apply le_trans _ h
    change _≤∑ w∈ballots L,p w*(a+b*(y w)^2)
    simp_rw [hh]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,hprob]
    have H' := mul_le_mul_of_nonpos_left hY hb
    dsimp only [av] at H'; linarith only [H']
  have h₀ := affine (fun w => σ*S (k w))
    (normalHeight*exp (-V/2)*(1+V/2)-5/1000) (-normalHeight*exp (-V/2)/2) (by nlinarith only [mul_nonneg hN (exp_pos (-V/2)).le]) (by
      intro w _
      have H := (abs_le.mp (hs (k w)).1).1
      change -(5/1000)≤σ*S (k w)-normalHeight*bell (y w) at H
      linarith only [H,mul_le_mul_of_nonneg_left (bell_lower V (y w)) hN])
  have h₁ := affine (fun w => σ^2*(S (k w+1)-S (k w)))
    (-normalHeight*(406/1000)-7/1000) (-normalHeight*(293/1000)) (by linarith only [hN]) (by
      intro w _
      have H := (abs_le.mp (hs (k w)).2.1).1
      change -(7/1000)≤σ^2*(S (k w+1)-S (k w))+normalHeight*y w*bell (y w) at H
      have hy := (mul_le_mul_of_nonneg_right (le_abs_self (y w)) (exp_pos (-(y w)^2/2)).le).trans (gaussian_slope_quadratic (y w))
      dsimp only [bell] at H
      linarith only [H,mul_le_mul_of_nonneg_left hy hN])
  have Hmass : A j=∑ w∈ballots L,p w*S (k w) := prefixSiteMass_mixture c ht j
  have Hnext : A (j+1)=∑ w∈ballots L,p w*S (k w+1) := by
    rw [show A (j+1)=_ from prefixSiteMass_mixture c ht (j+1)]
    apply Finset.sum_congr rfl; intro w _
    dsimp only [k,p,S]; rw [show j+1-shiftedPrefixRank (m-L) w=j-shiftedPrefixRank (m-L) w+1 by omega]
  have he₀ : av (fun w => σ*S (k w))=σ*A j := by
    dsimp only [av]; rw [Hmass,Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
  have he₁ : av (fun w => σ^2*(S (k w+1)-S (k w)))=σ^2*(A (j+1)-A j) := by
    dsimp only [av]; rw [Hmass,Hnext,← Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro _ _; ring
  rw [he₀] at h₀
  rw [he₁] at h₁
  change P*(normalHeight*exp (-V/2)-5/1000)≤σ*A j ∧ _
  constructor <;> linarith only [h₀,h₁]

end CentralUnimodality.MarkedExcursion
