module

public import CentralUnimodality.CurveInterpolation

/-! A rational perturbation separates the leading terms of rows of equal
order. Its parameter is chosen after taking the determinant. -/
@[expose] public section

namespace CentralUnimodality.Polarization
open Polynomial Matrix
variable {n : ℕ}

private noncomputable def basisEntry (V : Polynomial ℚ) (s k j : ℕ) : ℚ :=
  ((X:Polynomial ℚ)^(s+k)*V^k).coeff j

private theorem perturbed_entry (e : ℚ) (V : Polynomial ℚ) (s a j L : ℕ) (ha : a ≤ L) :
    ((X:Polynomial ℚ)^s*(1+C e*X*V)^a).coeff j =
      ∑ k ∈ Finset.range (L+1), e^k * (Nat.choose a k:ℚ) * basisEntry V s k j := by
  classical
  have expand : (X:Polynomial ℚ)^s*(1+C e*X*V)^a =
      ∑ k ∈ Finset.range (a+1), C (e^k*(Nat.choose a k:ℚ)) * (X^(s+k)*V^k) := by
    rw [add_comm (1:Polynomial ℚ),add_pow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp [mul_pow,pow_add]
    ring
  rw [expand,Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  symm
  apply (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ ha)) _).symm
  intro k _ hk
  have hl : a < k := by simp at hk; omega
  simp [Nat.choose_eq_zero_of_lt hl]

private def rowTransform (W : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℕ)
    (i : Fin n) (k : ℕ) : ℚ := ∑ l, W i l * (Nat.choose (a l) k:ℚ)

private theorem transformed_entry (V : Polynomial ℚ) (s a : Fin n → ℕ)
    (W : Matrix (Fin n) (Fin n) ℚ) (hw : ∀ i l, s l ≠ s i → W i l=0)
    (L : ℕ) (ha : ∀ i, a i ≤ L) (e : ℚ) (i j : Fin n) :
    (W * orderMatrix (1+C e*X*V) s a) i j =
    ∑ k ∈ Finset.range (L+1), e^k * (rowTransform W a i k * basisEntry V (s i) k j) := by
  rw [Matrix.mul_apply]
  simp only [orderMatrix,Matrix.of_apply]
  simp_rw [perturbed_entry e V _ _ _ L (ha _),Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [rowTransform,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hs : s l=s i
  · rw [hs]; ring
  · simp [hw i l hs]

private noncomputable def normalRow (h L : ℕ) (b : ℕ → ℚ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (L+1), if h ≤ k then C (b k)*X^(k-h) else 0

private theorem normalRow_zero (h L : ℕ) (hh : h ≤ L) (b : ℕ → ℚ) :
    (normalRow h L b).eval 0 = b h := by
  classical
  unfold normalRow
  rw [Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single h]
  · simp
  · intro k _ hk
    by_cases hl : h ≤ k
    · simp [hl,zero_pow (show k-h ≠ 0 by omega)]
    · simp [hl]
  · simp [show h<L+1 by omega]

private theorem normalRow_scale (e : ℚ) (h L : ℕ) (b : ℕ → ℚ) (hb : ∀ k < h, b k=0) :
    e^h * (normalRow h L b).eval e = ∑ k ∈ Finset.range (L+1), e^k*b k := by
  unfold normalRow
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hl : h ≤ k
  · simp only [hl,ite_true,eval_mul,eval_C,eval_pow,eval_X]
    calc
      _ = e^(k-h)*e^h*b k := by ring
      _ = _ := by rw [← pow_add,Nat.sub_add_cancel hl]
  · simp [hl,hb k (by omega)]

/-- From a successful test of the separated rows, obtain a test of the
original rows. The transformed determinant at zero is the separated one. -/
theorem perturbation_step (s a : Fin n → ℕ) (hp : Function.Injective fun i => (s i,a i))
    (σ : Perm n) (V : Polynomial ℚ)
    (hV : (orderMatrix V (fun i => s i+groupIndex s σ i) (groupIndex s σ)).det ≠ 0) :
    ∃ U : Polynomial ℚ, U.eval 0=1 ∧ (orderMatrix U s a).det ≠ 0 := by
  classical
  let h := groupIndex s σ
  choose c cs ci using fun i => group_interpolation s a hp i (groupIndex_lt s σ i)
  let W : Matrix (Fin n) (Fin n) ℚ := Matrix.of c
  have hw (i l) (hs : s l ≠ s i) : W i l=0 := cs i l hs
  have ht (i k) (hk : k < (orderGroup s i).card) :
      rowTransform W a i k = if k=h i then 1 else 0 := ci i k hk
  let L := n+∑ i, a i
  have ha (i) : a i ≤ L := by
    have := Finset.single_le_sum (s := Finset.univ) (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp [L]; omega
  have hh (i) : h i ≤ L := by
    have h₁ := groupIndex_lt s σ i
    have h₂ := Finset.card_le_univ (orderGroup s i)
    rw [Fintype.card_fin] at h₂
    dsimp [h,L]; omega
  let b := fun (i j : Fin n) k => rowTransform W a i k * basisEntry V (s i) k j
  let P : Matrix (Fin n) (Fin n) (Polynomial ℚ) := Matrix.of fun i j => normalRow (h i) L (b i j)
  have hP : (evalRingHom 0).mapMatrix P = orderMatrix V (fun i => s i+h i) h := by
    ext i j
    change (normalRow (h i) L (b i j)).eval 0 = _
    rw [normalRow_zero _ _ (hh i)]
    simp [b,ht i (h i) (groupIndex_lt s σ i),basisEntry,orderMatrix]
  have hD : P.det ≠ 0 := by
    intro hz
    apply hV
    rw [← hP,← RingHom.map_det,hz,map_zero]
  obtain ⟨e,he⟩ : ∃ e : ℚ, (X*P.det).eval e ≠ 0 := by
    by_contra! hz
    exact (mul_ne_zero X_ne_zero hD) (Polynomial.funext (fun i => by simpa using hz i))
  simp only [eval_mul,eval_X,mul_ne_zero_iff] at he
  have hM : W*orderMatrix (1+C e*X*V) s a =
      diagonal (fun i => e^(h i)) * (evalRingHom e).mapMatrix P := by
    ext i j
    rw [transformed_entry V s a W hw L ha,diagonal_mul]
    change _ = e^(h i)*(normalRow (h i) L (b i j)).eval e
    apply (normalRow_scale _ _ _ _ _).symm
    intro k hk
    simp [ht i k (lt_trans hk (groupIndex_lt s σ i)),hk.ne]
  refine ⟨1+C e*X*V,by simp,?_⟩
  intro hz
  have hd := congrArg Matrix.det hM
  rw [Matrix.det_mul,Matrix.det_mul,hz,mul_zero,Matrix.det_diagonal,← RingHom.map_det] at hd
  exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ he.1)) he.2) hd.symm

end CentralUnimodality.Polarization
