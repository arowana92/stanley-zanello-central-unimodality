module

public import CentralUnimodality.DyckDiagonalSlices
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Raising and lowering on a degree-d slice imply reflected dimension
inequalities. The proof uses the commutator and the bottom grade directly. -/
@[expose] public section

namespace CentralUnimodality

structure WeightOperators (d : ℕ) (V : Type*) [AddCommGroup V] [Module ℚ V] where
  space : ℕ → Submodule ℚ V
  raise : Module.End ℚ V
  lower : Module.End ℚ V
  raise_mem : ∀ k, ∀ v ∈ space k, raise v ∈ space (k+1)
  lower_mem : ∀ k, ∀ v ∈ space (k+1), lower v ∈ space k
  lower_zero : ∀ v ∈ space 0, lower v = 0
  commutator : ∀ k, ∀ v ∈ space k,
    raise (lower v) = lower (raise v) + (2*(k:ℚ)-d) • v

namespace WeightOperators

variable {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℚ V] (T : WeightOperators d V)

private theorem raise_succ (r : ℕ) (v : V) :
    (T.raise^(r+1)) v = T.raise ((T.raise^r) v) := by rw [pow_succ',mul_apply_eq_comp]

private theorem power_mem {k : ℕ} {v : V} (hv : v ∈ T.space k) (r : ℕ) :
    (T.raise^r) v ∈ T.space (k+r) := by
  induction r with
  | zero => simpa
  | succ r ih => exact (T.raise_succ r v).symm ▸ T.raise_mem _ _ ih

private theorem power_lower {k : ℕ} {v : V} (hv : v ∈ T.space k) (s : ℕ) :
    (T.raise^(s+1)) (T.lower v) = T.lower ((T.raise^(s+1)) v) +
      (((s:ℚ)+1)*(2*k-d+s)) • ((T.raise^s) v) := by
  induction s with
  | zero => simpa using T.commutator k v hv
  | succ s ih =>
    rw [T.raise_succ (s+1) (T.lower v),ih,map_add,map_smul,
      T.commutator (k+(s+1)) _ (T.power_mem hv (s+1)),← T.raise_succ (s+1),← T.raise_succ s,
      add_assoc,← add_smul]
    congr 2
    push_cast
    ring

/-- When the reflected target lies at or below the opposite weight,
vanishing of one positive raising power forces vanishing one step earlier. -/
private theorem kernel_step (k s : ℕ) (v : V) (hv : v ∈ T.space k)
    (hd : 2*k+s < d) (hz : (T.raise^(s+1)) v = 0) : (T.raise^s) v = 0 := by
  induction k generalizing s v with
  | zero =>
    have h := T.power_lower hv s
    rw [T.lower_zero v hv,map_zero,hz,map_zero,zero_add] at h
    have hw : 2*(0:ℚ)-d+s < 0 := by exact_mod_cast (show (2*(0:ℤ)-d+s) < 0 by omega)
    exact (smul_eq_zero.mp h.symm).resolve_left (mul_ne_zero (by positivity) hw.ne)
  | succ k ih =>
    have h := T.power_lower hv s
    have hz' : (T.raise^(s+1+1)) v = 0 := by rw [T.raise_succ,hz,map_zero]
    have h' := T.power_lower hv (s+1)
    rw [hz',hz,map_zero,smul_zero,add_zero] at h'
    have hl := ih (s+1) (T.lower v) (T.lower_mem k v hv) (by omega) h'
    rw [hl,hz,map_zero,zero_add] at h
    have hw : 2*((k+1:ℕ):ℚ)-d+s < 0 := by
      exact_mod_cast (show 2*((k+1:ℕ):ℤ)-d+s < 0 by omega)
    exact (smul_eq_zero.mp h.symm).resolve_left (mul_ne_zero (by positivity) hw.ne)

theorem raise_power_injective_on {k r : ℕ} (hd : 2*k+r ≤ d) :
    Set.InjOn (T.raise^r) (T.space k) := by
  have zero_of_power (s : ℕ) (hs : 2*k+s ≤ d) (v : V) (hv : v ∈ T.space k)
      (h : (T.raise^s) v = 0) : v = 0 := by
    induction s with
    | zero => simpa using h
    | succ s ih => exact ih (by omega) (T.kernel_step k s v hv (by omega) h)
  intro x hx y hy he
  apply sub_eq_zero.mp
  exact zero_of_power r hd (x-y) ((T.space k).sub_mem hx hy) (by rw [map_sub,he,sub_self])

theorem reflected_finrank {i j : ℕ} [FiniteDimensional ℚ (T.space j)] (hij : i ≤ j) (hs : i+j ≤ d) :
    Module.finrank ℚ (T.space i) ≤ Module.finrank ℚ (T.space j) := by
  let r := j-i
  have he : i+r = j := by dsimp [r]; omega
  let L := ((T.raise^r).comp (T.space i).subtype).codRestrict (T.space j)
    (fun v => he ▸ T.power_mem v.property r)
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro x y h
  apply Subtype.ext
  exact T.raise_power_injective_on (k := i) (r := r) (by omega) x.property y.property
    (congrArg Subtype.val h)

/-- For a univariate Hilbert series it suffices to know the sum of the
weight dimensions and a lower bound on the contributing total degrees. -/
theorem reflected_of_weight_sum {p : Polynomial ℕ} {cut : ℕ}
    (degrees : Finset ℕ) (a : ℕ → ℕ) (T : ∀ d, WeightOperators d (Fin (a d) → ℚ))
    (hc : ∀ d ∈ degrees, cut ≤ d)
    (hf : ∀ k, p.coeff k = ∑ d ∈ degrees, Module.finrank ℚ ((T d).space k)) :
    ReflectedCoeffs p (cut:ℤ) := by
  intro i j hij hs
  rw [hf,hf]
  apply Finset.sum_le_sum
  intro d hd
  apply (T d).reflected_finrank hij.le
  have h := hc d hd
  omega

/-- A rational raising/lowering realization of each ordinary Dyck slice
implies the all-size coefficient comparisons used by the staircase induction. -/
theorem dyck_comparisons_of_operators
    (h : ∀ n d, ∃ (a : ℕ) (T : WeightOperators d (Fin a → ℚ)),
      ∀ k, Module.finrank ℚ (T.space k) = dyckSliceCount n d k) : DyckComparisons := by
  intro n i j hij hsum
  rw [dyck_slice_sum,dyck_slice_sum]
  apply Finset.sum_le_sum
  intro d hd
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨a,T,hT⟩ := h n (dyckTotalDegree w)
  rw [← hT i,← hT j]
  apply T.reflected_finrank hij.le
  have hc := dyck_diagonal_cutoff hw
  omega

/-- The specialization at the second grading variable equal to one is
enough for the staircase induction, given the alternating degree cutoff. -/
theorem conjecture34_of_weight_sums_and_midpoints
    (hw : ∀ n, ∃ (degrees : Finset ℕ) (a : ℕ → ℕ) (T : ∀ d, WeightOperators d (Fin (a d) → ℚ)),
      (∀ d ∈ degrees, ⌈dyckLower n⌉₊ ≤ d) ∧
      (∀ k, (dyckPoly n).coeff k = ∑ d ∈ degrees, Module.finrank ℚ ((T d).space k)))
    (hm : ∀ n ≥ 96, ∀ δ ≤ 1, CentralToMidpoint n δ) : Conjecture34 := by
  apply conjecture34_of_comparisons_and_midpoints _ hm
  intro n
  obtain ⟨degrees,a,T,hc,hf⟩ := hw n
  exact reflected_of_weight_sum degrees a T hc hf

end WeightOperators
end CentralUnimodality
