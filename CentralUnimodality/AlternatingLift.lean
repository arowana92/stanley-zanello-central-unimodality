module

public import CentralUnimodality.DiagonalCoinvariants

/-! A signed average lifts each alternating class of fixed bidegree to
an alternating polynomial of that same bidegree. -/
@[expose] public section

namespace CentralUnimodality.Polarization
open MvPolynomial

variable {n : ℕ}
abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)

theorem rename_ideal (σ : Perm n) {p : Poly n} (hp : p ∈ invariantIdeal n) :
    rename (reindex σ) p ∈ invariantIdeal n := by
  change p ∈ Submodule.span (Poly n) {q | positiveInvariant q} at hp
  induction hp using Submodule.span_induction with
  | mem p hp => rw [hp.2 σ]; exact Ideal.subset_span hp
  | zero => simp
  | add p q _ _ hp hq => simpa using (invariantIdeal n).add_mem hp hq
  | smul f p _ ih => simpa [smul_eq_mul] using (invariantIdeal n).mul_mem_left (rename (reindex σ) f) ih

noncomputable def coinvariantRename (σ : Perm n) : Module.End ℚ (Poly n ⧸ relations n) :=
  (relations n).mapQ (relations n) (rename (R := ℚ) (reindex σ)).toLinearMap fun _ hp => rename_ideal σ hp

private theorem rename_mul (σ τ : Perm n) (p : Poly n) :
    rename (reindex σ) (rename (reindex τ) p) = rename (reindex (σ*τ)) p := by
  rw [rename_rename]
  rfl

private theorem rename_grade (σ : Perm n) (b : Bool) {p : Poly n} {l : ℤ}
    (hp : p.IsWeightedHomogeneous (degree b) l) : (rename (reindex σ) p).IsWeightedHomogeneous (degree b) l := by
  intro x hx
  obtain ⟨m,rfl,hm⟩ := coeff_rename_ne_zero _ p x hx
  rw [← hp hm,Finsupp.weight_apply,Finsupp.weight_apply,Finsupp.sum_mapDomain_index]
  · rfl
  · simp
  · intros; simp [add_mul]

private theorem sign_twice (σ : Perm n) : (σ.sign:ℤ)*(σ.sign:ℤ) = 1 := by
  rcases Int.units_eq_one_or (σ.sign) with h|h <;> rw [h] <;> decide

private noncomputable def signedSum (p : Poly n) : Poly n :=
  ∑ σ : Perm n, (σ.sign:ℤ) • rename (reindex σ) p

private theorem sum_alternating (p : Poly n) : signedSum p ∈ alternating n := by
  intro σ
  unfold signedSum
  rw [map_sum,Finset.smul_sum]
  simp only [map_zsmul,rename_mul,smul_smul]
  let term := fun τ : Perm n => ((σ.sign:ℤ)*(τ.sign:ℤ)) • rename (reindex τ) p
  have ht (τ : Perm n) : (τ.sign:ℤ) • rename (reindex (σ*τ)) p = term (σ*τ) := by
    dsimp [term]
    rw [Equiv.Perm.sign_mul,Units.val_mul,← mul_assoc,sign_twice,one_mul]
  simp_rw [ht]
  exact Equiv.sum_comp (Equiv.mulLeft σ) term

private theorem sum_bidegree {p : Poly n} {d k : ℕ} (hp : p ∈ bidegreeSpace n d k) :
    signedSum p ∈ bidegreeSpace n d k := by
  apply (bidegreeSpace n d k).sum_mem
  intro σ _
  rw [← Int.cast_smul_eq_zsmul ℚ]
  apply (bidegreeSpace n d k).smul_mem
  exact ⟨rename_grade σ false hp.1,rename_grade σ true hp.2⟩

theorem coinvariantSpace_iff {d k : ℕ} (q : Poly n ⧸ relations n) :
    q ∈ coinvariantSpace n d k ↔ q ∈ (bidegreeSpace n d k).map (relations n).mkQ ∧
      ∀ σ : Perm n, coinvariantRename σ q = (σ.sign:ℤ) • q := by
  constructor
  · rintro ⟨p,⟨hb,ha⟩,rfl⟩
    refine ⟨⟨p,hb,rfl⟩,fun σ => ?_⟩
    change (relations n).mkQ (rename (reindex σ) p) = _
    rw [ha σ,map_zsmul]
  · rintro ⟨⟨p,hp,rfl⟩,ha⟩
    let N := Fintype.card (Perm n)
    have hpos : 0 < N := Fintype.card_pos
    have hn : (N:ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    let c := ((N:ℚ)⁻¹)
    refine ⟨c • signedSum p,⟨(bidegreeSpace n d k).smul_mem _ (sum_bidegree hp),
      (alternating n).smul_mem _ (sum_alternating p)⟩,?_⟩
    have he (σ : Perm n) : (relations n).mkQ ((σ.sign:ℤ) • rename (reindex σ) p) = (relations n).mkQ p := by
      have h := ha σ
      change (relations n).mkQ (rename (reindex σ) p) = _ at h
      rw [map_zsmul,h,smul_smul,sign_twice,one_smul]
    simp only [map_smul,signedSum,map_sum,he,Finset.sum_const,Finset.card_univ]
    change c • (N • _) = _
    rw [← Nat.cast_smul_eq_nsmul ℚ,smul_smul,inv_mul_cancel₀ hn,one_smul]

end CentralUnimodality.Polarization
