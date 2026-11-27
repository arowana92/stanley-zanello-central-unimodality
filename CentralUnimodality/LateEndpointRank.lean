module

public import CentralUnimodality.TiltedWallProducts
public import CentralUnimodality.RankHitDecomposition

/-! At the late cut, paths with the same prefix endpoint have the same
ruin transform in the remaining steps. The height tilt therefore preserves
the cancellations in the prefix row, including its ballot restriction. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Polynomial

private noncomputable def ruinRow (c a θ : ℝ) (n H : ℕ) :=
  endpointRow c (c*n) a θ ((words n).filter (fun w => ¬ BallotFrom H w))

private theorem ruinRow_norm (c a θ : ℝ) (n H : ℕ) :
    endpointNorm (ruinRow c a θ n H) ≤ ruin c n H := by
  apply (endpointRow_mass ..).trans_eq
  simp only [Finset.sum_filter,ruin,ite_not]

private theorem atom_change (c u a b θ : ℝ) {T : ℕ} {v : List Bool} (hv : v ∈ words T) :
    endpointAtom c u a θ v = endpointAtom c (u-b) a θ v *
      monomial 0 (((coshProduct c (u-b) T/coshProduct c u T)*exp (b*displacement v):ℝ):ℂ) := by
  have H := congrArg (· * exp (b*displacement v)) (prefix_height_shift c u b hv)
  rw [mul_assoc,← exp_add,show -b*(displacement v:ℝ)+b*displacement v=0 by ring,exp_zero,mul_one] at H
  simp only [endpointAtom,monomial_mul_monomial,add_zero,Complex.ofReal_mul]
  rw [H]; push_cast; ring_nf

/-- An endpoint row for paths which first cross strictly after T, at any
rank frequency. Its bound keeps the full endpoint norm of the shifted ballot
prefix and the explicit suffix ruin cost. -/
theorem late_endpoint_bound {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) (θ : ℝ) (T n : ℕ) :
    let m := T+n
    let Z := coshProduct c (c*m-b) T/coshProduct c (c*m) T
    endpointNorm (endpointRow c (c*m) m θ (lateHitEvent m T)) ≤
      endpointNorm (wallRow c (c*m-b) m θ 0 T)*(Z*exp (n*b^2/2)) := by
  let m := T+n
  let Z := coshProduct c (c*m-b) T/coshProduct c (c*m) T
  let E (k : ℕ) := T-2*k
  let K (k : ℕ) := monomial 0 ((Z*exp (b*(E k:ℝ)):ℝ):ℂ) * ruinRow c n θ n (E k)
  have hZ : 0 ≤ Z := (div_pos (coshProduct_pos ..) (coshProduct_pos ..)).le
  have hk (k : ℕ) : endpointNorm (K k) ≤ Z*exp (n*b^2/2) := by
    apply (endpointNorm_mul ..).trans
    rw [endpointNorm_monomial,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hZ (exp_pos _).le)]
    apply (mul_le_mul_of_nonneg_left ((ruinRow_norm ..).trans (suffix_ruin hc hb n (E k)))
      (mul_nonneg hZ (exp_pos _).le)).trans
    rw [mul_assoc,← exp_add]
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) hZ
    linarith
  have he : endpointRow c (c*m) m θ (lateHitEvent m T) =
      ∑ v ∈ ballots T, endpointAtom c (c*m-b) m θ v * K (wordParts v).length := by
    unfold endpointRow lateHitEvent
    rw [Finset.sum_filter,split_word_sum]
    rw [ballots,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    have hl := mem_words.mp hv
    have htake (w : List Bool) : (v++w).take T=v := by rw [← hl]; simp
    simp only [htake,Finset.mem_filter,hv,true_and,hl,ballot_split,Nat.zero_add]
    by_cases hvb : BallotFrom 0 v
    · have hpos := ballot_endpoint_nonneg hvb
      have hD : (E (wordParts v).length:ℤ)=displacement v := by
        have h := displacement_length v
        rw [hl] at h; dsimp [E]; omega
      have hR : (E (wordParts v).length:ℝ)=(displacement v:ℝ) := by exact_mod_cast hD
      have hu : c*(m:ℝ)-c*T=c*n := by dsimp [m]; push_cast; ring
      have ha : (m:ℝ)-T=n := by dsimp [m]; push_cast; ring
      have hcng : endpointAtom c (c*m) m θ v = endpointAtom c (c*m-b) m θ v *
          monomial 0 ((Z*exp (b*displacement v):ℝ):ℂ) := atom_change c (c*m) m b θ hv
      simp only [hvb,true_and,ite_true,endpointAtom_append,hl,hu,ha,K,ruinRow,endpointRow,
        Finset.sum_filter,hR,← mul_assoc,← hcng,Finset.mul_sum,mul_ite,mul_zero,E]
    · simp [hvb]
  change endpointNorm (endpointRow c (c*m) m θ (lateHitEvent m T)) ≤ _
  rw [he]
  exact endpoint_continuation c (c*m-b) m θ (ballots T) K hk

/-- The scalar characteristic function uses exactly the strict-partition
rank, summed over the actual late crossing event. -/
theorem rank_character_le_row (c θ : ℝ) {m : ℕ} (A : Finset (List Bool)) (hA : A ⊆ words m) :
    ‖∑ w ∈ A, (signMass c (c*m) w:ℂ)*phase (θ*(wordParts w).sum)‖ ≤
      endpointNorm (endpointRow c (c*m) m θ A) := by
  let P := endpointRow c (c*m) m θ A
  have he : P.eval 1=∑ w ∈ A, (signMass c (c*m) w:ℂ)*phase (θ*(wordParts w).sum) := by
    change (∑ w ∈ A, endpointAtom c (c*m) m θ w).eval 1=_
    rw [eval_finsetSum]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [endpointAtom,eval_monomial,one_pow,mul_one]
    rw [← mem_words.mp (hA hw),prefixRank_full]
  rw [← he,eval_eq_sum]
  simpa [Polynomial.sum,endpointNorm] using (norm_sum_le P.support (fun k => P.coeff k))

end CentralUnimodality.MarkedExcursion
