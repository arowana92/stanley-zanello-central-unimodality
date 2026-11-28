module

public import CentralUnimodality.HeightBlockTransfer
public import CentralUnimodality.ReflectedBlockProduct

/-! Compose finite certificates for every pair of boundary heights.
The resulting coefficient inequalities apply to walks of arbitrary length. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock
open Polynomial

noncomputable def kernel (m h t : ℕ) : ℕ[X] :=
  transfer X m h (fun k => if k=t then 1 else 0)

theorem finish_le (h : ℕ) (w : List Bool) : finish h w≤h+w.length := by
  induction w generalizing h with
  | nil => simp [finish]
  | cons b w ih =>
    have hb : nextHeight h b≤h+1 := by cases b <;> simp [nextHeight]; omega
    rw [finish,List.length_cons]
    have := ih (nextHeight h b)
    omega

theorem transfer_expand (m h : ℕ) (f : ℕ → ℕ[X]) :
    transfer X m h f=∑ t ∈ Finset.range (h+m+1), kernel m h t*f t := by
  simp only [kernel,transfer_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  have ht : finish h w∈Finset.range (h+m+1) := by
    have := finish_le h w; have := mem_words.mp hw
    apply Finset.mem_range.mpr; omega
  by_cases ok : BallotFrom h w
  · simp only [ite_eq_left ok,mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
    symm
    exact Finset.sum_eq_single_of_mem (finish h w) ht (by intro t _ hn; simp [Ne.symm hn]) |>.trans (by simp)
  · simp [ok]

theorem transfer_cutoff {m e : ℕ} (block : ∀ h t, ReflectedCoeffs (kernel m h t) e)
    {f : ℕ → ℕ[X]} {v : ℤ} (ends : ∀ t, IntervalDecomposition (f t) v) (h : ℕ) :
    IntervalDecomposition (transfer X m h f) ((e:ℤ)+v) := by
  rw [transfer_expand]
  apply IntervalDecomposition.range
  intro t _
  exact (intervalDecomposition_of_reflected (block h t)).mul (ends t)

theorem transfer_blocks {m e : ℕ} (block : ∀ h t, ReflectedCoeffs (kernel m h t) e)
    (k r h : ℕ) (f : ℕ → ℕ[X]) :
    IntervalDecomposition (transfer X (k*m+r) h f) ((k*e:ℕ):ℤ) := by
  induction k generalizing h with
  | zero =>
    simp only [Nat.zero_mul,Nat.cast_zero,Nat.zero_add]
    apply intervalDecomposition_of_reflected (e:=0)
    intro i j hij hcut
    omega
  | succ k ih =>
    rw [show (k+1)*m+r=m+(k*m+r) by ring,transfer_add]
    have H := transfer_cutoff block ih h
    convert H using 1; push_cast; ring

end CentralUnimodality.HeightBlock
