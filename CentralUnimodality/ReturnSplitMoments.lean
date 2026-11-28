module

public import CentralUnimodality.ReturnSplitQuadrature

/-! Exact polynomial integration under the discrete split law. In the
binomial-coefficient basis its a-th moment is choose(N,a) r_a. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

private theorem delete_choose (k a : ℕ) :
    (k:ℝ)*((k-1).choose a:ℕ)=((k:ℝ)-a)*(k.choose a:ℕ) := by
  by_cases h : k<a
  · rw [Nat.choose_eq_zero_of_lt h,Nat.choose_eq_zero_of_lt (by omega : k-1<a)]; simp
  cases k with
  | zero =>
    have h₀ : a=0 := by omega
    subst a; simp
  | succ k =>
    rw [Nat.add_sub_cancel]
    have H := Nat.choose_mul_succ_eq k a
    have hle : a≤k+1 := by omega
    have R : (k.choose a:ℝ)*(k+1) = ((k+1).choose a:ℝ)*((k:ℝ)+1-a) := by
      exact_mod_cast H
    push_cast
    linarith only [R]

private def splitChoose (N a b k : ℕ) : ℝ :=
  (k.choose a:ℝ)*((N-k).choose b:ℝ)

private theorem split_choose_zero {N a b k : ℕ} (h : k<a ∨ N-k<b) :
    splitChoose N a b k=0 := by
  rcases h with h|h <;> simp [splitChoose,Nat.choose_eq_zero_of_lt h]

private theorem initial_split_choose (a b : ℕ) :
    average (a+b) (splitChoose (a+b) a b)=survival a*survival b := by
  unfold average
  rw [Finset.sum_eq_single a]
  · simp [splitChoose,weight]
  · intro k hk hne
    have h := Finset.mem_range.mp hk
    rw [split_choose_zero (by omega),mul_zero]
  · simp

private theorem split_delete (N a b k : ℕ) (hk : k≤N+1) :
    ((N:ℝ)+1-k)*splitChoose N a b k+k*splitChoose N a b (k-1)=
      ((N:ℝ)+1-a-b)*splitChoose (N+1) a b k := by
  let L := N+1-k
  have hL : (L:ℝ)=(N:ℝ)+1-k := by
    dsimp [L]; rw [Nat.cast_sub hk,Nat.cast_succ]
  have h₁ : N-k=L-1 := by dsimp [L]; omega
  have h₂ : (k:ℝ)*((k-1).choose a:ℝ)*((N-(k-1)).choose b:ℝ)=
      (k:ℝ)*((k-1).choose a:ℝ)*(L.choose b:ℝ) := by
    cases k with
    | zero => simp
    | succ k => rw [show N-(k+1-1)=L by dsimp [L]; omega]
  simp only [splitChoose]
  rw [← hL,h₁,mul_left_comm (L:ℝ),delete_choose L b,← mul_assoc (k:ℝ),h₂,delete_choose k a,hL]
  dsimp [L]
  ring

/-- Both pieces may carry a polynomial factor. The split average becomes
ordinary convolution of their binomial-basis coefficients. -/
theorem mixed_binomial_moment (N a b : ℕ) :
    average N (fun k => (k.choose a:ℝ)*((N-k).choose b:ℝ)) =
      (N.choose (a+b):ℝ)*survival a*survival b := by
  change average N (splitChoose N a b)=_
  by_cases ha : a+b≤N
  · induction N, ha using Nat.le_induction with
    | base => simp [initial_split_choose]
    | succ N hN ih =>
      have H := deletion N (splitChoose N a b)
      have repl : average (N+1) (fun k =>
          ((N:ℝ)+1-k)*splitChoose N a b k+k*splitChoose N a b (k-1))=
          ((N:ℝ)+1-a-b)*average (N+1) (splitChoose (N+1) a b) := by
        rw [← average_mul]
        exact average_congr (split_delete N a b)
      rw [repl,ih] at H
      have R : (N.choose (a+b):ℝ)*(N+1)=
          ((N+1).choose (a+b):ℝ)*((N:ℝ)+1-a-b) := by
        have eq := congrArg (fun i : ℕ => (i:ℝ)) (Nat.choose_mul_succ_eq N (a+b))
        push_cast [Nat.cast_sub (by omega : a+b≤N+1)] at eq
        linarith only [eq]
      have pos : (0:ℝ)<(N:ℝ)+1-a-b := by
        have x : (a:ℝ)+b≤N := by exact_mod_cast hN
        linarith
      apply mul_left_cancel₀ pos.ne'
      linear_combination survival a*survival b*R-H
  · rw [Nat.choose_eq_zero_of_lt (by omega : N<a+b),Nat.cast_zero,zero_mul,zero_mul,
      ← average_const N 0]
    exact average_congr (fun k hk => split_choose_zero (by omega))

theorem binomial_moment (N a : ℕ) :
    average N (fun k => (k.choose a:ℝ)) = (N.choose a:ℝ)*survival a := by
  simpa [survival] using mixed_binomial_moment N a 0

end CentralUnimodality.ReturnSplit
