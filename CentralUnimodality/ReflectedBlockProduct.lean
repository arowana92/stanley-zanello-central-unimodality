module

public import CentralUnimodality.ReflectedIntervals

/-! Reflected coefficient cutoffs add under multiplication. The interval
product identity strips off its outermost symmetric chain at each step. -/
@[expose] public section

namespace CentralUnimodality
open Polynomial

theorem IntervalDecomposition.weaken {P : ℕ[X]} {e f : ℤ} (h : IntervalDecomposition P e)
    (hf : f≤e) : IntervalDecomposition P f := by
  obtain ⟨L,he,hL⟩ := h
  exact ⟨L,he,fun t ht => hf.trans (hL t ht)⟩

private theorem int_last (a w : ℕ) :
    intervalPoly a (w+1)=intervalPoly a w+X^(a+w+1) := by
  rw [intervalPoly,Finset.sum_range_succ,intervalPoly,Nat.add_assoc]

private theorem int_first (a w : ℕ) :
    intervalPoly a (w+1)=X^a+intervalPoly (a+1) w := by
  rw [intervalPoly,Finset.sum_range_succ',intervalPoly,add_comm]
  simp only [Nat.add_zero]
  apply congrArg (X^a+·)
  apply Finset.sum_congr rfl
  intro i _
  rw [show a+(i+1)=a+1+i by omega]

private theorem int_join (a w v : ℕ) :
    intervalPoly a w + intervalPoly (a+w+1) v=intervalPoly a (w+1+v) := by
  unfold intervalPoly
  conv_rhs => rw [show w+1+v+1=(w+1)+(v+1) by omega,Finset.sum_range_add]
  apply congrArg₂ (·+·) rfl
  apply Finset.sum_congr rfl
  intro i _
  rw [show a+(w+1+i)=a+w+1+i by omega]

private theorem int_product (a w b v : ℕ) :
    IntervalDecomposition (intervalPoly a w*intervalPoly b v) (2*(a:ℤ)+w+2*b+v) := by
  induction w generalizing a b v with
  | zero =>
    rw [show intervalPoly a 0=(X:ℕ[X])^a by simp [intervalPoly],intervalPoly_shift]
    apply IntervalDecomposition.single
    push_cast; omega
  | succ w ih =>
    cases v with
    | zero =>
      rw [show intervalPoly b 0=(X:ℕ[X])^b by simp [intervalPoly],mul_comm,intervalPoly_shift]
      apply IntervalDecomposition.single
      push_cast; omega
    | succ v =>
      have eq : intervalPoly a (w+1)*intervalPoly b (v+1)=
          intervalPoly (b+a) (w+1+(v+1)) + intervalPoly a w*intervalPoly (b+1) v := by
        calc _ = intervalPoly a w*intervalPoly b (v+1) +
                X^(a+w+1)*intervalPoly b (v+1) := by rw [int_last a w,add_mul]
             _ = (intervalPoly (b+a) w + intervalPoly (a+w+1+b) (v+1)) +
                intervalPoly a w*intervalPoly (b+1) v := by
                  rw [int_first b v,mul_add,mul_comm _ (X^b),intervalPoly_shift,
                    ← int_first b v,intervalPoly_shift]
                  ac_rfl
             _ = _ := by rw [show a+w+1+b=b+a+w+1 by omega,int_join]
      rw [eq]
      apply IntervalDecomposition.add
      · apply IntervalDecomposition.single
        push_cast; omega
      · apply (ih a (b+1) v).weaken
        push_cast; omega

theorem IntervalDecomposition.mul {P Q : ℕ[X]} {e f : ℤ} (hp : IntervalDecomposition P e)
    (hq : IntervalDecomposition Q f) : IntervalDecomposition (P*Q) (e+f) := by
  obtain ⟨L,rfl,hL⟩ := hp
  induction L with
  | nil => simpa using IntervalDecomposition.zero (e+f)
  | cons t L ih =>
    simp only [List.map_cons,List.sum_cons,add_mul]
    apply IntervalDecomposition.add _ (ih (fun p hp => hL p (List.mem_cons_of_mem _ hp)))
    clear ih
    obtain ⟨M,rfl,hM⟩ := hq
    induction M with
    | nil => simp only [List.map_nil,List.sum_nil,mul_zero]; exact .zero _
    | cons s M ihM =>
      simp only [List.map_cons,List.sum_cons,mul_add]
      apply IntervalDecomposition.add _ (ihM (fun p hp => hM p (List.mem_cons_of_mem _ hp)))
      apply (int_product t.1 t.2 s.1 s.2).weaken
      have H := hL t List.mem_cons_self
      have K := hM s List.mem_cons_self
      omega

end CentralUnimodality
