module

public import CentralUnimodality.LaurentSupport
public import Mathlib.Data.Int.Interval

/-! Turn an exponent interval into an explicit bound on the number of
consecutive size coefficients that determine two Laurent formulas. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

private def atExponent (h : ℤ) : Laurent → ℚ
  | [] => 0
  | (k,c)::p => (if h = k then c else 0) + atExponent h p

private def grouped (keys : List ℤ) (p : Laurent) : Laurent :=
  keys.map fun h => (h,atExponent h p)

private theorem grouped_nil (keys : List ℤ) : eval (grouped keys []) = 0 := by
  induction keys with
  | nil => rfl
  | cons h keys ih => change C (0:ℚ)*rootPower h+eval (grouped keys []) = 0; simp [ih]

private theorem grouped_cons (keys : List ℤ) (hd : keys.Nodup) (h : ℤ) (c : ℚ) (p : Laurent) :
    eval (grouped keys ((h,c)::p)) =
      (if h ∈ keys then C c*rootPower h else 0) + eval (grouped keys p) := by
  induction keys with
  | nil => simp [grouped,eval]
  | cons k keys ih =>
    change C ((if k = h then c else 0) + atExponent k p)*rootPower k +
      eval (grouped keys ((h,c)::p)) =
      (if h ∈ k::keys then C c*rootPower h else 0) +
      (C (atExponent k p)*rootPower k + eval (grouped keys p))
    rw [ih hd.tail,map_add,add_mul]
    simp only [List.mem_cons]
    by_cases hk : k = h
    · subst h
      simp [List.nodup_cons.mp hd |>.1,add_assoc]
    · by_cases hm : h ∈ keys <;> simp [hk,Ne.symm hk,hm]; ring

private theorem grouped_exact (keys : List ℤ) (hd : keys.Nodup) (p : Laurent)
    (hc : ∀ t ∈ p, t.1 ∈ keys) : eval (grouped keys p) = eval p := by
  induction p with
  | nil => exact grouped_nil keys
  | cons t p ih =>
    obtain ⟨h,c⟩ := t
    rw [grouped_cons keys hd,ite_eq_left (hc _ List.mem_cons_self),ih (fun t ht => hc t (List.mem_cons_of_mem _ ht)),eval]

theorem compare_on_span {a b : ℤ} (p q : Laurent) (hp : (Span.interval a b).covers p)
    (hq : (Span.interval a b).covers q) (N : ℕ)
    (h : ∀ n < (b+1-a).toNat, coeff (N+n) (eval p) = coeff (N+n) (eval q)) :
    ∀ n, coeff (N+n) (eval p) = coeff (N+n) (eval q) := by
  let d := add p (scaleShift (-1) 0 q)
  have he : eval d = eval p-eval q := by simp [d,eval_add,eval_scaleShift,rootPower_zero,sub_eq_add_neg]
  have hs : (Span.interval a b).covers d := by
    apply Span.add_same hp
    simpa [Span.shifted] using Span.scale_covers hq (-1) 0
  let keys := (Finset.Icc a b).toList
  have hd := grouped_exact keys (Finset.nodup_toList _) d (by
    intro t ht
    simpa [keys,Span.contains] using hs t ht)
  have hlen : (grouped keys d).length = (b+1-a).toNat := by
    simp [grouped,keys,Int.card_Icc]
  have hall := coeff_zero_from_block (grouped keys d) N (by
    intro n hn
    rw [hd,he,map_sub,h n (by simpa [hlen] using hn),sub_self])
  intro n
  have hh := hall n
  rw [hd,he,map_sub,sub_eq_zero] at hh
  exact hh

end CentralUnimodality.Laurent
