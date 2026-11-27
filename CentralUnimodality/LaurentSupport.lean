module

public import CentralUnimodality.MomentDetermination

/-! Track only the exponent interval of a Laurent expression. These
operations can bound the number of samples needed for finite determination
without reducing any large rational coefficients. -/
@[expose] public section

namespace CentralUnimodality.Laurent

inductive Span where
  | empty
  | interval (lo hi : ℤ)
  deriving DecidableEq,Repr,Inhabited

namespace Span

def contains : Span → ℤ → Prop
  | .empty,_ => False
  | .interval a b,h => a ≤ h ∧ h ≤ b

def covers (I : Span) (p : Laurent) := ∀ t ∈ p, I.contains t.1

def hull : Span → Span → Span
  | .empty,J => J
  | I,.empty => I
  | .interval a b,.interval c d => .interval (min a c) (max b d)

def shifted : Span → ℤ → Span
  | .empty,_ => .empty
  | .interval a b,h => .interval (h+a) (h+b)

def product : Span → Span → Span
  | .interval a b,.interval c d => .interval (a+c) (b+d)
  | _,_ => .empty

theorem left_hull {I J : Span} {h : ℤ} (hh : I.contains h) : (hull I J).contains h := by
  cases I <;> cases J <;> simp_all [contains,hull]

theorem right_hull {I J : Span} {h : ℤ} (hh : J.contains h) : (hull I J).contains h := by
  cases I <;> cases J <;> simp_all [contains,hull]

theorem contains_shift {I : Span} {h : ℤ} (hh : I.contains h) (s : ℤ) :
    (shifted I s).contains (s+h) := by
  cases I <;> simp_all [contains,shifted]

theorem contains_product {I J : Span} {h j : ℤ} (hh : I.contains h) (hj : J.contains j) :
    (product I J).contains (h+j) := by
  cases I <;> cases J <;> simp_all [contains,product]
  omega

theorem nil (I : Span) : I.covers [] := by simp [covers]

theorem monotone {I J : Span} {p : Laurent} (hp : I.covers p)
    (h : ∀ k, I.contains k → J.contains k) : J.covers p := fun t ht => h _ (hp t ht)

theorem cons {I : Span} {p : Laurent} {h : ℤ} {c : ℚ} (hp : I.covers p) (hh : I.contains h) :
    I.covers ((h,c)::p) := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl|ht
  · exact hh
  · exact hp _ ht

theorem of_tail {I : Span} {t : ℤ × ℚ} {p : Laurent} (hp : I.covers (t::p)) :
    I.covers p := fun z hz => hp z (List.mem_cons_of_mem _ hz)

theorem insert_covers {I : Span} (p : Laurent) {h : ℤ} (c : ℚ) (hp : I.covers p)
    (hh : I.contains h) : I.covers (insert h c p) := by
  induction p with
  | nil => simp only [insert]; split <;> first | exact nil _ | exact cons (nil _) hh
  | cons t p ih =>
    obtain ⟨k,b⟩ := t
    have hk := hp _ List.mem_cons_self
    have ht := of_tail hp
    simp only [insert]
    split
    · exact hp
    split
    · exact cons hp hh
    split
    · split <;> first | exact ht | exact cons ht hk
    · exact cons (ih ht) hk

theorem add_same {I : Span} {p q : Laurent} (hp : I.covers p) (hq : I.covers q) :
    I.covers (add p q) := by
  induction p with
  | nil => exact hq
  | cons t p ih =>
    exact insert_covers _ _ (ih (of_tail hp)) (hp _ List.mem_cons_self)

theorem add_hull {I J : Span} {p q : Laurent} (hp : I.covers p) (hq : J.covers q) :
    (hull I J).covers (add p q) :=
  add_same (monotone hp (fun _ => left_hull)) (monotone hq (fun _ => right_hull))

theorem scale_covers {I : Span} {p : Laurent} (hp : I.covers p) (c : ℚ) (s : ℤ) :
    (I.shifted s).covers (scaleShift c s p) := by
  intro t ht
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
  exact contains_shift (hp _ hz) s

theorem product_covers {I J : Span} {p q : Laurent} (hp : I.covers p) (hq : J.covers q) :
    (product I J).covers (mul p q) := by
  induction p with
  | nil => exact nil _
  | cons t p ih =>
    obtain ⟨h,c⟩ := t
    apply add_same _ (ih (of_tail hp))
    intro z hz
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
    exact contains_product (hp _ List.mem_cons_self) (hq _ hy)

def derivative : Span → Span
  | .empty => .empty
  | .interval a b => .interval (a-2) b

private theorem derivative_contains {I : Span} {h : ℤ} (hh : I.contains h) {s : ℤ}
    (hs : -2 ≤ s) (hs' : s ≤ 0) : I.derivative.contains (s+h) := by
  cases I <;> simp_all [contains,derivative]
  omega

theorem euler_covers {I : Span} {p : Laurent} (hp : I.covers p) : I.derivative.covers (euler p) := by
  induction p with
  | nil => exact nil _
  | cons t p ih =>
    obtain ⟨h,c⟩ := t
    have hh := hp _ List.mem_cons_self
    apply insert_covers _ _ (insert_covers _ _ (ih (of_tail hp)) _)
    · simpa using derivative_contains hh (s := 0) (by decide) (by decide)
    · rw [show h-2 = -2+h by ring]
      exact derivative_contains hh (by decide) (by decide)

theorem base_euler {I : Span} {p : Laurent} (hp : I.covers p) (b : MomentBase) :
    I.derivative.covers (b.euler p) := by
  apply add_same (euler_covers hp)
  apply add_same <;> intro z hz <;> obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
  · exact derivative_contains (hp _ hy) (by cases b <;> decide) (by cases b <;> decide)
  · exact derivative_contains (hp _ hy) (by decide) (by decide)

end Span

end CentralUnimodality.Laurent
