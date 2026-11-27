module

public import CentralUnimodality.SupportSamples
public import CentralUnimodality.CellMoments

/-! Interval arithmetic for the exponent support of the triangular
moment recurrence and the endpoint-power transformation. -/
@[expose] public section

namespace CentralUnimodality.Laurent.Span

def sumBoxes (A : ℕ → Span) : ℕ → Span
  | 0 => .empty
  | n+1 => hull (sumBoxes A n) (A n)

theorem sum_boxes {A : ℕ → Span} {P : ℕ → Laurent} (h : ∀ i, (A i).covers (P i)) (r : ℕ) :
    (sumBoxes A r).covers (sumRange P r) := by
  induction r with
  | zero => exact nil _
  | succ r ih => exact add_hull ih (h r)

theorem scale_zero {p : Laurent} {I : Span} (h : I.covers p) (c : ℚ) : I.covers (scaleShift c 0 p) := by
  have ht := scale_covers h c 0
  cases I <;> simpa [shifted] using ht

def derivatives : ℕ → Span → Span
  | 0,I => I
  | r+1,I => (derivatives r I).derivative

theorem divided_box {p : Laurent} {I : Span} (h : I.covers p) (b : MomentBase) (d r : ℕ) :
    (derivatives r I).covers (b.divided d p r) := by
  induction r with
  | zero => exact h
  | succ r ih => exact scale_zero (base_euler ih b) _

theorem translate_box {p : Laurent} {I : Span} (h : I.covers p) (b : ℚ) (r : ℕ) :
    (derivatives r I).covers (translate b p r) := by
  induction r with
  | zero => exact h
  | succ r ih =>
    apply add_same (scale_zero (euler_covers ih) _)
    apply scale_zero
    apply monotone ih
    intro k hk
    simpa using derivative_contains_zero hk
where
  derivative_contains_zero {J : Span} {k : ℤ} (hk : J.contains k) : J.derivative.contains k := by
    cases J <;> simp_all [contains,derivative]; omega

def convBox (A B : ℕ → Span) (r : ℕ) := sumBoxes (fun i => product (A i) (B (r-i))) (r+1)
def shiftBox (A : ℕ → Span) (r : ℕ) := sumBoxes (fun i => derivatives i (A (r-i))) (r+1)
def expBox (A : ℕ → Span) (r : ℕ) := sumBoxes (fun i => A (r-i)) (r+1)

theorem conv_box {A B : ℕ → Span} {P Q : ℕ → Laurent} (h : ∀ i, (A i).covers (P i))
    (h' : ∀ i, (B i).covers (Q i)) (r : ℕ) :
    (convBox A B r).covers (convolution P Q r) := sum_boxes (fun i => product_covers (h i) (h' _)) _

theorem shift_box {A : ℕ → Span} {P : ℕ → Laurent} (h : ∀ i, (A i).covers (P i)) (b : MomentBase) (d r : ℕ) :
    (shiftBox A r).covers (CentralUnimodality.Laurent.shifted b d P r) := sum_boxes (fun i => divided_box (h _) b d i) _

theorem exp_box {A : ℕ → Span} {P : ℕ → Laurent} (h : ∀ i, (A i).covers (P i)) (r : ℕ) :
    (expBox A r).covers (exponential P r) := sum_boxes (fun _ => scale_zero (h _) _) _

def unitBox : ℕ → Span
  | 0 => .interval 0 1
  | _+1 => .empty

private theorem unit_box (r : ℕ) : (unitBox r).covers (unitColumn alpha r) := by
  cases r with
  | zero => simp [covers,unitBox,unitColumn,alpha,contains]
  | succ r => exact nil _

def dBox (A : ℕ → Span) (r : ℕ) :=
  hull (unitBox r) (product (.interval 0 1) (convBox A (shiftBox A) r))

def bBox (A B : ℕ → Span) (r : ℕ) :=
  hull ((A r).shifted 1) (expBox (convBox (fun i => hull (A i) (unitBox i)) (shiftBox B)) r)

private theorem dyck_box {A : ℕ → Span} {P : ℕ → Laurent} (h : ∀ i, (A i).covers (P i)) (r : ℕ) :
    (dBox A r).covers (dyckRhs P r) := by
  apply add_hull (unit_box r)
  apply product_covers _ (conv_box h (shift_box h .dyck 1) r)
  simp [covers,beta,contains]

private theorem ballot_box {A B : ℕ → Span} {P Q : ℕ → Laurent} (h : ∀ i, (A i).covers (P i))
    (h' : ∀ i, (B i).covers (Q i)) (r : ℕ) : (bBox A B r).covers (ballotRhs P Q r) :=
  add_hull (scale_covers (h r) 1 1) (exp_box (conv_box
    (fun i => add_hull (h i) (scale_zero (unit_box i) _)) (shift_box h' .ballot 2)) r)

def boxAt (A : Array Span) (i : ℕ) := A[i]?.getD .empty

def tableBoxes : ℕ → Array Span × Array Span
  | 0 => (#[.interval 0 0],#[.interval 0 0])
  | n+1 =>
    let (D,B) := tableBoxes n
    let D' := D.push ((dBox (boxAt D) (n+1)).shifted (-1))
    (D',B.push ((bBox (boxAt D') (boxAt B) (n+1)).shifted (-1)))

private def boxes (A : Array Span) (P : Array Laurent) :=
  A.size = P.size ∧ ∀ i, (boxAt A i).covers (lookup P i)

private theorem boxes_push {A : Array Span} {P : Array Laurent} (h : boxes A P) {I : Span} {p : Laurent}
    (hp : I.covers p) : boxes (A.push I) (P.push p) := by
  obtain ⟨hsize,hs⟩ := h
  refine ⟨by simpa using hsize,?_⟩
  intro i
  rcases lt_trichotomy i A.size with hi|rfl|hi
  · simpa only [boxAt,lookup,Array.getElem?_push_lt hi,Array.getElem?_push_lt (hsize ▸ hi),getElem?_pos A i hi,getElem?_pos P i (hsize ▸ hi)] using hs i
  · rw [boxAt,lookup,Array.getElem?_push_size,hsize,Array.getElem?_push_size]
    exact hp
  · have ha : (A.push I).size ≤ i := by simp; omega
    have hq : (P.push p).size ≤ i := by simp; omega
    rw [boxAt,lookup,Array.getElem?_eq_none ha,Array.getElem?_eq_none hq]
    exact nil _

private theorem boxes_exact (m : ℕ) :
    boxes (tableBoxes m).1 (tables m).1 ∧ boxes (tableBoxes m).2 (tables m).2 := by
  induction m with
  | zero =>
    have hc : boxes #[Span.interval 0 0] #[[(0,1)]] := by
      refine ⟨rfl,?_⟩
      intro i
      cases i <;> simp [boxAt,lookup,covers,contains]
    exact ⟨hc,hc⟩
  | succ m ih =>
    obtain ⟨hD,hB⟩ := ih
    have hD' := boxes_push hD (scale_covers (dyck_box hD.2 (m+1)) 1 (-1))
    exact ⟨hD',boxes_push hB (scale_covers (ballot_box hD'.2 hB.2 (m+1)) 1 (-1))⟩

def rawBox (D B : ℕ → Span) (δ r : ℕ) : Span :=
  if δ = 0 then (B r).shifted (-1)
  else let O := convBox D (shiftBox B) r
       hull (O.shifted (-1)) O

theorem raw_box (m δ j : ℕ) :
    (rawBox (boxAt (tableBoxes m).1) (boxAt (tableBoxes m).2) δ j).covers
    (rawNumerator (lookup (tables m).1) (lookup (tables m).2) δ j) := by
  obtain ⟨hD,hB⟩ := boxes_exact m
  unfold rawBox rawNumerator
  apply scale_zero
  split
  · exact scale_covers (hB.2 j) _ _
  · have ho := conv_box hD.2 (shift_box hB.2 .ballot 1) j
    exact add_hull (scale_covers ho _ _) (scale_zero ho _)

def cellBox (P : ℕ → Span) (r : ℕ) :=
  sumBoxes (fun j => derivatives (r+1-j) (P j)) (r+1)

theorem cell_box {A : ℕ → Span} {P : ℕ → Laurent} (h : ∀ j, (A j).covers (P j)) (b : ℚ) (r : ℕ) :
    (cellBox A r).covers (cellNumerator b P r) := by
  apply scale_zero
  apply sum_boxes
  intro j
  exact scale_zero (add_same (translate_box (h j) (b+1) _) (scale_zero (translate_box (h j) b _) _)) _

end CentralUnimodality.Laurent.Span
