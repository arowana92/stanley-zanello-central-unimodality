module

public import CentralUnimodality.CurveAlternants

/-! The area and dinv entries of the literal Dyck walks supply the exponent
pairs for curve evaluation. Their total orders fit the staircase slots. -/
@[expose] public section

namespace CentralUnimodality.Polarization
variable {n : ℕ}

def inversionsFrom (a : Fin n → ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => i < j ∧ (a j=a i ∨ a j+1=a i)

def dinvEntry (a : Fin n → ℕ) (i : Fin n) := (inversionsFrom a i).card

private theorem count_values (a : Fin n → ℕ) (v : ℕ) :
    (List.ofFn a).count v = ∑ i, if a i=v then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.count_cons,Fin.sum_univ_succ,ih]
    by_cases he : a 0=v
    · simp [he,add_comm]
    · simp [he]

theorem sum_dinvEntry (a : Fin n → ℕ) :
    ∑ i, dinvEntry a i = diagonalInversions (List.ofFn a) := by
  induction n with
  | zero => simp [diagonalInversions]
  | succ n ih =>
    let v := fun i : Fin n => a i.succ
    have tail (i : Fin n) : dinvEntry a i.succ = dinvEntry v i := by
      unfold dinvEntry inversionsFrom
      rw [Finset.card_filter,Finset.card_filter,Fin.sum_univ_succ]
      simp [v]
    rw [Fin.sum_univ_succ,List.ofFn_succ,diagonalInversions]
    simp_rw [tail]
    rw [ih]
    congr 1
    unfold dinvEntry inversionsFrom
    rw [Finset.card_filter,Fin.sum_univ_succ,count_values]
    by_cases h : a 0=0
    · simp [h]
    · simp only [h,ite_false,count_values,← Finset.sum_add_distrib]
      simp only [lt_self_iff_false,false_and,ite_false,zero_add,Fin.succ_pos,true_and]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> omega

/-- Every height below a later up-step has already occurred at an up-step,
starting from the initial height. -/
private theorem earlier_heights (w : List Bool) (h : ℕ) (p q : List ℕ) (a : ℕ)
    (he : upHeights h w = p++a::q) (b : ℕ) (hb : h ≤ b) (hba : b < a) : b ∈ p := by
  induction w generalizing h p with
  | nil => simp [upHeights] at he
  | cons v w ih =>
    cases v with
    | true => exact ih (h-1) p he (by omega)
    | false =>
      cases p with
      | nil => simp [upHeights] at he; omega
      | cons x p =>
        simp only [upHeights,List.cons_append,List.cons.injEq] at he
        rcases he with ⟨rfl,he⟩
        by_cases hx : b=h
        · simp [hx]
        · exact List.mem_cons_of_mem _ (ih (h+1) p he (by omega))

def dyckAreaEntry {w : List Bool} (hw : w ∈ dycks n) (i : Fin n) : ℕ :=
  (upHeights 0 w)[i.val]'(by rw [(dyck_up_heights hw).1]; exact i.isLt)

theorem areaEntry_word {w : List Bool} (hw : w ∈ dycks n) :
    List.ofFn (dyckAreaEntry hw) = upHeights 0 w := by
  apply List.ext_getElem
  · simp [(dyck_up_heights hw).1]
  · intro i _ _; simp [dyckAreaEntry]

theorem areaEntry_previous {w : List Bool} (hw : w ∈ dycks n) (i : Fin n) {b : ℕ}
    (hb : b < dyckAreaEntry hw i) : ∃ j < i, dyckAreaEntry hw j = b := by
  let word := upHeights 0 w
  have hi : i.val < word.length := by dsimp [word]; rw [(dyck_up_heights hw).1]; exact i.isLt
  have h := List.take_append_drop i.val word
  rw [List.drop_eq_getElem_cons hi] at h
  have hm := earlier_heights w 0 (word.take i.val) _ _ h.symm b (Nat.zero_le _) hb
  obtain ⟨j,hj,hb'⟩ := List.mem_iff_getElem.mp hm
  rw [List.getElem_take] at hb'
  simp only [List.length_take,lt_min_iff] at hj
  exact ⟨⟨j,lt_trans hj.1 i.isLt⟩,hj.1,hb'⟩

/-- A permutation of slots 0,...,n-1 dominates the row orders. -/
def FitsSlots (s : Fin n → ℕ) : Prop := ∃ σ : Perm n, ∀ i, s i ≤ (σ i:ℕ)

private def before (a : Fin n → ℕ) (i : Fin n) :=
  Finset.univ.filter fun j => a j < a i ∨ (a j=a i ∧ i < j)

private theorem before_lt (a : Fin n → ℕ) {i j : Fin n} (h : a i < a j ∨ a i=a j ∧ j < i) :
    (before a i).card < (before a j).card := by
  apply Finset.card_lt_card
  have sub : before a i ⊆ before a j := by
    intro k hk
    simp [before] at hk ⊢
    omega
  apply (Finset.ssubset_iff_of_subset sub).mpr
  exact ⟨i,by simpa [before] using h,by simp [before]⟩

theorem area_orders_fit (a : Fin n → ℕ) (hprev : ∀ i b, b < a i → ∃ j < i, a j=b) :
    FitsSlots (fun i => a i+dinvEntry a i) := by
  let r : Fin n → Fin n := fun i => ⟨(before a i).card,by
    apply lt_of_lt_of_eq _ (Finset.card_fin n)
    apply Finset.card_lt_card
    exact (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mpr
      ⟨i,Finset.mem_univ _,by simp [before]⟩⟩
  have hinj : Function.Injective r := by
    intro i j h
    have he := congrArg Fin.val h
    change (before a i).card = (before a j).card at he
    by_contra hne
    rcases (show (a i < a j ∨ a i=a j ∧ j < i) ∨ (a j < a i ∨ a j=a i ∧ i < j) by omega) with h|h
    · exact (before_lt a h).ne he
    · exact (before_lt a h).ne he.symm
  refine ⟨Equiv.ofBijective r (Finite.injective_iff_bijective.mp hinj),?_⟩
  intro i
  let E := Finset.univ.filter (fun j => j < i ∧ a j < a i)
  have cover : Finset.range (a i) ⊆ E.image a := by
    intro b hb
    obtain ⟨j,hj,rfl⟩ := hprev i b (Finset.mem_range.mp hb)
    exact Finset.mem_image.mpr ⟨j,by simpa [E] using And.intro hj (Finset.mem_range.mp hb),rfl⟩
  have hc : a i ≤ E.card := by simpa using (Finset.card_le_card cover).trans Finset.card_image_le
  have hd : Disjoint E (inversionsFrom a i) := by
    rw [Finset.disjoint_left]
    intro j hj h
    simp [E] at hj
    simp [inversionsFrom] at h
    omega
  have sub : E ∪ inversionsFrom a i ⊆ before a i := by
    intro j hj
    simp [E,inversionsFrom,before] at hj ⊢
    omega
  have hn := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint hd] at hn
  change a i+(inversionsFrom a i).card ≤ (before a i).card
  omega

theorem entry_pairs_injective (a : Fin n → ℕ) :
    Function.Injective (fun i => (a i+dinvEntry a i,a i)) := by
  have strict {i j : Fin n} (hij : i < j) (he : a i=a j) : dinvEntry a j < dinvEntry a i := by
    apply Finset.card_lt_card
    have sub : inversionsFrom a j ⊆ inversionsFrom a i := by
      intro k hk
      simp [inversionsFrom] at hk ⊢
      exact ⟨lt_trans hij hk.1,he ▸ hk.2⟩
    exact (Finset.ssubset_iff_of_subset sub).mpr
      ⟨j,by simp [inversionsFrom,hij,he],by simp [inversionsFrom]⟩
  intro i j h
  have he := congrArg Prod.snd h
  have hs := congrArg Prod.fst h
  simp only at he hs
  rcases lt_trichotomy i j with h|h|h
  · have := strict h he; omega
  · exact h
  · have := strict h he.symm; omega

theorem dyck_orders_fit {w : List Bool} (hw : w ∈ dycks n) :
    FitsSlots (fun i => dyckAreaEntry hw i+dinvEntry (dyckAreaEntry hw) i) :=
  area_orders_fit _ (fun i _ h => areaEntry_previous hw i h)

noncomputable def dyckClass {w : List Bool} (hw : w ∈ dycks n) : Poly n ⧸ relations n :=
  (relations n).mkQ (alternant (dyckAreaEntry hw) (dinvEntry (dyckAreaEntry hw)))

theorem dyckClass_bidegree {w : List Bool} (hw : w ∈ dycks n) :
    dyckClass hw ∈ coinvariantSpace n (dyckTotalDegree w) (walkCorank w) := by
  have h := alternant_class_mem (dyckAreaEntry hw) (dinvEntry (dyckAreaEntry hw))
  rw [sum_dinvEntry,← List.sum_ofFn,areaEntry_word,(dyck_up_heights hw).2] at h
  exact h

end CentralUnimodality.Polarization
