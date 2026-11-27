module

public import CentralUnimodality.FirstHitCount
public import CentralUnimodality.DyckRecurrence

/-! The exact law of a uniformly marked vertex in an ordinary excursion.
Insert an up-step at the mark and reverse the traversal of the suffix. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion

/-- Both endpoint vertices are among the possible marks. -/
def marks (d : ℕ) := dycks d ×ˢ Finset.range (2*d+1)

def height (p : List Bool × ℕ) : ℤ := displacement (p.1.take p.2)

def tail (d b : ℕ) := (marks d).filter (fun p => (b:ℤ) ≤ height p)

private def unfoldMark (p : List Bool × ℕ) : List Bool :=
  p.1.take p.2 ++ false :: reverseWalk (p.1.drop p.2)

private theorem joined_ballot (u v : List Bool) :
    BallotFrom 0 (u ++ v) ↔ BallotFrom 0 u ∧ ∀ y ∈ heights (displacement u) v, 0 ≤ y := by
  simp only [ballot_iff_heights, Nat.cast_zero, heights_append, zero_add, List.forall_mem_append]

private theorem reverse_suffix {u v : List Bool} (hu : 0 ≤ displacement u) (hz : displacement (u++v) = 0) :
    (∀ y ∈ heights (displacement u) v, 0 ≤ y) ↔ BallotFrom 0 (reverseWalk v) := by
  have he : displacement u + displacement v = 0 := displacement_append u v ▸ hz
  have h := reverse_vertices (displacement u) v
  rw [he] at h
  have hr : (∀ y ∈ vertices (displacement u) v, 0 ≤ y) ↔
      ∀ y ∈ vertices 0 (reverseWalk v), 0 ≤ y := by simp [h]
  rw [ballot_iff_heights]
  simp only [vertices,List.forall_mem_cons,le_refl,true_and] at hr
  constructor
  · exact fun hv => hr.mp ⟨hu,hv⟩
  · exact fun hv => (hr.mpr hv).2

private theorem unfold_ballot {u v : List Bool} (hb : BallotFrom 0 u) (hr : BallotFrom 0 v) :
    BallotFrom 0 (u ++ false :: v) := by
  apply (joined_ballot ..).mpr ⟨hb,?_⟩
  have hu := ballot_endpoint_nonneg hb
  have hs : heights (displacement u + 1) v = (heights 0 v).map (displacement u + 1 + ·) := by
    simpa using heights_translate (displacement u+1) 0 v
  simp only [heights,step,List.forall_mem_cons,hs,List.forall_mem_map]
  exact ⟨by omega,fun y hy => by have := (ballot_iff_heights 0 v).mp hr y hy; omega⟩

private theorem last_departure (w : List Bool) (b : ℕ) (hh : (b:ℤ) < displacement w) :
    ∃ u v, w = u ++ false :: v ∧ displacement u = (b:ℤ) ∧ BallotFrom 0 v := by
  induction w using List.reverseRecOn with
  | nil => simp [displacement] at hh; omega
  | append_singleton w a ih =>
    rw [displacement_snoc] at hh
    by_cases he : (b:ℤ) < displacement w
    · obtain ⟨u,v,rfl,hu,hv⟩ := ih he
      refine ⟨u,v++[a],by simp,hu,(ballot_snoc_iff ..).mpr ⟨hv,?_⟩⟩
      rw [displacement_append,hu] at hh
      change _ < _ + (1+displacement v) + _ at hh
      omega
    · cases a with
      | false => exact ⟨w,[],rfl,by dsimp [step] at hh; omega,trivial⟩
      | true => dsimp [step] at hh; omega

private theorem departure_unique {u v u' v' : List Bool}
    (hd : displacement u = displacement u') (hb : BallotFrom 0 v) (hb' : BallotFrom 0 v')
    (he : u++false::v = u'++false::v') : u = u' ∧ v = v' := by
  let z := reverseWalk u
  have hz : displacement (z++u) = 0 := by simp [z,displacement_append,reverseWalk_disp]
  have hz' : displacement (z++u') = 0 := by simpa [displacement_append,← hd] using hz
  have hx := congrArg (fun w => lastSplit (z++w)) he
  change lastSplit (z++(u++false::v)) = lastSplit (z++(u'++false::v')) at hx
  rw [← List.append_assoc,← List.append_assoc,lastSplit_append hz ((noReturn_up_iff v).mpr hb),
    lastSplit_append hz' ((noReturn_up_iff v').mpr hb')] at hx
  exact ⟨(List.append_right_inj z).mp (congrArg Prod.fst hx),(List.cons.inj (congrArg Prod.snd hx)).2⟩

private def highBallots (d b : ℕ) :=
  (ballots (2*d+1)).filter fun w => 2*(b:ℤ)+1 ≤ displacement w

private theorem pieces {p : List Bool × ℕ} {d : ℕ} (hp : p ∈ marks d) :
    let u := p.1.take p.2
    let v := p.1.drop p.2
    u.length = p.2 ∧ u.length + v.length = 2*d ∧ BallotFrom 0 u ∧
      BallotFrom 0 (reverseWalk v) ∧ displacement (reverseWalk v) = displacement u := by
  obtain ⟨hw,ht⟩ := Finset.mem_product.mp hp
  obtain ⟨⟨hl,hb⟩,hz⟩ := mem_dycks.mp hw
  have ht' := Finset.mem_range.mp ht
  dsimp only
  rw [← List.take_append_drop p.2 p.1] at hb hz
  obtain ⟨hu,hv⟩ := (joined_ballot ..).mp hb
  refine ⟨by rw [List.length_take, Nat.min_eq_left (by omega)],
    by rw [← List.length_append,List.take_append_drop,hl],hu,
    (reverse_suffix (ballot_endpoint_nonneg hu) hz).mp hv,?_⟩
  rw [reverseWalk_disp,displacement_append] at *
  omega

private theorem unfolded_height {p : List Bool × ℕ} {d : ℕ} (hp : p ∈ marks d) :
    displacement (unfoldMark p) = 2*height p+1 := by
  obtain ⟨_,_,_,_,he⟩ := pieces hp
  rw [unfoldMark,displacement_append]
  change _ + (1+displacement (reverseWalk _)) = _
  rw [he,height]; omega

private theorem unfolded_inj {d : ℕ} {p q : List Bool × ℕ} (hp : p ∈ marks d) (hq : q ∈ marks d)
    (h : unfoldMark p = unfoldMark q) : p = q := by
  obtain ⟨hpL,_,_,hpB,_⟩ := pieces hp
  obtain ⟨hqL,_,_,hqB,_⟩ := pieces hq
  have he := congrArg displacement h
  rw [unfolded_height hp,unfolded_height hq] at he
  have ⟨hu,hv⟩ := departure_unique (by change height p = height q; omega) hpB hqB h
  have hs := congrArg reverseWalk hv
  simp only [reverseWalk_twice] at hs
  exact Prod.ext (by calc
    p.1 = p.1.take p.2 ++ p.1.drop p.2 := (List.take_append_drop ..).symm
    _ = q.1 := by rw [hu,hs,List.take_append_drop])
    (hpL.symm.trans ((congrArg List.length hu).trans hqL))

private theorem image_tail (d b : ℕ) : (tail d b).image unfoldMark = highBallots d b := by
  ext w
  constructor
  · intro h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hm,hb⟩ := Finset.mem_filter.mp hp
    obtain ⟨_,hl,hu,hv,_⟩ := pieces hm
    apply Finset.mem_filter.mpr
    refine ⟨mem_ballots.mpr ⟨by simp only [unfoldMark,List.length_append,List.length_cons,reverseWalk_length]; omega,unfold_ballot hu hv⟩,?_⟩
    rw [unfolded_height hm]
    change (b:ℤ) ≤ height p at hb
    omega
  · intro hw
    obtain ⟨hball,hh⟩ := Finset.mem_filter.mp hw
    obtain ⟨hl,hball⟩ := mem_ballots.mp hball
    change 2*(b:ℤ)+1 ≤ displacement w at hh
    let h := d-(wordParts w).length
    have he := displacement_length w
    rw [hl] at he
    push_cast at he
    have hend : displacement w = 2*(h:ℤ)+1 := by dsimp [h]; omega
    obtain ⟨u,v,rfl,hu,hv⟩ := last_departure w h (by omega)
    have hvh : displacement v = (h:ℤ) := by
      rw [displacement_append,hu] at hend
      change _ + (1+displacement v) = _ at hend
      omega
    let p : List Bool × ℕ := (u++reverseWalk v,u.length)
    have htake : p.1.take p.2 = u := by simp [p]
    have hdrop : p.1.drop p.2 = reverseWalk v := by simp [p]
    have hz : displacement (u++reverseWalk v) = 0 := by rw [displacement_append,hu,reverseWalk_disp,hvh]; omega
    have hbu := ((joined_ballot ..).mp hball).1
    have hrev : BallotFrom 0 (reverseWalk (reverseWalk v)) := by simpa
    have ht : p ∈ tail d b := by
      simp only [List.length_append,List.length_cons] at hl
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨mem_dycks.mpr ⟨⟨?_,?_⟩,hz⟩, Finset.mem_range.mpr ?_⟩,?_⟩
      · change (u++reverseWalk v).length = 2*d
        simp only [List.length_append,reverseWalk_length]; omega
      · exact (joined_ballot ..).mpr ⟨hbu,(reverse_suffix (ballot_endpoint_nonneg hbu) hz).mpr hrev⟩
      · change u.length < 2*d+1; omega
      · change (b:ℤ) ≤ displacement (p.1.take p.2)
        rw [htake,hu]; omega
    exact Finset.mem_image.mpr ⟨p,ht,by simp [unfoldMark,htake,hdrop]⟩

/-- A mark at height at least b corresponds to a ballot path of length 2d+1
whose number of down-steps is at most d-b. -/
theorem card_tail {d b : ℕ} (hb : b ≤ d) :
    (tail d b).card = (2*d+1).choose (d-b) := by
  rw [← Finset.card_image_of_injOn (f := unfoldMark) (s := tail d b)
    (fun _ hp _ hq he => unfolded_inj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he),
    image_tail]
  let m := 2*d+1
  let rows := (Finset.range (d-b+1)).biUnion (partitions m)
  have hr {l : List ℕ} : l ∈ rows ↔ Fits m l ∧ l.length ≤ d-b := by
    simp only [rows,Finset.mem_biUnion,Finset.mem_range,mem_partitions]
    constructor
    · rintro ⟨i,hi,hf,rfl⟩; exact ⟨hf,by omega⟩
    · rintro ⟨hf,hl⟩; exact ⟨_,by omega,hf,rfl⟩
  have hc : (highBallots d b).card = rows.card := by
    apply Finset.card_bij' (fun w _ => wordParts w) (fun l _ => wordOfParts m l)
    · intro w hw
      obtain ⟨hw,hh⟩ := Finset.mem_filter.mp hw
      obtain ⟨hl,hw⟩ := mem_ballots.mp hw
      have hd := displacement_length w
      rw [hl] at hd
      change 2*(b:ℤ)+1 ≤ displacement w at hh
      exact hr.mpr ⟨by simpa [m,hl] using (ballot_iff_fits 0 w).mp hw,by omega⟩
    · intro l hl
      obtain ⟨hf,he⟩ := hr.mp hl
      obtain ⟨hlen,hball⟩ := ((ballotEquiv m).symm ⟨l,hf⟩).property
      apply Finset.mem_filter.mpr ⟨mem_ballots.mpr ⟨hlen,hball⟩,?_⟩
      have hw := displacement_length (wordOfParts m l)
      rw [wordOfParts_length,wordParts_wordOfParts hf] at hw
      change displacement (wordOfParts m l) + 2*(l.length:ℤ) = (2*(d:ℤ)+1) at hw
      change 2*(b:ℤ)+1 ≤ displacement (wordOfParts m l)
      omega
    · intro w hw
      have hl := (mem_ballots.mp (Finset.mem_filter.mp hw).1).1
      simpa only [hl] using wordOfParts_wordParts w
    · intro l hl
      exact wordParts_wordOfParts (hr.mp hl).1
  rw [hc,Finset.card_biUnion (s := Finset.range (d-b+1)) (fun _ _ _ _ h => disjoint_lengths h)]
  exact sum_card_partitions m _ (by dsimp [m]; omega)

theorem tail_empty {d b : ℕ} (hb : d < b) : tail d b = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hm,hb'⟩ := Finset.mem_filter.mp hp
  have him := Finset.mem_image_of_mem unfoldMark hp
  rw [image_tail] at him
  have hl := (mem_ballots.mp (Finset.mem_filter.mp him).1).1
  have he := displacement_length (unfoldMark p)
  rw [hl,unfolded_height hm] at he
  change (b:ℤ) ≤ height p at hb'
  omega

theorem height_bounds {d : ℕ} {p : List Bool × ℕ} (hp : p ∈ marks d) :
    0 ≤ height p ∧ height p ≤ (d:ℤ) := by
  refine ⟨ballot_endpoint_nonneg (pieces hp).2.2.1,?_⟩
  by_contra! h
  have hit : p ∈ tail d (d+1) := Finset.mem_filter.mpr ⟨hp,by omega⟩
  rw [tail_empty (Nat.lt_succ_self _)] at hit
  exact Finset.notMem_empty _ hit

theorem card_marks (d : ℕ) : (marks d).card = (2*d+1).choose d := by
  have h : tail d 0 = marks d := by
    apply Finset.filter_true_of_mem
    intro p hp
    exact (height_bounds hp).1
  simpa [h] using (card_tail (d := d) (b := 0) (Nat.zero_le _))

end CentralUnimodality.MarkedExcursion
