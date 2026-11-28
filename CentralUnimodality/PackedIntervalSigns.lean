module

public import CentralUnimodality.IntervalPolynomialSigns

/-! Evaluate the homogeneous sign test at one power of two. A bound on
the coefficient mass makes the signs of its centered digits exact. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Polynomial

def homogeneousPack (bits : ℕ) (l h q : ℤ) : List ℤ → ℤ × ℤ
  | [] => (0,1)
  | c::a =>
    let (v,d) := homogeneousPack bits l h q a
    let next := q*(d+(d <<< bits))
    (l*v+((h*v) <<< bits)+c*next,next)

def packedDigitsTest (b n : ℕ) (m k : ℤ) (p : ℤ × ℤ) : Bool :=
  (centeredDigits b n (m*p.1-k*p.2)).all (fun c => decide (0≤c))

private theorem linear_mass (p q : ℤ) (a b : List ℤ) :
    coefficientMass (linearRows p q a b)≤p.natAbs*coefficientMass a+q.natAbs*coefficientMass b := by
  have scale (s : ℤ) (u : List ℤ) : coefficientMass (u.map (s*·))=s.natAbs*coefficientMass u := by
    induction u with
    | nil => simp [coefficientMass]
    | cons c u ih => simpa [coefficientMass,Int.natAbs_mul,mul_add] using ih
  induction a generalizing b with
  | nil => rw [linearRows,scale]; simp [coefficientMass]
  | cons c a ih =>
    cases b with
    | nil => rw [linearRows,scale] <;> simp [coefficientMass]
    | cons e b =>
      have bound := Int.natAbs_add_le (p*c) (q*e)
      simp only [Int.natAbs_mul] at bound
      change (p*c+q*e).natAbs+coefficientMass (linearRows p q a b)≤
        p.natAbs*(c.natAbs+coefficientMass a)+q.natAbs*(e.natAbs+coefficientMass b)
      rw [mul_add,mul_add]
      have sub := ih b
      omega

private theorem mulLinear_mass (p q : ℤ) (a : List ℤ) :
    coefficientMass (mulLinear p q a)≤(p.natAbs+q.natAbs)*coefficientMass a := by
  simpa [mulLinear,coefficientMass,add_mul] using linear_mass p q a (0::a)

theorem projective_mass (l h q : ℤ) (B : ℕ) (hh : l.natAbs+h.natAbs≤B) (hq : q.natAbs+q.natAbs≤B)
    (a : List ℤ) :
    coefficientMass (projectiveRows l h q a).1≤coefficientMass a*B^a.length ∧
    coefficientMass (projectiveRows l h q a).2≤B^a.length := by
  induction a with
  | nil => simp [projectiveRows,coefficientMass]
  | cons c a ih =>
    let v := (projectiveRows l h q a).1
    let d := (projectiveRows l h q a).2
    let next := mulLinear q q d
    have den : coefficientMass next≤B^(a.length+1) :=
      (mulLinear_mass q q d).trans ((Nat.mul_le_mul hq ih.2).trans_eq (by ring))
    have prev := (mulLinear_mass l h v).trans (Nat.mul_le_mul hh ih.1)
    refine ⟨?_,den⟩
    apply (linear_mass 1 c (mulLinear l h v) next).trans
    simp only [Int.natAbs_one,one_mul]
    apply (Nat.add_le_add prev (Nat.mul_le_mul_left _ den)).trans_eq
    change _=(c.natAbs+coefficientMass a)*B^(a.length+1)
    ring

private theorem linear_length (p q : ℤ) (a b : List ℤ) :
    (linearRows p q a b).length=max a.length b.length := by
  induction a generalizing b with
  | nil => simp [linearRows]
  | cons c a ih =>
    cases b with
    | nil => simp [linearRows]
    | cons e b => simp [linearRows,ih,Nat.succ_max_succ]

private theorem mulLinear_length (p q : ℤ) (a : List ℤ) : (mulLinear p q a).length=a.length+1 := by
  simp [mulLinear,linear_length]

theorem projective_length (l h q : ℤ) (a : List ℤ) :
    (projectiveRows l h q a).1.length≤a.length+1 ∧ (projectiveRows l h q a).2.length=a.length+1 := by
  induction a with
  | nil => simp [projectiveRows]
  | cons c a ih => simp only [projectiveRows,linear_length,mulLinear_length,List.length_cons]; omega

private theorem linear_pack (p q : ℤ) (a b : List ℤ) (s : ℕ) :
    packDense s (linearRows p q a b)=p*packDense s a+q*packDense s b := by
  simp only [packDense_eval,dense_linear,eval_add,eval_mul,eval_C]

theorem homogeneousPack_exact (s : ℕ) (l h q : ℤ) (a : List ℤ) :
    homogeneousPack s l h q a=
      (packDense s (projectiveRows l h q a).1,packDense s (projectiveRows l h q a).2) := by
  have mul (p q : ℤ) (u : List ℤ) : packDense s (mulLinear p q u)=
      p*packDense s u+((q*packDense s u) <<< s) := by
    rw [mulLinear,linear_pack,packDense,Int.zero_add,Int.shiftLeft_eq,Int.shiftLeft_eq]; ring
  induction a with
  | nil => simp [homogeneousPack,projectiveRows,packDense]
  | cons c a ih =>
    simp only [homogeneousPack,projectiveRows,ih,linear_pack,mul,one_mul,Int.shiftLeft_eq]
    congr 1 <;> ring

theorem rowTest_of_packed {bits B n : ℕ} {l h q m k : ℤ} {a : List ℤ}
    (hl : l.natAbs+h.natAbs≤B) (hq : q.natAbs+q.natAbs≤B) (hn : a.length+1≤n)
    (hb : (m.natAbs*coefficientMass a+k.natAbs)*B^a.length<2^bits)
    (test : packedDigitsTest bits n m k (homogeneousPack (bits+1) l h q a)=true) :
    rowTest m k (projectiveRows l h q a)=true := by
  let p := projectiveRows l h q a
  let c := linearRows m (-k) p.1 p.2
  have cap := projective_mass l h q B hl hq a
  have mass : coefficientMass c<2^bits := by
    apply (linear_mass ..).trans_lt
    rw [Int.natAbs_neg]
    exact (Nat.add_le_add (Nat.mul_le_mul_left _ cap.1) (Nat.mul_le_mul_left _ cap.2)).trans_lt
      ((by ring : m.natAbs*(coefficientMass a*B^a.length)+k.natAbs*B^a.length=
        (m.natAbs*coefficientMass a+k.natAbs)*B^a.length) ▸ hb)
  have coeff (i : ℕ) : |(densePoly c).coeff i|<2^bits := (dense_coeff_bound c i).trans_lt (by exact_mod_cast mass)
  have same : m*(homogeneousPack (bits+1) l h q a).1-k*(homogeneousPack (bits+1) l h q a).2=
      (densePoly c).eval (2^(bits+1)) := by
    rw [homogeneousPack_exact,← packDense_eval]
    dsimp only [c,p]; rw [linear_pack]; ring
  unfold packedDigitsTest at test
  rw [same] at test
  have len := projective_length l h q a
  have clen : c.length≤n := by dsimp only [c,p]; rw [linear_length]; omega
  apply List.all_eq_true.mpr
  intro z hz
  change z∈c at hz
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hz
  have eq := centeredDigits_coeff (densePoly c) bits n coeff (hi.trans_le clen)
  rw [dense_coeff,List.getElem?_eq_getElem hi,Option.getD_some] at eq
  exact List.all_eq_true.mp test _ (List.mem_of_getElem? eq)

end CentralUnimodality.PolynomialTrial
