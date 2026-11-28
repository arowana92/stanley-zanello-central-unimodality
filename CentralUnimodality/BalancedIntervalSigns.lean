module

public import CentralUnimodality.PackedIntervalSigns

/-! A balanced evaluation of the homogeneous polynomial at the packing
base. It reuses both homogeneous powers across each coefficient block. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

def scalarHomogeneous (u v : ℤ) : List ℤ → ℤ × ℤ
  | [] => (0,1)
  | c::a =>
    let (z,d) := scalarHomogeneous u v a
    (u*z+c*(v*d),v*d)

private theorem scalar_append (u v : ℤ) (a b : List ℤ) :
    scalarHomogeneous u v (a++b)=
      ((scalarHomogeneous u v a).1*(scalarHomogeneous u v b).2+u^a.length*(scalarHomogeneous u v b).1,
        (scalarHomogeneous u v a).2*(scalarHomogeneous u v b).2) := by
  induction a with
  | nil => simp [scalarHomogeneous]
  | cons c a ih =>
    simp only [List.cons_append,scalarHomogeneous,ih,List.length_cons,pow_succ]
    congr 1 <;> ring

private theorem scalar_packed (bits : ℕ) (l h q : ℤ) (a : List ℤ) :
    scalarHomogeneous (l+(h <<< bits)) (q+(q <<< bits)) a=homogeneousPack bits l h q a := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    simp only [scalarHomogeneous,homogeneousPack,ih]
    simp only [Int.shiftLeft_eq]
    congr 1 <;> ring

def blockHomogeneous (u v : ℤ) : ℕ → List ℤ → ℤ × ℤ × ℤ
  | 0, a =>
    let (p,d) := scalarHomogeneous u v a
    (p,d,u^a.length)
  | k+1, a =>
    let n := a.length/2
    let (p,d,m) := blockHomogeneous u v k (a.take n)
    let (s,t,b) := blockHomogeneous u v k (a.drop n)
    (p*t+m*s,d*t,m*b)

theorem blockHomogeneous_exact (u v : ℤ) (k : ℕ) (a : List ℤ) :
    blockHomogeneous u v k a=
      ((scalarHomogeneous u v a).1,(scalarHomogeneous u v a).2,u^a.length) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    let n := a.length/2
    have H := scalar_append u v (a.take n) (a.drop n)
    rw [List.take_append_drop] at H
    have len : (a.take n).length+(a.drop n).length=a.length := by
      rw [← List.length_append,List.take_append_drop]
    simp only [blockHomogeneous,ih]
    dsimp only [n] at H len
    rw [H,← pow_add,len]

def balancedPack (depth bits : ℕ) (l h q : ℤ) (a : List ℤ) : ℤ × ℤ :=
  let (p,d,_) := blockHomogeneous (l+(h <<< bits)) (q+(q <<< bits)) depth a
  (p,d)

theorem balancedPack_exact (depth bits : ℕ) (l h q : ℤ) (a : List ℤ) :
    balancedPack depth bits l h q a=homogeneousPack bits l h q a := by
  simp [balancedPack,blockHomogeneous_exact,scalar_packed]

end CentralUnimodality.PolynomialTrial
