module

public import CentralUnimodality.DenseIntegerCertificate
public import CentralUnimodality.BlockRadixDigits

/-! Balanced packing limits the number of large shifted intermediate integers
when checking a dense polynomial product in the kernel. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

private theorem pack_append (bits : ℕ) (a b : List ℤ) :
    packDense bits (a++b)=packDense bits a+(packDense bits b <<< (bits*a.length)) := by
  induction a with
  | nil => simp [packDense]
  | cons c a ih =>
    simp only [List.cons_append,packDense,ih,List.length_cons,Int.shiftLeft_eq,Nat.mul_succ,pow_add]
    ring

def blockPackDense (bits : ℕ) : ℕ → List ℤ → ℤ
  | 0, a => packDense bits a
  | k+1, a =>
    if a.length≤8 then packDense bits a else
      let n := a.length/2
      blockPackDense bits k (a.take n)+(blockPackDense bits k (a.drop n) <<< (bits*n))

theorem blockPackDense_exact (bits k : ℕ) (a : List ℤ) : blockPackDense bits k a=packDense bits a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [blockPackDense]
    split
    · rfl
    · simp only [ih]
      have eq := pack_append bits (a.take (a.length/2)) (a.drop (a.length/2))
      simpa [List.length_take,Nat.div_le_self] using eq.symm

end CentralUnimodality.PolynomialTrial
