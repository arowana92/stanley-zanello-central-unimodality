module

public import CentralUnimodality.MeshDot

/-! Share the intermediate half-angle enclosures when checking the single
phase table used by every Fourier length group. -/
@[expose] public section

namespace CentralUnimodality.MeshPhase

private def children (d : ℕ) (a : ℕ × ℕ) : List (ℕ × ℕ) :=
  let lo := DyadicAngle.lowerRoot d a.1
  let hi := DyadicAngle.upperRoot d a.2
  [(d+lo,d+hi),(d-hi,d-lo)]

private def levels (d : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => [(2*d,2*d),(0,0)]
  | k+1 => (levels d k).flatMap (children d)

private theorem bounds_mem (d k t : ℕ) (ht : t ≤ 2^k) : DyadicAngle.bounds d k t ∈ levels d k := by
  induction k generalizing t with
  | zero =>
    by_cases h : t = 0 <;> simp [DyadicAngle.bounds,levels,h]
  | succ k ih =>
    rw [levels,List.mem_flatMap]
    by_cases h : t ≤ 2^k
    · exact ⟨_,ih t h,by simp [DyadicAngle.bounds,h,children]⟩
    · rw [pow_succ] at ht
      exact ⟨_,ih (2*2^k-t) (by omega),by simp [DyadicAngle.bounds,h,children]⟩

private theorem all_radii {d k e : ℕ} (h : (levels d k).all (fun a => decide (radius a ≤ e)) = true) :
    radiusCheck d k e = true := by
  apply List.all_eq_true.mpr
  intro t ht
  exact List.all_eq_true.mp h _ (bounds_mem d k t (by have := List.mem_range.mp ht; omega))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem production_radius : radiusCheck (2^112) 14 653 = true := by
  apply all_radii
  decide +kernel

end CentralUnimodality.MeshPhase
