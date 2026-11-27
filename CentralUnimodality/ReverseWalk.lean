module

public import CentralUnimodality.Corank

/-! Reverse the traversal of an integer walk, including both endpoint
vertices. A walk staying strictly above zero reverses to another such walk. -/
@[expose] public section

namespace CentralUnimodality

def reverseWalk (w : List Bool) : List Bool := w.reverse.map Bool.not

@[simp] theorem reverseWalk_length (w : List Bool) : (reverseWalk w).length = w.length := by simp [reverseWalk]

@[simp] theorem reverseWalk_twice (w : List Bool) : reverseWalk (reverseWalk w) = w := by
  simp [reverseWalk,List.map_map,Function.comp_def]

theorem reverseWalk_cons (b : Bool) (w : List Bool) : reverseWalk (b::w) = reverseWalk w ++ [!b] := by
  simp [reverseWalk]

theorem step_flip (b : Bool) : step (!b) = -step b := by cases b <;> decide

theorem reverseWalk_disp (w : List Bool) : displacement (reverseWalk w) = -displacement w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [reverseWalk_cons,displacement_snoc,ih,step_flip]
    change _ = -(step b+displacement w)
    omega

def vertices (a : ℤ) (w : List Bool) := a :: heights a w

theorem endpoint_mem_vertices (a : ℤ) (w : List Bool) : a+displacement w ∈ vertices a w := by
  induction w generalizing a with
  | nil => simp [vertices,heights,displacement]
  | cons b w ih =>
    have h := ih (a+step b)
    change _ ∈ a :: vertices (a+step b) w
    apply List.mem_cons_of_mem
    simpa [displacement,add_assoc] using h

theorem reverse_vertices (a : ℤ) (w : List Bool) :
    vertices (a+displacement w) (reverseWalk w) = (vertices a w).reverse := by
  induction w generalizing a with
  | nil => simp [vertices,reverseWalk,displacement,heights]
  | cons b w ih =>
    have hd : a+displacement (b::w) = (a+step b)+displacement w := by
      simp [displacement,add_assoc]
    rw [hd,reverseWalk_cons]
    change vertices ((a+step b)+displacement w) (reverseWalk w++[!b]) =
      (a :: vertices (a+step b) w).reverse
    rw [List.reverse_cons,← ih]
    simp [vertices,heights_append,heights,reverseWalk_disp,step_flip]

def PositiveVertices (a : ℤ) (w : List Bool) := ∀ x ∈ vertices a w, 0 < x

theorem positive_reverse (a : ℤ) (w : List Bool) :
    PositiveVertices (a+displacement w) (reverseWalk w) ↔ PositiveVertices a w := by
  simp [PositiveVertices,reverse_vertices]

theorem positive_one_iff (w : List Bool) : PositiveVertices 1 w ↔ BallotFrom 0 w := by
  rw [ballot_iff_heights,PositiveVertices,vertices]
  have he : heights 1 w = (heights 0 w).map (1+·) := by simpa using heights_translate 1 0 w
  simp only [he,List.forall_mem_cons,List.forall_mem_map,Nat.cast_zero]
  constructor
  · intro h y hy
    have := h.2 y hy
    omega
  · intro h
    exact ⟨by decide,fun y hy => by have := h y hy; omega⟩

end CentralUnimodality
