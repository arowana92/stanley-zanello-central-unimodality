module

public import CentralUnimodality.DyckColumnCheckpoints
meta import CentralUnimodality.DyckStateWitness

/-! Exact reflected comparisons through semilength 256. The kernel
checks each proposed column from its predecessor in 32 semilengths. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

private noncomputable def row32 : List ℕ := dyck_column% 513 3606 62 32

private theorem stage32 : CheckedDycks 513 3606 62 32 row32 :=
  (CheckedDycks.start 513 3606 62).extend (k:=32) (by decide) (by decide) (by decide +kernel)

private noncomputable def row64 : List ℕ := dyck_column% 513 3606 62 64

private theorem stage64 : CheckedDycks 513 3606 62 64 row64 :=
  stage32.extend (k:=32) (by decide) (by decide) (by decide +kernel)

private noncomputable def row96 : List ℕ := dyck_column% 513 3606 62 96

private theorem stage96 : CheckedDycks 513 3606 62 96 row96 :=
  stage64.extend (k:=32) (by decide) (by decide) (by decide +kernel)

private noncomputable def row128 : List ℕ := dyck_column% 513 3606 62 128

private theorem stage128 : CheckedDycks 513 3606 62 128 row128 :=
  stage96.extend (k:=32) (by decide) (by decide) (by decide +kernel)

private noncomputable def row160 : List ℕ := dyck_column% 513 3606 62 160

private theorem stage160 : CheckedDycks 513 3606 62 160 row160 :=
  stage128.extend (k:=32) (by decide) (by decide) (by decide +kernel)

private noncomputable def row192 : List ℕ := dyck_column% 513 3606 62 192

private theorem stage192 : CheckedDycks 513 3606 62 192 row192 :=
  stage160.extend (k:=32) (by decide) (by decide) (by decide +kernel)

private noncomputable def row224 : List ℕ := dyck_column% 513 3606 62 224

private theorem stage224 : CheckedDycks 513 3606 62 224 row224 :=
  stage192.extend (k:=32) (by decide) (by decide) (by decide +kernel)

private theorem last33 : checkPairedDycks 513 3606 62 33 224 row224=true := by decide +kernel

theorem dyck_comparisons_through_256 {l : ℕ} (hl : l≤256) :
    ReflectedCoeffs (dyckPoly l) (⌈dyckLower l⌉₊:ℕ) := by
  by_cases h : l<224
  · exact stage224.tested l h
  · have H := last33
    rw [← stage224.state] at H
    exact checkPairedDycks_sound (by decide) (by decide) H (by omega) (by omega)

end CentralUnimodality.HeightBlock
