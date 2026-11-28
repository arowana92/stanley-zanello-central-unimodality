module

public import CentralUnimodality.HeightBlockChecks

/-! A uniform lower bound on the sum of the endpoints in each
interval decomposition. It applies to all walk lengths, with free
or prescribed terminal height. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock
open Polynomial

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem cols64_0 : checkBlockColumns 64 30 202 0 5=true := by decide +kernel
private theorem cols64_1 : checkBlockColumns 64 30 202 5 5=true := by decide +kernel
private theorem cols64_2 : checkBlockColumns 64 30 202 10 5=true := by decide +kernel
private theorem cols64_3 : checkBlockColumns 64 30 202 15 5=true := by decide +kernel
private theorem cols64_4 : checkBlockColumns 64 30 202 20 5=true := by decide +kernel
private theorem cols64_5 : checkBlockColumns 64 30 202 25 5=true := by decide +kernel

theorem block64 (h t : ℕ) : ReflectedCoeffs (kernel 64 h t) 202 := by
  apply checkBlock_sound (p:=14) (H:=30) (by decide) (by decide) _ h t
  intro j hj
  by_cases h0 : j<5
  · exact ⟨0,5,by omega,by omega,cols64_0⟩
  by_cases h1 : j<10
  · exact ⟨5,5,by omega,by omega,cols64_1⟩
  by_cases h2 : j<15
  · exact ⟨10,5,by omega,by omega,cols64_2⟩
  by_cases h3 : j<20
  · exact ⟨15,5,by omega,by omega,cols64_3⟩
  by_cases h4 : j<25
  · exact ⟨20,5,by omega,by omega,cols64_4⟩
  exact ⟨25,5,by omega,by omega,cols64_5⟩

theorem transfer_reflected64 (m h : ℕ) (f : ℕ → ℕ[X]) :
    ReflectedCoeffs (transfer X m h f) ((m/64*202:ℕ):ℤ) := by
  have H := (transfer_blocks block64 (m/64) (m%64) h f).reflected
  rwa [show m/64*64+m%64=m by omega] at H

theorem dyck_reflected64 (n : ℕ) : ReflectedCoeffs (dyckPoly n) ((n/32*202:ℕ):ℤ) := by
  rw [dyck_eq_transfer,show n/32=(2*n)/64 by omega]
  apply transfer_reflected64

theorem ballot_reflected64 (m : ℕ) : ReflectedCoeffs (ballotPoly m) ((m/64*202:ℕ):ℤ) := by
  rw [ballot_eq_transfer]
  apply transfer_reflected64

end CentralUnimodality.HeightBlock
