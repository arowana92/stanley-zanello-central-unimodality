module

public import CentralUnimodality.LocalQuadraticResidual
public meta import CentralUnimodality.RoundedQuadraticRows
import Mathlib.Tactic.Eval

/-! Retain the first 256 dyadic modes in each parity. The numerical tail and
the exact conversion of each prefix to monomials are checked separately. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

def evenQuadraticDyadic : List ℤ := eval% quadraticChebRow 0
def oddQuadraticDyadic : List ℤ := eval% quadraticChebRow 1

def evenQuadraticPower : List ℤ := eval% unpackCheb 1024 (evenQuadraticDyadic.take 256)
def oddQuadraticPower : List ℤ := eval% unpackCheb 1024 (oddQuadraticDyadic.take 256)

private def evenPacked : ℤ := eval% packCheb 1024 (evenQuadraticDyadic.take 256)
private def oddPacked : ℤ := eval% packCheb 1024 (oddQuadraticDyadic.take 256)

private theorem even_packed : packCheb 1024 (evenQuadraticDyadic.take 256)=evenPacked := by decide +kernel
private theorem odd_packed : packCheb 1024 (oddQuadraticDyadic.take 256)=oddPacked := by decide +kernel

def dyadicQuadratic (σ : ℕ) := if σ=0 then evenQuadraticDyadic else oddQuadraticDyadic
def powerQuadratic (σ : ℕ) := if σ=0 then evenQuadraticPower else oddQuadraticPower

theorem prefix_quadratic_power (σ : ℕ) :
    unpackCheb 1024 ((dyadicQuadratic σ).take 256)=powerQuadratic σ := by
  by_cases h : σ=0
  · simp only [dyadicQuadratic,powerQuadratic,ite_eq_left h,unpackCheb,even_packed,← blockCenteredDigits_exact 1024 7]
    decide +kernel
  · simp only [dyadicQuadratic,powerQuadratic,ite_eq_right h,unpackCheb,odd_packed,← blockCenteredDigits_exact 1024 7]
    decide +kernel

theorem quadratic_prefix_bounds (σ : ℕ) :
    (dyadicQuadratic σ).length=611 ∧
    coefficientMass ((dyadicQuadratic σ).drop 256)*10^9<2*2^120 ∧
    (coefficientMass ((dyadicQuadratic σ).take 256):ℤ)*7^((dyadicQuadratic σ).take 256).length<2^1024 ∧
    coefficientMass (powerQuadratic σ)*1024^(powerQuadratic σ).length<2^5376 := by
  by_cases h : σ=0
  · simp only [dyadicQuadratic,powerQuadratic,ite_eq_left h]; decide +kernel
  · simp only [dyadicQuadratic,powerQuadratic,ite_eq_right h]; decide +kernel

end CentralUnimodality.PolynomialTrial
