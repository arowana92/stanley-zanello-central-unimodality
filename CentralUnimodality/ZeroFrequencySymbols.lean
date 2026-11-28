module

public import CentralUnimodality.EndpointTransforms
import CentralUnimodality.Corank
public import CentralUnimodality.SurvivalBounds

/-! The unrestricted endpoint symbol at zero frequency is a binomial
coefficient, including endpoints below the support. -/
@[expose] public section

namespace CentralUnimodality
open PowerSeries

theorem endpoint_zero_frequency (n k : ℕ) :
    endpointTransform 0 n ((n:ℤ)-2*k)=(n.choose k:ℕ) := by
  induction n generalizing k with
  | zero =>
    rw [endpointTransform]
    simp only [words,Finset.sum_singleton,displacement,List.map_nil,List.sum_nil]
    cases k with
    | zero => simp [areaCharacter]
    | succ k =>
      rw [ite_eq_right (by omega),Nat.choose_zero_succ,Nat.cast_zero]
  | succ n ih =>
    rw [endpoint_append]
    simp only [areaCharacter,zero_mul,Complex.ofReal_zero,Complex.exp_zero,one_mul]
    cases k with
    | zero =>
      simp only [Nat.cast_zero,mul_zero,sub_zero,Nat.cast_succ,add_sub_cancel_right,Nat.choose_zero_right]
      have over : endpointTransform 0 n ((n:ℤ)+1+1)=0 := by
        apply Finset.sum_eq_zero
        intro w hw
        have H := displacement_length w
        rw [mem_words.mp hw] at H
        simp [show displacement w≠(n:ℤ)+1+1 by omega]
      simpa [over] using (ih 0)
    | succ k =>
      rw [show ((n+1:ℕ):ℤ)-2*(k+1:ℕ)-1=(n:ℤ)-2*(k+1:ℕ) by omega,
        show ((n+1:ℕ):ℤ)-2*(k+1:ℕ)+1=(n:ℤ)-2*k by omega,ih,ih,Nat.choose_succ_succ]
      push_cast; ring

theorem fair_bridge_zero_frequency (j : ℕ) :
    coeff (2*j) (fairSeries (areaCharacter 0) bridges)=(survival j:ℂ) := by
  have zero : ((2*j:ℕ):ℤ)-2*j=0 := by omega
  have count := endpoint_zero_frequency (2*j) j
  rw [zero] at count
  rw [fair_bridge_endpoint,count,survival,Nat.centralBinom,pow_mul]
  push_cast
  norm_num
  ring_nf
  rw [one_div]

end CentralUnimodality
