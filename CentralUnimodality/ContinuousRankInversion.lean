module

public import CentralUnimodality.PointAmplitude
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Continuous Fourier interpolation of the original ranks on their
positive shifted area lattice. Integrating through the exact period
does not require a periodization error estimate. -/
@[expose] public section

namespace CentralUnimodality.Witness

open Real intervalIntegral Laurent

private theorem integer_cosine (k : ℤ) :
    (∫ t in 0..π, cos (t*(k:ℝ)))=if k=0 then π else 0 := by
  by_cases h : k=0
  · simp [h]
  rw [ite_eq_right h,integral_comp_mul_right cos (by exact_mod_cast h),integral_cos,
    zero_mul,mul_comm π,sin_int_mul_pi,sin_zero,sub_self,smul_zero]

private theorem cosine_pair (h a b : ℕ) (hh : 0<h) :
    (∫ t in 0..π, cos (t*((a:ℝ)+h/2))*cos (t*((b:ℝ)+h/2)))=
      if a=b then π/2 else 0 := by
  let u : ℤ := (a:ℤ)+b+h
  let v : ℤ := (a:ℤ)-b
  have hu : u≠0 := by dsimp [u]; omega
  have hv : v=0 ↔ a=b := by dsimp [v]; omega
  have identity (t : ℝ) : cos (t*((a:ℝ)+h/2))*cos (t*((b:ℝ)+h/2))=
      (cos (t*(u:ℝ))+cos (t*(v:ℝ)))/2 := by
    have plus : t*(u:ℝ)=t*((a:ℝ)+h/2)+t*((b:ℝ)+h/2) := by dsimp [u]; push_cast; ring
    have minus : t*(v:ℝ)=t*((a:ℝ)+h/2)-t*((b:ℝ)+h/2) := by dsimp [v]; push_cast; ring
    rw [plus,minus,cos_add,cos_sub]; ring
  simp_rw [identity]
  rw [integral_div,integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),integer_cosine,integer_cosine,ite_eq_right hu]
  split_ifs <;> simp_all

noncomputable def rankIntegral (n δ : ℕ) (x : ℝ) : ℝ :=
  ∫ ξ in 0..π*cellScale (n+δ), signedAmplitude n δ (ξ/cellScale (n+δ))*cos (x*ξ)

private theorem halfAreaSite_value (n δ j : ℕ) :
    (halfAreaSite n δ j:ℝ)=(n*(n+δ)-j:ℕ)+(3*n+2*δ+1:ℕ)/2 := by
  unfold halfAreaSite
  push_cast
  ring

/-- At an original rank the interpolation equals its strictly positive
normalizing factor times its exact count. -/
theorem rankIntegral_site {n δ i : ℕ} (hs : δ≤1) (hn : 0<n+δ) (hi : i≤n*(n+δ)) :
    rankIntegral n δ (scaledSite n δ i)=
      (π*cellScale (n+δ)/(2*(massFactor n δ:ℝ)))*rankCount (2*n+δ) i := by
  let S := cellScale (n+δ)
  let D := n*(n+δ)
  let m := 2*n+δ
  let H := 3*n+2*δ+1
  have hS : S≠0 := (cellScale_pos hn).ne'
  let A := fun j : ℕ => (D-j:ℕ)+(H:ℝ)/2
  have phase (j : ℕ) (t : ℝ) : t*S*scaledSite n δ j=t*A j := by
    dsimp only [scaledSite,A,S,D,H]
    rw [halfAreaSite_value]
    field_simp [show cellScale (n+δ)≠0 from hS]
  have coeff (j : ℕ) (hj : j∈Finset.range (D+1)) :
      (∫ t in 0..π, cos (t*A j)*cos (t*A i))=if j=i then π/2 else 0 := by
    have id := cosine_pair H (D-j) (D-i) (by dsimp [H]; omega)
    have hj' := Finset.mem_range.mp hj
    have hij : D-j=D-i ↔ j=i := by change i≤D at hi; omega
    simpa only [hij,A] using id
  let g := fun ξ => signedAmplitude n δ (ξ/S)*cos (scaledSite n δ i*ξ)
  have sub : rankIntegral n δ (scaledSite n δ i)=S*(∫ t in 0..π, g (t*S)) := by
    simpa only [zero_mul,g,S,rankIntegral] using (mul_integral_comp_mul_right (a:=0) (b:=π) (f:=g) S).symm
  have form (t : ℝ) : g (t*S)=
      (∑ j ∈ Finset.range (D+1), (rankCount m j:ℝ)*(cos (t*A j)*cos (t*A i)))/(massFactor n δ:ℝ) := by
    dsimp only [g]
    rw [signedAmplitude_mean _ _ hs,rankMean,mul_comm (scaledSite n δ i),phase]
    simp only [phase]
    rw [div_mul_eq_mul_div,Finset.sum_mul]
    simp only [D,m,mul_assoc]
  rw [sub]
  simp_rw [form]
  rw [integral_div,integral_finsetSum (f:=fun j t => (rankCount m j:ℝ)*(cos (t*A j)*cos (t*A i)))
    (by intro j _; apply Continuous.intervalIntegrable; fun_prop)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_congr rfl (fun j hj => congrArg ((rankCount m j:ℝ)*·) (coeff j hj))]
  simp [Finset.mem_range.mpr (show i<D+1 by omega),S,m]
  ring

end CentralUnimodality.Witness
