module

public import CentralUnimodality.WallisEnclosure
public import CentralUnimodality.PolynomialBounds

/-! The explicit degree-ten trial polynomials and rational anchor for the
precision needed by the moment witnesses. -/
@[expose] public section

namespace CentralUnimodality.Wallis

open Witness

def trial : List ℚ := [1,1/8,1/128,-5/1024,-21/32768,399/262144,869/4194304,
  -39325/33554432,-334477/2147483648,28717403/17179869184]

def lower := trial ++ [-1]
def upper := trial ++ [1]

def lowerConstant : ℚ := 31332853432887506280197/25000000000000000000000
def upperConstant : ℚ := 125331413731550025120789/100000000000000000000000

private theorem signs :
    nonpositive (1/96) (ratioPolynomial lower) = true ∧
    nonpositive (1/96) ((ratioPolynomial upper).map ((-1)*·)) = true ∧
    nonpositive (1/96) (addCoeffs [1/2] (lower.map ((-1)*·))) = true := by decide +kernel

private theorem horner_snoc {R : Type*} [Field R] [CharZero R] (x : R) (p : List ℚ) (a : ℚ) :
    horner x (p++[a]) = horner x p + x^p.length*(a:R) := by
  induction p with
  | nil => simp [horner]
  | cons c p ih => simp only [List.cons_append,horner,ih,List.length_cons,pow_succ]; ring

private theorem trial_order {x : ℝ} (hx : 0 ≤ x) (hb : x ≤ ((1/96:ℚ):ℝ)) :
    0 < horner x lower ∧ horner x lower ≤ horner x upper := by
  have h := nonpositive_sound hx hb _ signs.2.2
  rw [horner_add,horner_scale] at h
  norm_num [horner] at h
  refine ⟨by linarith, ?_⟩
  rw [lower,upper,horner_snoc,horner_snoc]
  simp only [Rat.cast_neg,Rat.cast_one,mul_neg,mul_one]
  have : 0 ≤ x^trial.length := pow_nonneg hx _
  linarith

private theorem trial_steps {x : ℝ} (hx : 0 ≤ x) (hb : x ≤ ((1/96:ℚ):ℝ)) :
    (1+x)*(horner x lower)^2 ≤ (1+x/2)^2*(horner (x/(1+x)) lower)^2 ∧
    (1+x/2)^2*(horner (x/(1+x)) upper)^2 ≤ (1+x)*(horner x upper)^2 := by
  have h₁ := nonpositive_sound hx hb _ signs.1
  have h₂ := nonpositive_sound hx hb _ signs.2.1
  rw [horner_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul, neg_nonpos] at h₂
  rw [horner_ratioPolynomial hx] at h₁ h₂
  exact ⟨sub_nonpos.mp (nonpos_of_mul_nonpos_right h₁ (by positivity)),
    sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by positivity)).mp h₂)⟩

private def fastCentral : ℕ → ℕ
  | 0 => 1
  | n+1 => 2*(2*n+1)*fastCentral n/(n+1)

private theorem fastCentral_eq (n : ℕ) : fastCentral n = n.centralBinom := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fastCentral,ih,← Nat.succ_mul_centralBinom_succ,Nat.mul_div_cancel_left _ (by omega)]

private def anchorValue : ℚ := 4^8192 / (128*fastCentral 8192)

set_option maxRecDepth 100000 in
private theorem anchor_checked :
    lowerConstant * horner (1/8192:ℚ) upper ≤ anchorValue ∧
    anchorValue ≤ upperConstant * horner (1/8192:ℚ) lower := by decide +kernel

private theorem anchor_real : wallisFactor 8192 = (anchorValue:ℝ) := by
  rw [wallisFactor,survival,anchorValue,fastCentral_eq]
  have hs : Real.sqrt (2*(8192:ℝ)) = 128 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  simp only [Nat.cast_ofNat,hs,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,
    Rat.cast_ofNat,Rat.cast_natCast]
  generalize (4:ℝ)^8192 = v
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,one_mul]
  ring

private theorem horner_real (p : List ℚ) (x : ℚ) : ((horner x p : ℚ):ℝ) = horner (x:ℝ) p := by
  induction p with
  | nil => simp [horner]
  | cons c p ih => simp [horner,ih]

theorem uniform {n : ℕ} (hn : 96 ≤ n) :
    (lowerConstant:ℝ)*horner (n:ℝ)⁻¹ lower ≤ wallisFactor n ∧
    wallisFactor n ≤ (upperConstant:ℝ)*horner (n:ℝ)⁻¹ upper := by
  let L (i : ℕ) := horner (i:ℝ)⁻¹ lower
  let U (i : ℕ) := horner (i:ℝ)⁻¹ upper
  have endpoint {i : ℕ} (hi : 96 ≤ i) : (i:ℝ)⁻¹ ≤ ((1/96:ℚ):ℝ) := by
    have h : (96:ℝ) ≤ i := by exact_mod_cast hi
    simpa using inv_anti₀ (by norm_num : 0 < (96:ℝ)) h
  have htrial (i : ℕ) (hi : 96 ≤ i) := trial_order (by positivity : 0 ≤ (i:ℝ)⁻¹) (endpoint hi)
  have hstep (i : ℕ) (hi : 96 ≤ i) := trial_steps (by positivity : 0 ≤ (i:ℝ)⁻¹) (endpoint hi)
  have next (i : ℕ) (hi : 96 ≤ i) : (i:ℝ)⁻¹/(1+(i:ℝ)⁻¹) = ((i+1:ℕ):ℝ)⁻¹ := by
    have h : (i:ℝ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
    push_cast
    field_simp
  have h := wallis_anchor_enclosure (by decide : 0 < 96) L U htrial
    (fun i hi => by simpa only [L,← next i hi] using (hstep i hi).1)
    (fun i hi => by simpa only [U,← next i hi] using (hstep i hi).2) hn (k:=8192) (by decide)
  have hp := htrial 8192 (by decide)
  have hL : (lowerConstant:ℝ)*U 8192 ≤ wallisFactor 8192 := by
    rw [anchor_real]
    have hh : ((lowerConstant * horner (1/8192:ℚ) upper:ℚ):ℝ) ≤ (anchorValue:ℝ) :=
      by exact_mod_cast anchor_checked.1
    simpa [U,horner_real] using hh
  have hU : wallisFactor 8192 ≤ (upperConstant:ℝ)*L 8192 := by
    rw [anchor_real]
    have hh : (anchorValue:ℝ) ≤ ((upperConstant * horner (1/8192:ℚ) lower:ℚ):ℝ) :=
      by exact_mod_cast anchor_checked.2
    simpa [L,horner_real] using hh
  have hpN := htrial n hn
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ (wallisFactor 8192/U 8192)*L n := mul_le_mul_of_nonneg_right
        ((le_div_iff₀ (hp.1.trans_le hp.2)).mpr hL) hpN.1.le
      _ = _ := mul_comm ..
      _ ≤ _ := h.1
  · calc
      _ ≤ _ := h.2
      _ = (wallisFactor 8192/L 8192)*U n := mul_comm ..
      _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hp.1).mpr hU) (hpN.1.trans_le hpN.2).le

end CentralUnimodality.Wallis
