module

public import CentralUnimodality.QuarticLatticeLogs

/-! Sum the positive eighth-order defects of the two logarithms over
the actual free walk or bridge, including the bridge denominator. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Finset Real Set

noncomputable def eighthSum (n : ℕ) : ℝ := ∑ i ∈ range n, ((i:ℝ)+1)^8

private noncomputable def lossSum (f : ℝ → ℝ) (ω : ℝ) (n : ℕ) :=
  ∑ i ∈ range n, f (ω*((i:ℝ)+1))

private theorem segment {ω : ℝ} {n k : ℕ} (h : |ω| *(n:ℝ)≤9/8) (hk : k≤n) :
    |ω| *(k:ℝ)∈Set.Icc 0 (9/8) :=
  ⟨mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _),
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hk) (abs_nonneg _)).trans h⟩

private theorem loss_sum_bounds {f : ℝ → ℝ} {c ω : ℝ} {n : ℕ}
    (even : ∀ x, f |x|=f x) (zero : f 0=0) (m : MonotoneOn f (Set.Icc 0 (9/8)))
    (upper : ∀ x∈Set.Icc 0 (9/8), f x≤c*x^8) (h : |ω| *(n:ℝ)≤9/8) :
    0≤lossSum f ω n ∧ lossSum f ω n≤c*ω^8*eighthSum n := by
  have entry (i : ℕ) (hi : i∈range n) : 0≤f (ω*((i:ℝ)+1)) ∧
      f (ω*((i:ℝ)+1))≤c*ω^8*((i:ℝ)+1)^8 := by
    have mem := segment h (Nat.succ_le_iff.mpr (mem_range.mp hi))
    rw [Nat.cast_succ] at mem
    rw [← even,abs_mul,abs_of_nonneg (by positivity : 0≤(i:ℝ)+1)]
    have lo := m (show (0:ℝ)∈Set.Icc 0 (9/8) by norm_num) mem mem.1
    have up := upper _ mem
    rw [zero] at lo
    rw [mul_pow,← abs_pow,abs_of_nonneg (by positivity : 0≤ω^8)] at up
    exact ⟨lo,up.trans_eq (by ring)⟩
  constructor
  · exact sum_nonneg fun i hi => (entry i hi).1
  · unfold eighthSum
    rw [Finset.mul_sum]
    exact sum_le_sum fun i hi => (entry i hi).2

private theorem bridge_loss_nonneg {f : ℝ → ℝ} {ω : ℝ} {j : ℕ} (even : ∀ x, f |x|=f x)
    (m : MonotoneOn f (Set.Icc 0 (9/8))) (h : |ω| *(2*j:ℕ)≤9/8) :
    0≤lossSum f ω (2*j)-2*lossSum f ω j := by
  have cmp (i : ℕ) (hi : i∈range j) : f (ω*((i:ℝ)+1))≤f (ω*((j+i:ℕ)+1)) := by
    have ij := mem_range.mp hi
    rw [← even (ω*((i:ℝ)+1)),← even (ω*((j+i:ℕ)+1)),abs_mul,abs_mul,
      abs_of_nonneg (by positivity : 0≤(i:ℝ)+1),abs_of_nonneg (by positivity : 0≤((j+i:ℕ):ℝ)+1)]
    have small := segment h (show i+1≤2*j by omega)
    have large := segment h (show j+i+1≤2*j by omega)
    rw [Nat.cast_succ] at small large
    apply m small large
    gcongr
    exact Nat.le_add_left ..
  unfold lossSum
  rw [two_mul,sum_range_add]
  linarith only [sum_le_sum cmp]

private theorem cos_loss_abs (x : ℝ) : cosSexticLoss |x|=cosSexticLoss x := by
  rcases le_total 0 x with hx|hx
  · simp [abs_of_nonneg hx]
  · simp [abs_of_nonpos hx,cosSexticLoss,cosLoss]; ring

private theorem sinc_loss_abs (x : ℝ) : sincSexticLoss |x|=sincSexticLoss x := by
  rcases le_total 0 x with hx|hx
  · simp [abs_of_nonneg hx]
  · simp [abs_of_nonpos hx,sincSexticLoss,sincLoss]; ring

theorem free_sextic_log (ω : ℝ) {t : ℕ} (ha : |ω| *t≤9/8) :
    let defect := -freeLog ω t-freeExponent ω t-freeQuartic ω t-ω^6*sixthSum t/45
    0≤defect ∧ defect≤(1/70)*ω^8*eighthSum t := by
  have eq (n : ℕ) : -freeLog ω n-freeExponent ω n-freeQuartic ω n-ω^6*sixthSum n/45=
      lossSum cosSexticLoss ω n := by
    induction n with
    | zero => simp [freeLog,freeExponent,freeQuartic,sixthSum,fourthSum,lossSum]
    | succ n ih =>
      simp only [freeLog,freeExponent,freeQuartic,sixthSum,fourthSum,lossSum,sum_range_succ,
        Nat.cast_succ,cosSexticLoss,cosLoss] at ih ⊢
      linear_combination ih
  dsimp only
  rw [eq]
  exact loss_sum_bounds cos_loss_abs (by norm_num [cosSexticLoss,cosLoss]) cosSexticLoss_control.1
    cosSexticLoss_control.2 ha

theorem bridge_sextic_log (ω : ℝ) {j : ℕ} (ha : |ω| *(2*j:ℕ)≤9/8) :
    let defect := -bridgeLog ω j-bridgeExponent ω j-bridgeQuartic ω j-
      ω^6*(sixthSum (2*j)-2*sixthSum j)/2835
    0≤defect ∧ defect≤(1/32000)*ω^8*eighthSum (2*j) := by
  have eq (n : ℕ) (h : |ω| *(2*n:ℕ)≤9/8) :
      -bridgeLog ω n-bridgeExponent ω n-bridgeQuartic ω n-
        ω^6*(sixthSum (2*n)-2*sixthSum n)/2835=
        lossSum sincSexticLoss ω (2*n)-2*lossSum sincSexticLoss ω n := by
    induction n with
    | zero => simp [bridgeLog,bridgeExponent,bridgeQuartic,sixthSum,fourthSum,lossSum]
    | succ n ih =>
      have prev := ih ((mul_le_mul_of_nonneg_left (by exact_mod_cast (show 2*n≤2*(n+1) by omega))
        (abs_nonneg ω)).trans h)
      let b : ℝ := ω*((n:ℝ)+1)
      let c : ℝ := ω*(2*(n:ℝ)+1)
      have hb : |b|≤9/8 := by
        have m := segment h (show n+1≤2*(n+1) by omega)
        simpa only [b,abs_mul,abs_of_nonneg (by positivity : 0≤(n:ℝ)+1),Nat.cast_succ] using m.2
      have evenArg : 2*b=ω*((2*n:ℕ)+1+1:ℝ) := by dsimp only [b]; push_cast; ring
      calc
        _ = (-bridgeLog ω n-bridgeExponent ω n-bridgeQuartic ω n-
            ω^6*(sixthSum (2*n)-2*sixthSum n)/2835)+
            (sincSexticLoss (2*b)+sincSexticLoss c-2*sincSexticLoss b) := by
          rw [bridgeLog,Finset.sum_range_succ,← bridgeLog]
          change -(bridgeLog ω n+(log (cos b)+log (sinc c)-log (sinc b)))-_-_-_=_
          rw [log_cos_sinc_double hb]
          simp only [bridgeExponent,bridgeQuartic,fourthSum,sixthSum,show 2*(n+1)=2*n+1+1 by omega,
            sum_range_succ,Nat.cast_succ,Nat.cast_mul,sincSexticLoss,sincLoss,b,c]
          ring
        _ = _ := by
          rw [prev,evenArg]
          simp only [lossSum,show 2*(n+1)=2*n+1+1 by omega,sum_range_succ,Nat.cast_succ,
            Nat.cast_mul,b,c]
          ring
  have half := loss_sum_bounds sinc_loss_abs (by norm_num [sincSexticLoss,sincLoss])
    sincSexticLoss_control.1 sincSexticLoss_control.2
    ((mul_le_mul_of_nonneg_left (by exact_mod_cast (show j≤2*j by omega)) (abs_nonneg ω)).trans ha)
  have both := loss_sum_bounds sinc_loss_abs (by norm_num [sincSexticLoss,sincLoss])
    sincSexticLoss_control.1 sincSexticLoss_control.2 ha
  dsimp only
  rw [eq j ha]
  exact ⟨bridge_loss_nonneg sinc_loss_abs sincSexticLoss_control.1 ha,by linarith only [half.1,both.2]⟩

end CentralUnimodality.ReturnSplit
