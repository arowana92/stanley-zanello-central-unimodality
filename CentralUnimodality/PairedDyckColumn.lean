module

public import CentralUnimodality.FiniteDyckComparison
import Mathlib.Tactic.Ring

/-! At even time, index height 2h by h. A descent from 2h to
zero contributes at least h(h-1) area. Thus a cutoff in area also
cuts the transfer matrix off at a fixed height, independently of length. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock

def bridgeValue (B s h : ℕ) : ℕ :=
  transfer B (2*s) (2*h) (fun t => if t=0 then 1 else 0)

private theorem paired_ground (B s : ℕ) :
    bridgeValue B (s+1) 0=bridgeValue B s 0+B*bridgeValue B s 1 := by
  simp only [bridgeValue,show 2*(s+1)=2*s+1+1 by omega,transfer]
  simp; omega

private theorem paired_above (B s h : ℕ) :
    bridgeValue B (s+1) (h+1)=
      B^(2*h)*bridgeValue B s h +
      (B^(2*h+1)+B^(2*h+2))*bridgeValue B s (h+1) +
      B^(2*h+3)*bridgeValue B s (h+2) := by
  simp only [bridgeValue,show 2*(s+1)=2*s+1+1 by omega,transfer]
  simp only [ite_eq_right (show 2*(h+1)≠0 by omega),ite_eq_right (show 2*(h+1)+1≠0 by omega),
    ite_eq_right (show 2*(h+1)-1≠0 by omega),
    show (2*(h+1)+1)/2=h+1 by omega,show (2*(h+1)-1)/2=h by omega,
    show 2*(h+1)+1+1=2*(h+2) by omega,show 2*(h+1)+1-1=2*(h+1) by omega,
    show 2*(h+1)-1+1=2*(h+1) by omega,show 2*(h+1)-1-1=2*h by omega,
    show 2*(h+2)/2=h+2 by omega,show 2*(h+1)/2=h+1 by omega,show 2*h/2=h by omega]
  simp only [pow_add,pow_mul]
  ring

private theorem bridge_divisible (B s h : ℕ) : B^(h*(h-1)) ∣ bridgeValue B s h := by
  induction s generalizing h with
  | zero =>
    by_cases hh : h=0 <;> simp [bridgeValue,transfer,hh]
  | succ s ih =>
    cases h with
    | zero => simp
    | succ h =>
      rw [paired_above]
      apply dvd_add
      · apply dvd_add
        · have H := Nat.mul_dvd_mul_left (B^(2*h)) (ih h)
          rw [← pow_add] at H
          convert H using 2
          cases h <;> simp; ring
        · exact dvd_mul_of_dvd_right (ih (h+1)) _
      · apply dvd_mul_of_dvd_right _ _
        exact (pow_dvd_pow B (by
          rw [show h+2-1=h+1 by omega,show h+1-1=h by omega]
          nlinarith : (h+1)*(h+1-1)≤(h+2)*(h+2-1))).trans (ih (h+2))

def shiftSum (b h left atH right : ℕ) : ℕ :=
  if h=0 then atH+(right <<< b)
  else (left+(atH <<< b)+(atH <<< (2*b))+(right <<< (3*b))) <<< (b*(2*h-2))

def pairedEntries (b M : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _, _ => []
  | k+1, h, left, a =>
    (shiftSum b h left (a.headD 0) (a.tail.headD 0)%M)::
      pairedEntries b M k (h+1) (a.headD 0) a.tail

def pairedNext (b M H : ℕ) (r : List ℕ) := pairedEntries b M H 0 0 r

def pairedRows (b M H : ℕ) : ℕ → List ℕ
  | 0 => [1]
  | s+1 => pairedNext b M H (pairedRows b M H s)

private theorem entries_at (b M k h left : ℕ) (a : List ℕ) (j : ℕ) (hj : j<k) :
    entry (pairedEntries b M k h left a) j =
      shiftSum b (h+j) (if j=0 then left else entry a (j-1)) (entry a j) (entry a (j+1))%M := by
  have head (r : List ℕ) : r.headD 0=entry r 0 := by cases r <;> rfl
  have tail (r : List ℕ) (i : ℕ) : entry r.tail i=entry r (i+1) := by cases r <;> rfl
  induction k generalizing h left a j with
  | zero => omega
  | succ k ih =>
    cases j with
    | zero => change shiftSum b h left (a.headD 0) (a.tail.headD 0)%M=_
              rw [head,head,tail]; simp only [Nat.add_zero,ite_true]
    | succ j =>
      change entry (pairedEntries b M k (h+1) (a.headD 0) a.tail) j=_
      rw [ih _ _ _ _ (by omega),head,tail,tail,show h+1+j=h+(j+1) by omega]
      by_cases z : j=0
      · simp [z,tail]
      · simp [z,tail,show j-1+1=j by omega]

private theorem outside_zero {b M H s h : ℕ} (ht : H≤h) (hH : 0<H) :
    entry (pairedRows b M H s) h=0 := by
  cases s with
  | zero => cases h <;> first | omega | rfl
  | succ s =>
    have len (k i left : ℕ) (a : List ℕ) : (pairedEntries b M k i left a).length=k := by
      induction k generalizing i left a with
      | zero => rfl
      | succ k ih => simp [pairedEntries,ih]
    exact (show ((pairedEntries b M H 0 0 (pairedRows b M H s))[h]?).getD 0=0 by
      rw [List.getElem?_eq_none (by rw [len]; omega)]; rfl)

private theorem shifted_above (b h x y z : ℕ) :
    shiftSum b (h+1) x y z =
      (2^b)^(2*h)*x+((2^b)^(2*h+1)+(2^b)^(2*h+2))*y+(2^b)^(2*h+3)*z := by
  simp only [shiftSum,ite_eq_right (show h+1≠0 by omega),Nat.shiftLeft_eq,
    show 2*(h+1)-2=2*h by omega,show 2*b=b*2 by omega,show 3*b=b*3 by omega,
    Nat.pow_mul,Nat.pow_add]
  ring

theorem paired_congr {b e H : ℕ} (height : e+1≤H*(H-1)) (s h : ℕ) :
    entry (pairedRows b (2^(b*(e+1))) H s) h ≡ bridgeValue (2^b) s h [MOD 2^(b*(e+1))] := by
  have hH : 0<H := Nat.pos_of_ne_zero (by rintro rfl; simp at height)
  induction s generalizing h with
  | zero =>
    cases h with
    | zero => rfl
    | succ h => simp [pairedRows,entry,bridgeValue,transfer,Nat.ModEq.refl]
  | succ s ih =>
    by_cases inside : h<H
    · rw [pairedRows,pairedNext,entries_at _ _ _ _ _ _ _ inside,Nat.zero_add]
      apply (Nat.mod_modEq ..).trans
      cases h with
      | zero =>
        simp only [shiftSum,ite_true,Nat.shiftLeft_eq,paired_ground,Nat.zero_add]
        rw [Nat.mul_comm _ (2^b)]
        exact (ih 0).add ((ih 1).mul_left _)
      | succ h =>
        rw [shifted_above,paired_above]
        simp only [ite_eq_right (Nat.succ_ne_zero _),Nat.add_sub_cancel]
        exact (((ih h).mul_left _).add ((ih (h+1)).mul_left _)).add ((ih (h+2)).mul_left _)
    · rw [outside_zero (by omega) hH]
      apply Dvd.dvd.zero_modEq_nat
      rw [Nat.pow_mul]
      exact (pow_dvd_pow _ (height.trans (Nat.mul_le_mul (by omega) (by omega)))).trans
        (bridge_divisible (2^b) (s+1) h)

theorem paired_digit {b e H s i : ℕ} (height : e+1≤H*(H-1)) (bits : 2*s<b) (hi : i≤e) :
    digit b (entry (pairedRows b (2^(b*(e+1))) H s) 0) i=(dyckPoly s).coeff i := by
  rw [dyck_eq_transfer]
  apply kernel_digit_of_congr (t:=0) bits hi
  rw [eval_kernel]
  exact paired_congr height s 0

def checkPairedDycks (b e H : ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | k+1, n, row => (decide (dyckCut n≤e) && checkReflection b (dyckCut n) (entry row 0)) &&
      checkPairedDycks b e H k (n+1) (pairedNext b (2^(b*(e+1))) H row)

theorem checkPairedDycks_sound {b e H k n l : ℕ} (height : e+1≤H*(H-1)) (bits : 2*(n+k-1)<b)
    (ok : checkPairedDycks b e H k n (pairedRows b (2^(b*(e+1))) H n)=true)
    (hl : n≤l) (hu : l<n+k) : ReflectedCoeffs (dyckPoly l) (⌈dyckLower l⌉₊:ℕ) := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    simp only [checkPairedDycks,Bool.and_eq_true,decide_eq_true_eq] at ok
    by_cases he : l=n
    · subst l
      intro i j hij hsum
      have hcut := ceil_dyck_le_cut n
      have := ok.1.1
      have test := checkReflection_sound ok.1.2 hij (by omega)
      rwa [paired_digit height (by omega) (by omega),paired_digit height (by omega) (by omega)] at test
    · exact ih (by omega) ok.2 (by omega) (by omega)

end CentralUnimodality.HeightBlock
