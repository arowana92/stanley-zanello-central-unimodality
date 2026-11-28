module

public import CentralUnimodality.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Compare all adjacent coefficients in a packed rank interval at once.
One spare bit per digit records the sign of its own comparison. -/
@[expose] public section

namespace CentralUnimodality.PackedComparisons

private def pack (B : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n+1, f => f 0+B*pack B n (fun j => f (j+1))

private theorem pack_digit {B n : ℕ} (hB : 0<B) {f : ℕ→ℕ}
    (hf : ∀ i<n, f i<B) {i : ℕ} (hi : i<n) : (pack B n f/B^i)%B=f i := by
  induction n generalizing i f with
  | zero => omega
  | succ n IH =>
    have h₀ := hf 0 (by omega)
    cases i with
    | zero => simp [pack,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt h₀]
    | succ i =>
      rw [pow_succ',← Nat.div_div_eq_div_mul,pack,Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt h₀,zero_add]
      exact IH (fun j hj => hf (j+1) (by omega)) (by omega)

private theorem pack_clip (B n x : ℕ) :
    pack B n (fun j => x/B^j%B) = x%B^n := by
  induction n generalizing x with
  | zero => simp [pack,Nat.mod_one]
  | succ n IH =>
    rw [pack,show (fun j => x/B^(j+1)%B)=(fun j => (x/B)/B^j%B) by
      funext j; rw [pow_succ',Nat.div_div_eq_div_mul],IH,pow_succ']
    simpa only [pow_zero,Nat.div_one] using (Nat.mod_mul (x:=x) (a:=B) (b:=B^n)).symm

private theorem pack_constant {B : ℕ} (hB : 0<B) (n u : ℕ) :
    (B-1)*pack B n (fun _ => u)+u=B^n*u := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    have he : B-1+1=B := by omega
    rw [pack,pow_succ']
    nlinarith only [congrArg (B*·) ih,congrArg (·*u) he]

/-- The high bit of each of the first n base-2^(w+1) digits. -/
def guards (w n : ℕ) := (((1 <<< ((w+1)*n))-1)/((1 <<< (w+1))-1)) <<< w

private theorem guards_pack (w n : ℕ) :
    guards w n=pack (2^(w+1)) n (fun _ => 2^w) := by
  let B : ℕ := 2^(w+1)
  have hB : 1<B := Nat.one_lt_pow (by omega) (by decide)
  have ones := pack_constant (by omega : 0<B) n 1
  have H : (B^n-1)/(B-1)=pack B n (fun _ => 1) := by
    rw [mul_one] at ones
    exact Nat.div_eq_of_eq_mul_right (by omega) (by omega)
  have scaled (j : ℕ) : pack B j (fun _ => 1)*2^w=pack B j (fun _ => 2^w) := by
    induction j with
    | zero => simp [pack]
    | succ j IH => simp only [pack,Nat.add_mul,one_mul,mul_assoc,IH]
  simp only [guards,Nat.shiftLeft_eq,one_mul,pow_mul]
  exact H ▸ scaled n

private theorem pack_gap (B n g : ℕ) (x y : ℕ→ℕ) (hx : ∀ i<n, x i≤g) :
    pack B n (fun _ => g)+pack B n y-pack B n x =
      pack B n (fun j => g+y j-x j) := by
  suffices H : pack B n (fun _ => g)+pack B n y =
      pack B n (fun j => g+y j-x j)+pack B n x by omega
  induction n generalizing x y with
  | zero => simp [pack]
  | succ n IH =>
    have hh := IH (fun j => x (j+1)) (fun j => y (j+1)) (fun j hj => hx (j+1) (by omega))
    have h₀ : g+y 0-x 0+x 0=g+y 0 := by have := hx 0 (by omega); omega
    simp only [pack]; nlinarith only [congrArg (B*·) hh,h₀]

private theorem high_bit {w n i : ℕ} {f : ℕ→ℕ} (hi : i<n) (hf : ∀ j<n, f j<2^(w+1)) :
    (pack (2^(w+1)) n f).testBit (w+(w+1)*i)=(f i).testBit w := by
  rw [Nat.testBit_add,pow_mul]
  have H := Nat.testBit_mod_two_pow (pack (2^(w+1)) n f / (2^(w+1))^i) (w+1) w
  simp only [show w<w+1 by omega,decide_true,Bool.true_and] at H
  rw [← H,pack_digit (by positivity) hf hi]

def segment (w d x : ℕ) := x % (1 <<< ((w+1)*d))

def ordered (w d x y : ℕ) : Bool :=
  let G := guards w d
  decide ((G+segment w d y-segment w d x) &&& G = G)

theorem ordered_sound {w d x y : ℕ} (hx : ∀ i<d, digit (w+1) x i<2^w)
    (hy : ∀ i<d, digit (w+1) y i<2^w) (H : ordered w d x y=true) :
    ∀ i<d, digit (w+1) x i ≤ digit (w+1) y i := by
  let B : ℕ := 2^(w+1)
  let g : ℕ := 2^w
  let X := digit (w+1) x
  let Y := digit (w+1) y
  have hB : 0<B := by dsimp only [B]; positivity
  have hg : 0<g := by dsimp only [g]; positivity
  have double : B=g+g := by dsimp only [B,g]; rw [pow_succ]; omega
  have seg (v : ℕ) : segment w d v=pack B d (digit (w+1) v) := by
    have he : digit (w+1) v=(fun j => v/B^j%B) := by
      funext j; simp only [digit,Nat.shiftRight_eq_div_pow,pow_mul,B]
    rw [he]
    simpa only [segment,Nat.shiftLeft_eq,one_mul,pow_mul,B] using (pack_clip B d v).symm
  have delta := pack_gap B d g X Y (fun i hi => (hx i hi).le)
  have hh := of_decide_eq_true H
  change (_ &&& guards w d)=guards w d at hh
  rw [seg,seg,guards_pack,delta] at hh
  intro i hi
  have hflag := congrArg (fun t : ℕ => t.testBit (w+(w+1)*i)) hh
  have hbnd (j : ℕ) (hj : j<d) : g+Y j-X j<B := by
    have h : Y j<g := hy j hj; omega
  have ha := high_bit (w:=w) (f:=fun j => g+Y j-X j) hi hbnd
  have hguard := high_bit (w:=w) (f:=fun _ => 2^w) hi (fun _ _ => show g<B by omega)
  simp only [Nat.testBit_and] at hflag
  rw [ha,hguard,Nat.testBit_two_pow_self,Bool.and_true] at hflag
  have h := Nat.ge_two_pow_of_testBit hflag
  change g ≤ g+Y i-X i at h
  change X i ≤ Y i
  omega

end CentralUnimodality.PackedComparisons
