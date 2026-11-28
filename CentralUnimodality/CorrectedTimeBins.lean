module

public import CentralUnimodality.LocalizedReturnBins

/-! Closed half-unit bins for the two arguments of the corrected split
and for the time remaining after the first return. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Set

noncomputable def halfInterval (i : ℕ) := Icc ((i:ℝ)/2) ((i+1:ℕ)/2:ℝ)
noncomputable def cappedBin (i : ℕ) (y : ℝ) := min i ⌊2*y⌋₊

theorem mem_capped_bin {i : ℕ} {y : ℝ} (hy : 0≤y) (endpt : 2*y≤(i:ℝ)+1) :
    y∈halfInterval (cappedBin i y) := by
  have lo := Nat.floor_le (show 0≤2*y by linarith)
  have hi := Nat.lt_floor_add_one (2*y)
  unfold cappedBin halfInterval
  by_cases h : i≤⌊2*y⌋₊
  · rw [min_eq_left h]
    have s : (i:ℝ)≤⌊2*y⌋₊ := by exact_mod_cast h
    constructor <;> push_cast <;> linarith only [lo,s,endpt]
  · rw [min_eq_right (by omega)]
    constructor <;> push_cast <;> linarith only [lo,hi]

theorem split_half_bins {i : ℕ} {v a b : ℝ} (hv : v∈halfInterval i)
    (ha : 0≤a) (hb : 0≤b) (ab : a+b=v) :
    ∃ p q : ℕ, p≤ i ∧ q≤ i-p ∧ i≤p+q+1 ∧ a∈halfInterval p ∧ b∈halfInterval q := by
  have lower := hv.1
  have upper := hv.2
  change (i:ℝ)/2≤v at lower
  change v≤(i+1:ℕ)/2 at upper
  push_cast at upper
  let p := cappedBin i a
  let q := cappedBin (i-p) b
  have pi : p≤ i := min_le_left ..
  have qi : q≤ i-p := min_le_left ..
  have ma : a∈halfInterval p := mem_capped_bin ha (by linarith only [upper,hb,ab])
  have ml : (p:ℝ)/2≤a := ma.1
  have mb : b∈halfInterval q := by
    apply mem_capped_bin hb
    rw [Nat.cast_sub pi]; linarith only [upper,ml,ab]
  refine ⟨p,q,pi,qi,?_,ma,mb⟩
  by_cases saturated : i-p≤⌊2*b⌋₊
  · have eq : q=i-p := min_eq_left saturated
    omega
  by_cases left : i≤⌊2*a⌋₊
  · have eq : p=i := min_eq_left left
    omega
  have eqp : p=⌊2*a⌋₊ := min_eq_right (by omega)
  have eqq : q=⌊2*b⌋₊ := min_eq_right (by omega)
  have ap : 2*a<(p:ℝ)+1 := eqp ▸ Nat.lt_floor_add_one _
  have bq : 2*b<(q:ℝ)+1 := eqq ▸ Nat.lt_floor_add_one _
  have lt : (i:ℝ)<(p:ℝ)+q+2 := by linarith only [lower,ab,ap,bq]
  have cast : i<p+q+2 := by exact_mod_cast lt
  omega

theorem return_bin_index {N j i : ℕ} (n0 : 0<N) (le : j≤N) {u : ℝ} (hu : u∈halfInterval i) :
    let t := ((N-j:ℕ):ℝ)*(u/N)
    let k := cappedBin i t
    t∈halfInterval k ∧ k≤ i ∧
    (20*j≤N → 19*i/20≤k) ∧
    (N≤20*j → k≤19*(i+1)/20 ∧ (N:ℝ)/20≤j ∧
      (0< i → (N:ℝ)*(1-((k:ℝ)+1)/i)≤j)) := by
  let t := ((N-j:ℕ):ℝ)*(u/N)
  let k := cappedBin i t
  change t∈halfInterval k ∧ k≤ i ∧ _
  have np : (0:ℝ)<N := by exact_mod_cast n0
  have low := hu.1
  have high := hu.2
  change (i:ℝ)/2≤u at low
  change u≤(i+1:ℕ)/2 at high
  push_cast at high
  have u0 : 0≤u := by linarith only [low,Nat.cast_nonneg (α:=ℝ) i]
  have t0 : 0≤t := mul_nonneg (Nat.cast_nonneg _) (div_nonneg u0 np.le)
  have id : t*(N:ℝ)=((N:ℝ)-j)*u := by dsimp only [t]; rw [Nat.cast_sub le]; field_simp
  have tu : t≤u := by apply le_of_mul_le_mul_right (a:=(N:ℝ)) _ np; rw [id]; nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) j) u0]
  have mem : t∈halfInterval k := mem_capped_bin t0 (by linarith only [tu,high])
  refine ⟨mem,min_le_left ..,?_,?_⟩
  · intro early
    have jr : 20*(j:ℝ)≤N := by exact_mod_cast early
    have product := mul_le_mul_of_nonneg_right jr u0
    have slope : 19*u/20≤t := by apply le_of_mul_le_mul_right (a:=(N:ℝ)) _ np; rw [id]; linarith only [product]
    have bound : ((19*i/20:ℕ):ℝ)≤19*(i:ℝ)/20 := by
      have h := Nat.div_mul_le_self (19*i) 20
      have r : ((19*i/20:ℕ):ℝ)*20≤19*i := by exact_mod_cast h
      linarith only [r]
    apply le_min (by omega) (Nat.le_floor _)
    linarith only [bound,slope,low]
  · intro late
    change k≤19*(i+1)/20 ∧ (N:ℝ)/20≤j ∧ (0< i → (N:ℝ)*(1-((k:ℝ)+1)/i)≤j)
    have jr : (N:ℝ)≤20*j := by exact_mod_cast late
    have prod := mul_le_mul_of_nonneg_right jr u0
    have slope : t≤19*u/20 := by apply le_of_mul_le_mul_right (a:=(N:ℝ)) _ np; rw [id]; linarith only [prod]
    have kl : (k:ℝ)/2≤t := mem.1
    have kh : t≤((k:ℝ)+1)/2 := by exact_mod_cast mem.2
    have kp : (20:ℝ)*k≤19*((i:ℝ)+1) := by linarith only [kl,slope,high]
    have nn : 20*k≤19*(i+1) := by exact_mod_cast kp
    refine ⟨by omega,by linarith only [jr],?_⟩
    intro ip
    have ip' : (0:ℝ)< i := by exact_mod_cast ip
    have a := mul_le_mul_of_nonneg_right kh np.le
    have jle : (j:ℝ)≤N := by exact_mod_cast le
    have b := mul_le_mul_of_nonneg_left low (sub_nonneg.mpr jle)
    rw [id] at a
    apply le_of_mul_le_mul_right (a:=(i:ℝ)) _ ip'
    rw [show ((N:ℝ)*(1-((k:ℝ)+1)/i))*i=N*((i:ℝ)-(k+1)) by field_simp]
    linarith only [a,b]

end CentralUnimodality.ReturnSplit
