module

public import CentralUnimodality.ParityBins

/-! A 400-bin upper sum for first hits after one tenth of the block. The
same bound applies at every block length above the stated minimum. -/
@[expose] public section

namespace CentralUnimodality

def lateHits (a L : ℕ) := (Finset.range (L+1)).filter fun j => L < 10*j ∧ j%2=a%2

noncomputable def binRemainder (M i : ℕ) : ℝ :=
  max 0 (1-((i:ℝ)+1)/400-2/(M:ℝ))

noncomputable def binCharge (c : ℝ) (M low i : ℕ) : ℝ :=
  if low ≤ i then Real.exp (-(c*(binRemainder M i)^3))/(4*i) else 0

private theorem binCharge_nonneg (c : ℝ) (M low i : ℕ) : 0 ≤ binCharge c M low i := by
  unfold binCharge
  split <;> positivity

/-- Bounds for the site index and the unused fraction of the block at each
microcell in the parity split. -/
private theorem slot_ratios {M L j h low : ℕ} (hM : 0 < M) (hML : M ≤ L) (hj : j ≤ L)
    (h₂ : 2 ≤ j) (hlate : L < 10*j) (hh : h < 2*400)
    (hlo : (low:ℝ)/400+2/(M:ℝ) ≤ 1/10) :
    let i := cellSlot 400 j h / L
    low ≤ i ∧ (i:ℝ)*L ≤ 400*j ∧ binRemainder M i ≤ ((L-j:ℕ):ℝ)/L := by
  let s := cellSlot 400 j h
  let i := s/L
  have hL : 0 < L := by omega
  have hp : (0:ℝ) < L := by exact_mod_cast hL
  have hmp : (0:ℝ) < M := by exact_mod_cast hM
  obtain ⟨hb,ht⟩ := cellSlot_bounds h₂ hh
  have hlow : 400*((j:ℝ)-2) ≤ s := by
    have h : (400:ℝ)*((j-2:ℕ):ℝ) ≤ s := by exact_mod_cast hb
    simpa only [Nat.cast_sub h₂,Nat.cast_ofNat] using h
  have hhigh : (s:ℝ) < 400*j := by exact_mod_cast ht
  have hi : (i:ℝ)*L ≤ s := by exact_mod_cast Nat.div_mul_le_self s L
  have hs : (s:ℝ) < (i+1)*(L:ℝ) := by
    exact_mod_cast (Nat.lt_mul_div_succ s hL |> (fun v => by simpa [i,Nat.mul_comm] using v) : s < (i+1)*L)
  have hfrac : 2/(L:ℝ) ≤ 2/(M:ℝ) := div_le_div_of_nonneg_left (by norm_num) hmp (by exact_mod_cast hML)
  have hlate' : (L:ℝ) < 10*j := by exact_mod_cast hlate
  have hlo' : (low:ℝ)/400 + 2/(L:ℝ) ≤ 1/10 := by linarith only [hlo,hfrac]
  have hloL := mul_le_mul_of_nonneg_right hlo' hp.le
  field_simp at hloL
  have hslo : (low:ℝ)*L ≤ s := by linarith only [hloL,hlate',hlow]
  have hindex := (Nat.le_div_iff_mul_le hL).mpr (by exact_mod_cast hslo : low*L ≤ s)
  change low ≤ i ∧ _ ∧ _
  refine ⟨hindex,hi.trans hhigh.le,?_⟩
  unfold binRemainder
  apply max_le (by positivity)
  rw [Nat.cast_sub hj]
  have hpart : 1-((i:ℝ)+1)/400-2/(L:ℝ) ≤ ((L:ℝ)-j)/L := by
    apply (le_div_iff₀ hp).mpr
    field_simp
    nlinarith only [hlow,hs]
  linarith only [hpart,hfrac]

theorem late_hit_sum {c : ℝ} (hc : 0 ≤ c) {M L low a : ℕ}
    (hM : 20 ≤ M) (hML : M ≤ L) (hlow : 0 < low) (ha : 0 < a)
    (hlo : (low:ℝ)/400+2/(M:ℝ) ≤ 1/10) :
    (∑ j ∈ lateHits a L, ((hitWords a j).card/(2:ℝ)^j)*
      Real.exp (-(c*(((L-j:ℕ):ℝ)/L)^3))) ≤ ∑ i ∈ Finset.range 400, binCharge c M low i := by
  let u (j : ℕ) := ((hitWords a j).card/(2:ℝ)^j)*Real.exp (-(c*(((L-j:ℕ):ℝ)/L)^3))
  let F (i : ℕ) := (800/(L:ℝ))*binCharge c M low i
  have hL : 0 < L := by omega
  have hLp : (0:ℝ) < L := by exact_mod_cast hL
  have mem {j : ℕ} (hj : j ∈ lateHits a L) : j ≤ L ∧ L < 10*j ∧ j%2=a%2 := by
    simpa [lateHits] using hj
  have hsum := parity_bins (B := 400) (p := a%2) hL (lateHits a L) (fun j hj =>
    ⟨by have := (mem hj).2.1; omega,(mem hj).1,(mem hj).2.2⟩) u F
    (fun i _ => mul_nonneg (by positivity) (binCharge_nonneg ..))
  have hu : ∀ j ∈ lateHits a L, ∀ h < 2*400, u j ≤ F (cellSlot 400 j h/L) := by
    intro j hj h hh
    obtain ⟨hm,hl,_⟩ := mem hj
    let i := cellSlot 400 j h/L
    obtain ⟨hi,hdiv,hrem⟩ := slot_ratios (by omega : 0 < M) hML hm (by omega) hl hh hlo
    change low ≤ i at hi
    have hip : (0:ℝ) < i := by exact_mod_cast (hlow.trans_le hi)
    have hjp : (0:ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hmass := first_hit_half ha (by omega : 0 < j)
    have hsite : 1/(2*(j:ℝ)) ≤ (800/(L:ℝ))*(1/(4*i)) := by
      change (i:ℝ)*L ≤ 400*j at hdiv
      field_simp
      nlinarith only [hdiv]
    have hexp := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_max_left ..) hrem 3) hc))
    dsimp [u,F]
    change _ ≤ (800/(L:ℝ))*binCharge c M low i
    rw [binCharge,ite_eq_left hi]
    calc
      _ ≤ ((800/(L:ℝ))*(1/(4*i)))*Real.exp (-(c*(binRemainder M i)^3)) :=
        mul_le_mul (hmass.trans hsite) hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hr := hsum hu
  dsimp only [F] at hr
  rw [← Finset.mul_sum,← mul_assoc,show (L:ℝ)*(800/(L:ℝ)) = 800 by field_simp] at hr
  norm_num at hr
  change (∑ j ∈ lateHits a L, u j) ≤ _
  linarith only [hr]

end CentralUnimodality
