module

public import CentralUnimodality.DiscountedLiveCap
public import CentralUnimodality.PinnedPrefixSplit

/-! Two outer fifths of a centered first-passage bridge, with discounted
survival on both pieces and the Fourier endpoint bound on its middle. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem sharp_centered_bridge {d a q : ℕ} {c : ℝ} (hc : 0≤c) (hlen : a+q+a=2*d)
    (hq : 80≤q) (hcap : c*d≤21/100) :
    (∑ w∈hitWords 1 (2*d+1),signMass c (c*d) w) ≤
      live c (c*d) a 1*upChance (c*d)*live c (c*d-c) a 1*((43/50)/√q) := by
  have hdis (j : ℤ) : (∑ w∈(words q).filter (fun w => displacement w=j),signMass c (c*d-c*a) w)≤(43/50)/√q := by
    let u := c*d-c*a
    let k := ((q:ℤ)-j)/2
    have h₁ : (∑ w∈(words q).filter (fun w => displacement w=j),signMass c u w)≤downMass c u q k := by
      rw [Finset.sum_filter,downMass]
      apply Finset.sum_le_sum
      intro w hw
      have H := displacement_length w
      rw [mem_words.mp hw] at H
      dsimp only [k]; split_ifs <;> first | exact le_rfl | exact (signMass_pos ..).le | omega
    have h₂ := endpoint_cap_numbers false c u hq k (by
      intro i hi
      have hl : (a:ℝ)+i≤2*d := by exact_mod_cast (show a+i≤2*d by omega)
      have hsite : |u-c*i|≤21/100 := abs_le.mpr ⟨by dsimp only [u]; linarith only [mul_le_mul_of_nonneg_left hl hc,hcap],
        by dsimp only [u]; linarith only [hcap,mul_nonneg hc (Nat.cast_nonneg (α:=ℝ) a),mul_nonneg hc (Nat.cast_nonneg (α:=ℝ) i)]⟩
      have h := chance_interval hsite
      change 119/500≤_
      nlinarith only [mul_nonneg (sub_nonneg.mpr h.1) (sub_nonneg.mpr h.2),congrArg (upChance (-(u-c*i))*·) (up_total (u-c*i))])
    exact h₁.trans ((le_div_iff₀ (sqrt_pos.mpr (by exact_mod_cast (show 0<q by omega) : (0:ℝ)<q))).mpr h₂)
  have H := first_hit_three_blocks c (c*d) a q a hdis
  dsimp only at H
  rwa [hlen,Nat.cast_mul,Nat.cast_ofNat,show c*(2*(d:ℝ))-c*d=c*d by ring] at H

/-- The upper time endpoint and upper label tilt can both be outward
bounds. Only the lengths of the two retained pieces enter the discount. -/
theorem fifths_hit_budget {m d : ℕ} (hm : 4096≤m) {v e c lam : ℝ} (hc : 0≤c)
    (hlam : 2*c*((m:ℝ)*√m)≤lam) (hl : v*m≤2*(d:ℝ)+1) (hh : 2*(d:ℝ)+1≤e*m)
    (hβ : lam*e/4≤(21/100)*64) (houter : 0<v/5-2/4096)
    (hinner : 80≤(3*v/5-1/4096)*m) :
    let β := lam*e/4
    let f := v/5-2/4096
    let g := 3*v/5-1/4096
    (∑ w∈hitWords 1 (2*d+1),signMass c (c*d) w) ≤
      (1/2+β/128)*(discountedLive β f)^2*(43/50)/(√g*((m:ℝ)*√m)) := by
  let a := 2*d/5
  let q := 2*d-2*a
  let β := lam*e/4
  let f := v/5-2/4096
  let g := 3*v/5-1/4096
  let s := √(m:ℝ)
  have hM : (4096:ℝ)≤m := by exact_mod_cast hm
  have hm' : (0:ℝ)<m := by linarith
  have hs : 64≤s := (le_sqrt (by norm_num) hm'.le).mpr (by linarith only [hM])
  have hs' : 0<s := by linarith
  have he : 0≤e := by
    by_contra! H; linarith only [mul_nonpos_of_nonpos_of_nonneg H.le hm'.le,hh,Nat.cast_nonneg (α:=ℝ) d]
  have hcap : c*d*s≤β := by
    dsimp only [β,s]
    nlinarith only [mul_le_mul_of_nonneg_right hlam he,
      mul_le_mul_of_nonneg_right (show 2*(d:ℝ)≤e*m by linarith only [hh]) (mul_nonneg hc hs'.le)]
  have hcd : 0≤c*d := by positivity
  have hβ' : 0≤β := (mul_nonneg hcd hs'.le).trans hcap
  have hdiv : β/s≤21/100 := (div_le_iff₀ hs').mpr (hβ.trans (by linarith only [hs]))
  have huc : c*d≤β/s := (le_div_iff₀ hs').mpr hcap
  have hprob : upChance (c*d)≤1/2+β/128 := by
    nlinarith only [up_drift (c*d),up_total (c*d),tanh_le_linear hcd,hcap,mul_le_mul_of_nonneg_left hs hcd]
  have hl₁ : 2*(d:ℝ)≤5*a+4 := by exact_mod_cast (show 2*d≤5*a+4 by dsimp [a]; omega)
  have hl₂ : 6*(d:ℝ)≤5*q := by exact_mod_cast (show 6*d≤5*q by dsimp [q,a]; omega)
  have ha : f*m≤a := by dsimp only [f]; linarith only [hl,hl₁,hM]
  have hq : g*m≤q := by dsimp only [g]; linarith only [hl,hl₂,hM]
  have hg : 0<g := by
    change 80≤g*m at hinner
    by_contra! H; linarith only [hinner,mul_nonpos_of_nonpos_of_nonneg H hm'.le]
  have hq' : 80≤q := by exact_mod_cast hinner.trans hq
  have hqroot : √g*s≤√(q:ℝ) := by rw [show √g*s=√(g*m) from (sqrt_mul hg.le _).symm]; exact sqrt_le_sqrt hq
  have hlen : a+q+a=2*d := by dsimp [q,a]; omega
  let F := discountedLive β f
  have hF : 0≤F := by dsimp [F,discountedLive]; positivity
  have liveB (u : ℝ) (hu : u≤c*d) : live c u a 1≤F/s :=
    discounted_parameter_survival (m:=m) (by omega) houter ha hβ' (hdiv.trans (by norm_num))
      (fun i _ => by linarith only [hu,huc,mul_nonneg hc (Nat.cast_nonneg (α:=ℝ) i)])
  have hC : 0≤1/2+β/128 := by positivity
  have H := sharp_centered_bridge hc hlen hq' (huc.trans hdiv)
  have hout := mul_le_mul (mul_le_mul (liveB _ le_rfl) hprob (by unfold upChance; positivity) (by positivity))
    (liveB (c*d-c) (by linarith only [hc])) (live_nonneg ..) (by positivity)
  have hQ := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤43/50) (mul_pos (sqrt_pos.mpr hg) hs') hqroot
  apply H.trans ((mul_le_mul hout hQ (by positivity) (by positivity)).trans_eq _)
  have heq : (m:ℝ)*s=s^3 := by dsimp [s]; rw [pow_succ,sq_sqrt hm'.le]
  change F/s*(1/2+β/128)*(F/s)*((43/50)/(√g*s))=(1/2+β/128)*F^2*(43/50)/(√g*((m:ℝ)*s))
  rw [heq]; ring

end CentralUnimodality.MarkedExcursion
