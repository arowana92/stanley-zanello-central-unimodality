import CentralUnimodality
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let permitted : List Name := [``propext, ``Quot.sound, ``Classical.choice]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    if (`CentralUnimodality).isPrefixOf env.header.moduleNames[idx]! then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a => !(permitted.contains a)
      unless extra.isEmpty do
        throwError "{name} depends on unapproved axioms {extra}"
      checked := checked + 1
  if checked == 0 then throwError "no CentralUnimodality declarations found"
  logInfo m!"Audited {checked} project declarations."


open CentralUnimodality

example {n : ℕ} (hn : n ≤ 63) :
    UnimodalOn (rankCount (2*n)) 0 (n*n) ∧
    UnimodalOn (rankCount (2*n+1)) 0 (n*(n+1)) := central_through_63 hn

example (n δ : ℕ) (hδ : δ ≤ 1) (μ : List ℕ) :
    μ ∈ containedPartitions n δ ↔ InsideStaircase n δ μ :=
  mem_containedPartitions hδ μ

#check Conjecture34
#print axioms central_through_63
#print axioms conjecture34_iff_staircase
#print axioms packedRow_digit
#print axioms unimodalOn_of_curvature

example (n δ : ℕ) (hδ : δ ≤ 1) (F : ℤ → ℤ) :
    (∑ w ∈ strictWords (2*n+δ+1), F (walkArea w)) =
      ∑ j ∈ Finset.range (n*(n+δ)+1), rankCount (2*n+δ) j •
        (F (signedAreaAtRank n δ j) + F (-signedAreaAtRank n δ j)) := signed_ranks F n δ hδ

#print axioms ReturnSplit.rising_split
#print axioms ReturnSplit.gamma_polynomial_split
#print axioms ReturnSplit.gamma_residual_bound
#print axioms amplitude_of_residual_model
#print axioms ReturnSplit.arc_polynomial
#print axioms ReturnSplit.sample_arc_bound
#print axioms ReturnSplit.free_curve_bound
#print axioms ReturnSplit.bridge_curve_bound
#print axioms ReturnSplit.signed_curve_bound
#print axioms PolynomialTrial.candidate_bounds
#print axioms PolynomialTrial.gaussian_inputs
#print axioms Witness.rankIntegral_site
#print axioms Witness.threeFifths_of_integral_signs

#print axioms lastReturn_convolution
#print axioms reflected_of_negative_sum
#print axioms firstReturn_renewal
#print axioms firstReturn_kraft

example (ω : ℝ) (V : PowerSeries ℂ) (n : ℕ) (e : ℝ)
    (h : ∀ j ≤ n, ‖PowerSeries.coeff j (fairSeries (areaCharacter ω) words -
        fairSeries (areaCharacter ω) bridges * V)‖ ≤ e) :
    ‖PowerSeries.coeff n (fairSeries (areaCharacter ω) strictWords - V)‖ ≤ 2*e :=
  fairSeries_residual_bound _ (areaCharacter_zero ω) (areaCharacter_add ω)
    (fun x => (norm_areaCharacter ω x).le) V n e h

#print axioms fourier_signed_ranks
#print axioms fourier_free_product
#print axioms fairSeries_residual_bound
#print axioms firstReturn_probability
#print axioms survival_sq_lower
#print axioms survival_sq_upper

#print axioms ballot_rank_polynomial
#print axioms dyck_convolution
#print axioms odd_ballot_convolution
#print axioms stump_convolution

example {n : ℕ} (hn : n ≤ 95) :
    UnimodalOn (rankCount (2*n)) 0 (n*n) ∧
    UnimodalOn (rankCount (2*n+1)) 0 (n*(n+1)) := central_through_95 hn

#print axioms reflected_through_191
#print axioms Witness.reflected_from_two_witnesses
#print axioms oddPart_prefix_step
#print axioms evenPart_prefix_step
#print axioms even_momentColumn
#print axioms odd_momentColumn
#print axioms momentColumn_rescale
#print axioms catalanRoot_mul_ballotBase
#print axioms sizeEuler_dyckBase

#print axioms rootPower_coeff
#print axioms MomentBase.eval_divided
#print axioms certify_moment_series

example (n r : ℕ) :
    (rankMoment n 0 r : ℚ) = r.factorial*(n.centralBinom:ℚ)*
      Laurent.ratioSum n (Laurent.evenNumerator (Laurent.lookup (Laurent.tables r).2 r)) :=
  Laurent.exact_even_moment n r

#print axioms Laurent.exact_even_moment
#print axioms Laurent.exact_odd_moment

-- The two-row corank lists are (1,2,1,1,1) and (1,2,2,2,1,1,1).
-- These values check the shift and the factor of two against the closed formulas.
example : (List.range 4).map (fun r =>
    (r.factorial:ℚ)*Nat.centralBinom 2 *
      Laurent.ratioSum 2 (Laurent.evenNumerator (Laurent.lookup (Laurent.tables r).2 r))) =
      [6,11,31,101] := by decide +kernel

example : (List.range 4).map (fun r =>
    (r.factorial:ℚ)*Nat.centralBinom 3 / 2 *
      Laurent.ratioSum 3 (Laurent.oddNumerator
        (Laurent.oddRhs (Laurent.lookup (Laurent.tables r).1) (Laurent.lookup (Laurent.tables r).2) r))) =
      [10,27,105,477] := by decide +kernel

#print axioms Wallis.uniform

#print axioms Laurent.cellNumerator_exact
#print axioms Witness.normalizedCell_exact
#print axioms Witness.weightedSum_expectation
#print axioms Witness.second_expectation
#print axioms odd_prefix_from_bounds
#print axioms even_prefix_from_bounds

-- Integrating the unit cells of the directly enumerated two-row shapes
-- gives these four unnormalized moments in each parity.
example : (List.range 4).map (Witness.rawCell 2 0) = [6,32,182,1096] := by decide +kernel
example : (List.range 4).map (Witness.rawCell 2 1) = [10,72,1654/3,4464] := by decide +kernel

#print axioms degree_sum_lower
#print axioms periodized_ranks
#print axioms recover_rank
#print axioms rank_error_of_residual
#print axioms inverse_periodicCount
#print axioms periodicCount_bounds

#print axioms normalized_corankTail
#print axioms grid_alias_reserve
#print axioms fair_bridge_sine_step
#print axioms fair_bridge_sinc_step
#print axioms Laurent.certify_cell_samples
#print axioms Laurent.rows_certify
#print axioms Witness.supplied_first_signs
#print axioms central_from_windows

#print axioms fair_inputs_after_pairs
#print axioms blockSines_identity
#print axioms blockSines_middle
#print axioms pairFactor_arc

#print axioms prefix_mean_bound
#print axioms odd_first_moment
#print axioms odd_prefix_peak_bound
#print axioms dyck_degree_le
#print axioms odd_midpoint_tail
#print axioms even_midpoint_tail
#print axioms central_from_midpoints

#print axioms intervalDecomposition_iff_reflected
#print axioms central_from_comparisons

#print axioms fair_first_hit
#print axioms first_hit_incompatible

#print axioms first_hit_expansion
#print axioms survivor_hit_total
#print axioms killed_block_bound

#print axioms killed_arc_008
#print axioms killed_arc_032
#print axioms rank_fourier_blocks
#print axioms conditional_rank_arc

#print axioms Laurent.binomial_cell
#print axioms Laurent.cachedRow_eq
#print axioms Witness.evenCells_exact
#print axioms Witness.oddCells_exact
#print axioms Witness.first_expectation
#print axioms reflected_of_unimodal
#print axioms conjecture34_of_comparisons_and_midpoints

example (hD : DyckComparisons)
    (hc : ∀ n ≥ 96, ∀ δ ≤ 1, CentralToMidpoint n δ) : Conjecture34 :=
  conjecture34_of_comparisons_and_midpoints hD hc

#print axioms pointMass_le_square
#print axioms first_hit_half
#print axioms free_cubic_block
#print axioms parity_bins
#print axioms two_inner_caps
#print axioms killed_inner_001
#print axioms killed_inner_008
#print axioms corank_inner_001
#print axioms signed_inner_frequency
#print axioms signed_outer_frequency

#print axioms inner_grid_first
#print axioms outer_grid_cap
#print axioms omitted_fourier_grid
#print axioms site_fourier_reflect
#print axioms truncation_two_orders
#print axioms full_reconstruction
#print axioms rank_truncation_two_orders

#print axioms dyck_up_heights
#print axioms area_dinv_degree
#print axioms dyck_diagonal_cutoff
#print axioms dyck_comparisons_of_diagonal_unimodality
#print axioms conjecture34_of_diagonal_unimodality_and_midpoints

#print axioms retained_inverse_pairs
#print axioms cosine_inverse_error
#print axioms residual_rank_differences
#print axioms spatial_second_difference
#print axioms spatial_group_mesh
#print axioms rank_window_of_spatial_signs

#print axioms packed_residual_coefficients
#print axioms Residual.check_sound
#print axioms dyadic_residual_bound
#print axioms interleaved_residual
#print axioms checked_half_amplitude
#print axioms DyadicAngle.bounds_sound
#print axioms SmallGrid.inputs_sound
#print axioms SmallGrid.check_sound
#print axioms SmallGrid.input_amplitude
#print axioms quadrant_input_tail
#print axioms SmallGrid.retained_quadrant_cut
#print axioms SmallGrid.cut_sound
#print axioms SmallGrid.cut_amplitude
#print axioms MeshPhase.uniform_sample_error
#print axioms MeshPhase.production_radius
#print axioms MeshPhase.derivative_dot_error
#print axioms MeshLength.checked_chord
#print axioms WeightOperators.raise_power_injective_on
#print axioms WeightOperators.reflected_finrank
#print axioms WeightOperators.dyck_comparisons_of_operators
#print axioms WeightOperators.conjecture34_of_weight_sums_and_midpoints
#print axioms Polarization.commutator
#print axioms Polarization.move_ideal
#print axioms Polarization.coinvariant_reflected
#print axioms Polarization.alternating_degree_cutoff
#print axioms Polarization.conjecture34_of_hilbert_and_midpoints
#print axioms Polarization.coinvariantSpace_iff
#print axioms Polarization.probe_kills_relations
#print axioms Polarization.quotientProbe_alternant
#print axioms Polarization.curve_nonsingular_iff
#print axioms Polarization.dyckClass_bidegree
#print axioms Polarization.dyckClass_ne_zero
#print axioms Polarization.dyck_slice_finrank_pos
#print axioms Polarization.slice_independent_of_minor
#print axioms Polarization.dyck_hilbert_of_minors_and_dimension
#print axioms Polarization.conjecture34_of_minors_dimension_and_midpoints
#print axioms MarkedExcursion.card_tail
#print axioms MarkedExcursion.heightTail_gaussian
#print axioms MarkedExcursion.area_exp_gaussian
#print axioms MarkedExcursion.signMass_total
#print axioms MarkedExcursion.centered_cosh_lower
#print axioms MarkedExcursion.fair_hit_upper
#print axioms MarkedExcursion.tilted_hit_gaussian
#print axioms MarkedExcursion.rank_step_iff
#print axioms MarkedExcursion.change_rank_tilt
#print axioms MarkedExcursion.rank_prefix_hit_bound
#print axioms MarkedExcursion.log_cosh_shift
#print axioms MarkedExcursion.meanRank_expectation
#print axioms MarkedExcursion.saddle_rank
#print axioms MarkedExcursion.joint_cost_bound
#print axioms MarkedExcursion.prefix_height_shift
#print axioms MarkedExcursion.height_laplace
#print axioms MarkedExcursion.first_hit_change_bound
#print axioms MarkedExcursion.suffix_ruin
#print axioms MarkedExcursion.first_hit_bin
#print axioms MarkedExcursion.late_hit_bin
#print axioms MarkedExcursion.change_difference_bounds
#print axioms MarkedExcursion.rank_curvature_of_tilt
#print axioms MarkedExcursion.homogeneous_live
#print axioms MarkedExcursion.hit_time_first_moment
#print axioms MarkedExcursion.prefixRank_full
#print axioms MarkedExcursion.prefixMean_exact
#print axioms MarkedExcursion.prefixVariance_exact
#print axioms MarkedExcursion.stopped_variance_bound
#print axioms MarkedExcursion.conditional_prefix_variance
#print axioms MarkedExcursion.prefixSiteMass_mixture
#print axioms MarkedExcursion.saddle_suffix_site
#print axioms MarkedExcursion.gaussian_average
#print axioms MarkedExcursion.conditional_prefix_differences
#print axioms MarkedExcursion.exp_taylor_left
#print axioms MarkedExcursion.bernoulli_gaussian_error
#print axioms MarkedExcursion.suffix_transform_words
#print axioms MarkedExcursion.suffix_rank_inversion
#print axioms MarkedExcursion.product_gaussian_error
#print axioms MarkedExcursion.suffix_small_error
#print axioms MarkedExcursion.suffix_middle_arcs
#print axioms MarkedExcursion.suffix_outer_arcs
#print axioms MarkedExcursion.suffix_saddle_parameters
#print axioms MarkedExcursion.normal_rank_inverse
#print axioms MarkedExcursion.normal_forward_error
#print axioms MarkedExcursion.normal_curvature_error
#print axioms MarkedExcursion.suffix_difference_inversion
#print axioms MarkedExcursion.free_suffix_of_spectral_moments
#print axioms MarkedExcursion.inner_gaussian_moments
#print axioms MarkedExcursion.outer_exponential_budget
#print axioms MarkedExcursion.right_suffix_envelope
#print axioms MarkedExcursion.right_free_suffix
#print axioms MarkedExcursion.right_prefix_differences
#print axioms MarkedExcursion.right_prefix_cut_lengths
#print axioms MarkedExcursion.lattice_difference_integral
#print axioms MarkedExcursion.prefix_difference_mixture
#print axioms MarkedExcursion.first_hit_rank_bin
#print axioms MarkedExcursion.short_outer_budgets
#print axioms MarkedExcursion.short_suffix_envelope
#print axioms MarkedExcursion.short_free_differences
#print axioms MarkedExcursion.first_hit_rank_bound
#print axioms MarkedExcursion.first_hit_rank_marked
#print axioms MarkedExcursion.homogeneous_live_upper
#print axioms MarkedExcursion.middle_displacement_bound
#print axioms MarkedExcursion.first_hit_three_blocks
#print axioms MarkedExcursion.pinned_hit_bin
#print axioms MarkedExcursion.pinned_rank_loss
#print axioms MarkedExcursion.late_event_probability
#print axioms MarkedExcursion.difference_hit_decomposition
#print axioms MarkedExcursion.tilted_retained_pair
#print axioms MarkedExcursion.paired_wall_powers
#print axioms MarkedExcursion.late_endpoint_bound
#print axioms MarkedExcursion.late_rank_arcs
#print axioms MarkedExcursion.late_rank_moments
#print axioms MarkedExcursion.late_rank_loss
#print axioms MarkedExcursion.late_uniform_budget
#print axioms MarkedExcursion.early_loss_bin_bound
#print axioms MarkedExcursion.integer_rank_signs
#print axioms MarkedExcursion.bin_suffix_scale
#print axioms MarkedExcursion.bin_prefix_survival
#print axioms MarkedExcursion.bin_prefix_variance
#print axioms MarkedExcursion.BinArithmetic.growth_bin_checks
#print axioms MarkedExcursion.BinArithmetic.curvature_bin_checks

open MarkedExcursion.BinArithmetic in
example {m j : ℕ} (hm : 4096 ≤ m) (hj : j+1 ≤ staircaseDegree m)
    (hl : (3/4)*sizeScale m ≤ (staircaseDegree m:ℝ)-(j+1))
    (hu : (staircaseDegree m:ℝ)-(j+1) ≤ 2*sizeScale m) :
    rankCount m (j+1)<rankCount m (j+2) := right_flank_growth hm hj hl hu

open MarkedExcursion.BinArithmetic in
example {m j : ℕ} (hm : 4096 ≤ m) (hj : j+1 ≤ staircaseDegree m)
    (hl : (15/16)*sizeScale m ≤ (staircaseDegree m:ℝ)-(j+1))
    (hu : (staircaseDegree m:ℝ)-(j+1) ≤ 2*sizeScale m) :
    rankCount m j*rankCount m (j+2)<rankCount m (j+1)^2 := right_flank_log_concave hm hj hl hu

#print axioms MarkedExcursion.BinArithmetic.right_flank_growth
#print axioms MarkedExcursion.BinArithmetic.right_flank_log_concave
#print axioms conjecture34_of_remaining_windows
#print axioms MarkedExcursion.upper_half_saddle
#print axioms MarkedExcursion.suffix_variance_ratio
#print axioms MarkedExcursion.upper_half_suffix_labels

open MarkedExcursion.BinArithmetic in
example {m j : ℕ} (hm : 4096 ≤ m) (hmid : staircaseDegree m ≤ 2*(j+1))
    (hj : j+1 ≤ staircaseDegree m)
    (hl : (3/4)*sizeScale m ≤ (staircaseDegree m:ℝ)-(j+1)) :
    rankCount m (j+1)<rankCount m (j+2) := upper_half_growth hm hmid hj hl

#print axioms MarkedExcursion.BinArithmetic.upper_half_growth
#print axioms conjecture34_of_peak_windows

example {n : ℕ} (hn : n ≤ 191) :
    UnimodalOn (rankCount (2*n)) 0 (n*n) ∧
    UnimodalOn (rankCount (2*n+1)) 0 (n*(n+1)) := central_through_191 hn

#print axioms central_through_191
#print axioms conjecture34_from_192
#print axioms MarkedExcursion.marked_late_rank_bound
#print axioms MarkedExcursion.scaled_prefix_survival
#print axioms MarkedExcursion.fair_ruin_identity

example {m j : ℕ} (hm : 4096≤m) (hmid : staircaseDegree m≤2*(j+1))
    (hj : j+1≤staircaseDegree m)
    (hl : (3/5)*MarkedExcursion.BinArithmetic.sizeScale m≤(staircaseDegree m:ℝ)-(j+1)) :
    rankCount m (j+1)<rankCount m (j+2) :=
  MarkedExcursion.BinArithmetic.Peak.upper_half_three_fifths hm hmid hj hl

#print axioms MarkedExcursion.BinArithmetic.Peak.upper_half_three_fifths
#print axioms conjecture34_from_three_fifths
#print axioms EndpointDeficit.rank_lt_of_separated
#print axioms EndpointDeficit.midpoint_192
#print axioms central_through_195
#print axioms conjecture34_from_196
#print axioms MarkedExcursion.firstReturn_absolute_area
#print axioms uniform_smooth_amplitude
#print axioms ReturnSplit.mixed_binomial_moment
#print axioms ReturnSplit.residual_anchor
#print axioms ReturnSplit.gaussian_residual_error
#print axioms Witness.pointCoefficients_exact
#print axioms Witness.low_frequency_four
#print axioms Interpolation.interpolation_error
#print axioms Witness.node_product_cost
#print axioms Witness.interpolation_twelve
#print axioms PolynomialTrial.trial_convolution
#print axioms PolynomialTrial.curve_lipschitz
#print axioms PolynomialTrial.amplitude_4096
#print axioms PolynomialTrial.integratedTaylor_exact
#print axioms PolynomialTrial.full_period_error
#print axioms ReturnSplit.sample_split_corrected
#print axioms returnMass_ratio
#print axioms inverseAt_local_error
#print axioms PolynomialTrial.moderate_inner_tail
#print axioms PolynomialTrial.outer_rank_tail_from_300000
