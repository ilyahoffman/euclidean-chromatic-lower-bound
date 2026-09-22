import HoffmanChromatic

/-! Kernel-checked theorem signatures, including the explicit endpoint quantifiers. -/

#check HoffmanChromatic.finite_six_real
#check HoffmanChromatic.finite_seven_real
#check HoffmanChromatic.finite_chromatic_inequality
#check HoffmanChromatic.coefficient_rank_transfer
#check HoffmanChromatic.coordinate_factorization
#check (HoffmanChromatic.rounded_chromatic : HoffmanChromatic.RoundedTarget)
#check (HoffmanChromatic.subsequence_chromatic : HoffmanChromatic.SubsequenceTarget)
#check (HoffmanChromatic.uniform_chromatic : HoffmanChromatic.UniformTarget)
#check HoffmanChromatic.rounded_euclidean_chromatic
#check HoffmanChromatic.subsequence_euclidean_chromatic

-- The exact constant-prefactor endpoint is now inhabited by uniform_chromatic.
#print HoffmanChromatic.UniformTarget

#check HoffmanChromatic.binomial_central_bounds
#check HoffmanChromatic.binomial_uniform_upper
#check HoffmanChromatic.uniform_coefficient_bounds
#check HoffmanChromatic.uniform_weighted_coefficient_bound
#check HoffmanChromatic.six_uniform_parameter_bound
#check HoffmanChromatic.seven_uniform_parameter_bound
#check HoffmanChromatic.six_uniform_rate
#check HoffmanChromatic.seven_uniform_rate
#check HoffmanChromatic.sharp_crossing
#check HoffmanChromatic.sharp_rate_cover

-- Direct statements use arbitrary colouring functions and the L2 metric.
#check HoffmanChromatic.Direct.direct_rounded
#check HoffmanChromatic.Direct.direct_subsequence
#check HoffmanChromatic.Direct.direct_uniform

-- The standalone optimal-index remark is proved in both binomial bases.
#check HoffmanChromatic.minimum_detector_index_iff
#check HoffmanChromatic.minimum_shifted_detector_index_iff
#print HoffmanChromatic.minimumDetectorIndex
