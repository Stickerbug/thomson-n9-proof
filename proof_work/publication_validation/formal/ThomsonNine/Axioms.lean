import ThomsonNine.CandidateMem
import ThomsonNine.FinalAssembly
import ThomsonNine.Derivative
import ThomsonNine.Stationary
import ThomsonNine.SecondDerivative
import ThomsonNine.StrictConvex
import ThomsonNine.EnergyContinuity
import ThomsonNine.DomainCoverage
import ThomsonNine.LeafSemantics
import ThomsonNine.Applications
import ThomsonNine.ContactInner
import ThomsonNine.EnergyBounds
import ThomsonNine.DistanceValues
import ThomsonNine.GramBound
import ThomsonNine.DomainChamber
import ThomsonNine.EnergyValue
import ThomsonNine.EnergyForms
import ThomsonNine.EnergyGradient
import ThomsonNine.EnergyPath
import ThomsonNine.GradientZero
import ThomsonNine.EnergyOptimality
import ThomsonNine.EnergySymmetry
import ThomsonNine.Minimizer
import ThomsonNine.ThreePoint
import ThomsonNine.ThreePointBound
import ThomsonNine.TreeSemantics
import ThomsonNine.PSDSemantics
import ThomsonNine.IntervalTensor
import ThomsonNine.IntervalMul
import ThomsonNine.IntervalEval
import ThomsonNine.IntervalSum
import ThomsonNine.IntervalTensorEval
import ThomsonNine.LeafCert
import ThomsonNine.PairDeriv
import ThomsonNine.LocalLDLData
import ThomsonNine.LocalLDLFactorization
import ThomsonNine.LocalNonneg
import ThomsonNine.IntervalLocalOps
import ThomsonNine.LocalLDLReplay
import ThomsonNine.GramBoundary
import ThomsonNine.IntervalLinear
import ThomsonNine.LocalHessianBridge
import ThomsonNine.IntervalSparsePolynomial
import ThomsonNine.IntervalPowerReplay
import ThomsonNine.IntervalSparseDerivative
import ThomsonNine.LocalSparseHessianAAA
import ThomsonNine.TargetBinding
import ThomsonNine.GatheredBinding
import ThomsonNine.MultiCornerBindings
import ThomsonNine.MultiCornerPowBindings
import ThomsonNine.MultiCornerPBindings
import ThomsonNine.GroupedT114
import ThomsonNine.Grouped739
import ThomsonNine.Grouped103
import ThomsonNine.Grouped517
import ThomsonNine.Grouped629
import ThomsonNine.Grouped615
import ThomsonNine.Grouped574
import ThomsonNine.Grouped547
import ThomsonNine.Grouped531
import ThomsonNine.Grouped469
import ThomsonNine.Grouped463
import ThomsonNine.Grouped328
import ThomsonNine.Grouped312
import ThomsonNine.Grouped242
import ThomsonNine.Grouped224
import ThomsonNine.Grouped123
import ThomsonNine.Grouped647
import ThomsonNine.Grouped612
import ThomsonNine.Grouped590
import ThomsonNine.Grouped583
import ThomsonNine.Grouped403
import ThomsonNine.Grouped396
import ThomsonNine.Grouped329
import ThomsonNine.Grouped321
import ThomsonNine.Grouped124
import ThomsonNine.GatheredTwoSource
import ThomsonNine.GatheredChain
import ThomsonNine.SingleSourceBindings
import ThomsonNine.FiveSourceBindings
import ThomsonNine.ChainRestBindings
import ThomsonNine.SevenSourceBindings
import ThomsonNine.EightSourceBindings
import ThomsonNine.NineSourceBindings
import ThomsonNine.ElevenSourceBindings
import ThomsonNine.SeventeenSourceBindings
import ThomsonNine.SixteenSourceBindings
import ThomsonNine.FifteenSourceBindings
import ThomsonNine.FourteenSourceBindings
import ThomsonNine.ThirteenSourceBindings
import ThomsonNine.TwelveSourceBindings
import ThomsonNine.TenSourceBindings
import ThomsonNine.TwoSourceBindings
import ThomsonNine.ChainBindings
import ThomsonNine.SparseTranslation

/-! Print the axiom footprints of the formalized building blocks. -/

#print axioms ThomsonNine.Family.candidate_eq_p
#print axioms ThomsonNine.Family.energy_p
#print axioms ThomsonNine.Family.energy_candidate
#print axioms ThomsonNine.Family.candidate_mem_sphere
#print axioms ThomsonNine.Coverage.coverage_sound_on_domain
#print axioms ThomsonNine.Semantics.energy_lower_of_balance
#print axioms ThomsonNine.Family.hasDerivAt_familyEnergy
#print axioms ThomsonNine.Family.familyEnergyDeriv_half_neg
#print axioms ThomsonNine.Family.familyEnergyDeriv_nine_tenths_pos
#print axioms ThomsonNine.Family.continuousOn_familyEnergyDeriv
#print axioms ThomsonNine.Family.exists_familyEnergyDeriv_zero
#print axioms ThomsonNine.Family.exists_stationary_point
#print axioms ThomsonNine.Family.hasDerivAt_familyEnergyDeriv
#print axioms ThomsonNine.Family.familyEnergyDeriv2_pos
#print axioms ThomsonNine.Family.continuousOn_familyEnergyDeriv_Ioo
#print axioms ThomsonNine.Family.stationary_point_unique
#print axioms ThomsonNine.Family.stationary_point_unique'
#print axioms ThomsonNine.Family.exists_unique_stationary_point
#print axioms ThomsonNine.Family.strictMonoOn_familyEnergyDeriv
#print axioms ThomsonNine.Family.familyEnergy_strictAntiOn
#print axioms ThomsonNine.Family.familyEnergy_strictMonoOn
#print axioms ThomsonNine.Family.familyEnergy_min
#print axioms ThomsonNine.Family.exists_unique_familyEnergy_min
#print axioms ThomsonNine.Family.familyEnergy_strictAntiOn_Ioo
#print axioms ThomsonNine.Family.familyEnergy_strictMonoOn_Ioo
#print axioms ThomsonNine.Family.strictConvexOn_familyEnergy
#print axioms ThomsonNine.continuousAt_energy_of_injective
#print axioms ThomsonNine.continuousOn_energy_injective
#print axioms ThomsonNine.Family.energy_candidate_min
#print axioms ThomsonNine.Family.exists_candidate_with_family_min

#print axioms ThomsonNine.energy_comp_isometry
#print axioms ThomsonNine.sphereConfig_comp_isometry
#print axioms ThomsonNine.energy_ge_eighteen
#print axioms ThomsonNine.norm_sub_sq_eq_inner
#print axioms ThomsonNine.norm_sub_eq_sqrt_inner
#print axioms ThomsonNine.energy_eq_inner
#print axioms ThomsonNine.hasDerivAt_energy_candidate
#print axioms ThomsonNine.sphereConfig_nonempty

#print axioms ThomsonNine.inner_p_T_T
#print axioms ThomsonNine.inner_p_T_B_same
#print axioms ThomsonNine.inner_p_T_B_diff
#print axioms ThomsonNine.inner_p_E_E
#print axioms ThomsonNine.inner_p_ring_E_adj
#print axioms ThomsonNine.inner_p_ring_E_opp

#print axioms ThomsonNine.dist_le_two
#print axioms ThomsonNine.inv_dist_le_energy_of_lt
#print axioms ThomsonNine.inv_dist_le_energy
#print axioms ThomsonNine.dist_ge_inv_energy
#print axioms ThomsonNine.energy_candidate_strict_min
#print axioms ThomsonNine.exists_candidate_strict_energy_min

#print axioms ThomsonNine.dist_p_T_T
#print axioms ThomsonNine.dist_p_T_B_same
#print axioms ThomsonNine.dist_p_T_B_diff
#print axioms ThomsonNine.dist_p_E_E
#print axioms ThomsonNine.dist_p_T_E_near
#print axioms ThomsonNine.dist_p_T_E_far
#print axioms ThomsonNine.dist_p_T_E_far_B
#print axioms ThomsonNine.dist_candidate_eq_sqrt_inner
#print axioms ThomsonNine.dist_sq_candidate_eq_inner

#print axioms ThomsonNine.gram_inner_nonneg
#print axioms ThomsonNine.inner_mem_Icc_of_unit
#print axioms ThomsonNine.inner_mem_Icc_of_mem
#print axioms ThomsonNine.gram_constraint_of_mem
#print axioms ThomsonNine.Family.familyEnergy_seven_tenths_lt_26
#print axioms ThomsonNine.Family.familyEnergy_stationary_lt_26
#print axioms ThomsonNine.Family.exists_candidate_energy_lt_26

#print axioms ThomsonNine.energy_smul
#print axioms ThomsonNine.hasDerivAt_energy_scale
#print axioms ThomsonNine.energy_eq_sum_rpow

#print axioms ThomsonNine.hasDerivAt_affine
#print axioms ThomsonNine.hasDerivAt_norm_sq_affine
#print axioms ThomsonNine.hasDerivAt_norm_affine
#print axioms ThomsonNine.hasDerivAt_inv_norm_affine

#print axioms ThomsonNine.hasDerivAt_pair_inv_dist
#print axioms ThomsonNine.inner_gradAt
#print axioms ThomsonNine.energy_translate
#print axioms ThomsonNine.hasDerivAt_energy_update

#print axioms ThomsonNine.sum_Ioi_ite_eq
#print axioms ThomsonNine.pairSum_eq_inner_gradAt
#print axioms ThomsonNine.hasDerivAt_energy_update_gradAt

#print axioms ThomsonNine.hasDerivAt_pair_inv_dist_path
#print axioms ThomsonNine.sum_Iio_swap
#print axioms ThomsonNine.sum_univ_ite_eq_sum_erase
#print axioms ThomsonNine.sum_erase_eq_sum_Iio_add_Ioi
#print axioms ThomsonNine.hasDerivAt_energy_path

#print axioms ThomsonNine.gradient_zero_iff_directional
#print axioms ThomsonNine.hasDerivAt_energy_path_zero

#print axioms ThomsonNine.stationary_iff_gradient_zero

#print axioms ThomsonNine.inner_le_of_energy_le
#print axioms ThomsonNine.local_min_gradient_zero
#print axioms ThomsonNine.isLocalMin_gradient_zero

#print axioms ThomsonNine.two_mul_energy
#print axioms ThomsonNine.energy_perm
#print axioms ThomsonNine.sphereConfig_perm

#print axioms ThomsonNine.exists_global_minimizer
#print axioms ThomsonNine.exists_global_minimizer_lt_26
#print axioms ThomsonNine.isCompact_feasibleShell

#print axioms ThomsonNine.ThreePoint.quad_Y3_nonneg
#print axioms ThomsonNine.ThreePoint.sum_S3_eq_sum_Y3
#print axioms ThomsonNine.ThreePoint.bv_positivity
#print axioms ThomsonNine.ThreePoint.exists_tangent_frame
#print axioms ThomsonNine.ThreePoint.Q3_eq_re
#print axioms ThomsonNine.ThreePoint.sum_all_eq
#print axioms ThomsonNine.ThreePoint.dsum_pair12
#print axioms ThomsonNine.ThreePoint.dsum_const
#print axioms ThomsonNine.ThreePoint.dsum_Rs
#print axioms ThomsonNine.ThreePoint.dsum_H
#print axioms ThomsonNine.ThreePoint.gramOK_inner
#print axioms ThomsonNine.ThreePoint.matDot_Rk
#print axioms ThomsonNine.ThreePoint.sum_matDot_Rk
#print axioms ThomsonNine.ThreePoint.sum4_swap
#print axioms ThomsonNine.ThreePoint.three_point_identity
#print axioms ThomsonNine.ThreePoint.matDot_moment_nonneg_sos
#print axioms ThomsonNine.ThreePoint.three_point_bound_sos

#print axioms ThomsonNine.thomsonNineClaim_iff_global_lower_bound
#print axioms ThomsonNine.thomsonNineClaim_of_pointwise

#print axioms ThomsonNine.exists_ordered_domain_triple
#print axioms ThomsonNine.exists_ordered_gram_constraint_of_mem
#print axioms ThomsonNine.gram_swap13
#print axioms ThomsonNine.TreeSemantics.terminal_sound
#print axioms ThomsonNine.TreeSemantics.bisect_sound
#print axioms ThomsonNine.TreeSemantics.covered_sound
#print axioms ThomsonNine.TreeSemantics.physicalOrdered_mem_rootBox
#print axioms ThomsonNine.TreeSemantics.covered_sound_root
#print axioms ThomsonNine.PSDSemantics.dotProduct_mulVec_nonneg_real
#print axioms ThomsonNine.PSDSemantics.reduced_quadform_nonneg
#print axioms ThomsonNine.PSDSemantics.sum_quadform_nonneg
#print axioms ThomsonNine.PSDSemantics.reduced_sum_quadform_nonneg

#print axioms ThomsonNine.Interval.RatInterval.mem_add
#print axioms ThomsonNine.Interval.RatInterval.mem_mulNonneg
#print axioms ThomsonNine.Interval.RatInterval.mem_powNonneg
#print axioms ThomsonNine.Interval.RatInterval.nonneg_of_lo
#print axioms ThomsonNine.Interval.tensor_nonneg_of_coeff_intervals

#print axioms ThomsonNine.Interval.RatInterval.mulMixed
#print axioms ThomsonNine.Interval.RatInterval.mem_mulMixed

#print axioms ThomsonNine.Interval.RatInterval.oneMinus_lo_nonneg
#print axioms ThomsonNine.Interval.RatInterval.bernInterval
#print axioms ThomsonNine.Interval.RatInterval.mem_bernInterval

#print axioms ThomsonNine.Interval.RatInterval.bernInterval_lo_nonneg
#print axioms ThomsonNine.Interval.RatInterval.mem_mulMixed3

#print axioms ThomsonNine.Interval.RatInterval.mem_sumIntervals

#print axioms ThomsonNine.Interval.RatInterval.mem_sum
#print axioms ThomsonNine.Interval.RatInterval.evalTensor_sound

#print axioms ThomsonNine.Interval.RatInterval.LocalCert.sound

-- Local certificate implications and the exact generated endpoint data.
#print axioms ThomsonNine.LocalLDL.quadratic_nonneg
#print axioms ThomsonNine.LocalLDL.quadratic_eq_of_entries
#print axioms ThomsonNine.LocalLDL.positive_of_mem
#print axioms ThomsonNine.LocalLDL.LDL3Cert.sound
#print axioms ThomsonNine.LocalLDL.congruence_nonneg
#print axioms ThomsonNine.LocalLDL.hessian_quadratic_nonneg
#print axioms ThomsonNine.LocalLDL.LDL2Cert.sound
#print axioms ThomsonNine.LocalLDL.quadratic2_eq_of_entries
#print axioms ThomsonNine.LocalLDL.congruence2_nonneg
#print axioms ThomsonNine.LocalLDL.boundary_residual_nonneg
#print axioms ThomsonNine.LocalLDL.quadratic_eq_recurrence
#print axioms ThomsonNine.LocalLDL.LDL3Cert.entries_nonneg
#print axioms ThomsonNine.LocalLDL.symmetricQuadratic_congruence
#print axioms ThomsonNine.LocalLDL.LDL3Cert.preconditioned_entries_nonneg
#print axioms ThomsonNine.LocalLDL.LDL2Cert.entries_nonneg
#print axioms ThomsonNine.LocalLDL.LDL2Cert.preconditioned_entries_nonneg
#print axioms ThomsonNine.LocalLDL.segment_nonneg_of_convex
#print axioms ThomsonNine.LocalLDL.segment_nonneg_of_second_derivative
#print axioms ThomsonNine.LocalLDL.segment_nonneg_of_ldl3
#print axioms ThomsonNine.LocalLDL.segment_nonneg_of_ldl2
#print axioms ThomsonNine.LocalLDL.nonneg_above_boundary
#print axioms ThomsonNine.LocalLDL.Data.cert_00_AAA
#print axioms ThomsonNine.LocalLDL.Data.center_contained_00_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_00_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_00_2
#print axioms ThomsonNine.LocalLDL.Data.cert_01_CBA
#print axioms ThomsonNine.LocalLDL.Data.center_contained_01_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_01_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_01_2
#print axioms ThomsonNine.LocalLDL.Data.cert_02_CCA
#print axioms ThomsonNine.LocalLDL.Data.center_contained_02_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_02_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_02_2
#print axioms ThomsonNine.LocalLDL.Data.cert_03_AFF
#print axioms ThomsonNine.LocalLDL.Data.center_contained_03_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_03_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_03_2
#print axioms ThomsonNine.LocalLDL.Data.cert_04_GAF
#print axioms ThomsonNine.LocalLDL.Data.center_contained_04_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_04_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_04_2
#print axioms ThomsonNine.LocalLDL.Data.cert_05_BFF
#print axioms ThomsonNine.LocalLDL.Data.center_contained_05_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_05_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_05_2
#print axioms ThomsonNine.LocalLDL.Data.cert_06_GGB
#print axioms ThomsonNine.LocalLDL.Data.center_contained_06_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_06_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_06_2
#print axioms ThomsonNine.LocalLDL.Data.boundary_Ru_pos_06
#print axioms ThomsonNine.LocalLDL.Data.cert_07_CFF
#print axioms ThomsonNine.LocalLDL.Data.center_contained_07_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_07_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_07_2
#print axioms ThomsonNine.LocalLDL.Data.boundary_Ru_pos_07
#print axioms ThomsonNine.LocalLDL.Data.cert_08_CGF
#print axioms ThomsonNine.LocalLDL.Data.center_contained_08_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_08_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_08_2
#print axioms ThomsonNine.LocalLDL.Data.cert_09_DDD
#print axioms ThomsonNine.LocalLDL.Data.center_contained_09_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_09_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_09_2
#print axioms ThomsonNine.LocalLDL.Data.boundary_Ru_pos_09
#print axioms ThomsonNine.LocalLDL.Data.cert_10_DFF
#print axioms ThomsonNine.LocalLDL.Data.center_contained_10_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_10_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_10_2
#print axioms ThomsonNine.LocalLDL.Data.cert_11_GDF
#print axioms ThomsonNine.LocalLDL.Data.center_contained_11_0
#print axioms ThomsonNine.LocalLDL.Data.center_contained_11_1
#print axioms ThomsonNine.LocalLDL.Data.center_contained_11_2
#print axioms ThomsonNine.Interval.RatInterval.mem_subset
#print axioms ThomsonNine.Interval.RatInterval.mem_mul_of_bounds
#print axioms ThomsonNine.Interval.RatInterval.mem_mul
#print axioms ThomsonNine.Interval.RatInterval.mem_square_of_bounds
#print axioms ThomsonNine.Interval.RatInterval.mem_square
#print axioms ThomsonNine.Interval.RatInterval.mem_reciprocalPos
#print axioms ThomsonNine.Interval.RatInterval.mem_divPos
#print axioms ThomsonNine.Interval.RatInterval.mem_div_pos_of_bounds
#print axioms ThomsonNine.LocalLDL.Replay.psd_00_AAA
#print axioms ThomsonNine.LocalLDL.Replay.psd_01_CBA
#print axioms ThomsonNine.LocalLDL.Replay.psd_02_CCA
#print axioms ThomsonNine.LocalLDL.Replay.psd_03_AFF
#print axioms ThomsonNine.LocalLDL.Replay.psd_04_GAF
#print axioms ThomsonNine.LocalLDL.Replay.psd_05_BFF
#print axioms ThomsonNine.LocalLDL.Replay.psd_06_GGB
#print axioms ThomsonNine.LocalLDL.Replay.psd_07_CFF
#print axioms ThomsonNine.LocalLDL.Replay.psd_08_CGF
#print axioms ThomsonNine.LocalLDL.Replay.psd_09_DDD
#print axioms ThomsonNine.LocalLDL.Replay.psd_10_DFF
#print axioms ThomsonNine.LocalLDL.Replay.psd_11_GDF
#print axioms ThomsonNine.LocalLDL.gram_eq_radicand_sub_sq
#print axioms ThomsonNine.LocalLDL.radicand_nonneg
#print axioms ThomsonNine.LocalLDL.gram_lowerGraph_zero
#print axioms ThomsonNine.LocalLDL.feasible_between_graphs
#print axioms ThomsonNine.LocalLDL.residual_nonneg_of_graph

-- Original Hessian, signed sparse evaluation, and analytic coordinate derivatives.
#print axioms ThomsonNine.Interval.RatInterval.mem_signedScale
#print axioms ThomsonNine.Interval.RatInterval.mem_linear6
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_00_AAA
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_01_CBA
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_02_CCA
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_03_AFF
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_04_GAF
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_05_BFF
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_06_GGB
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_07_CFF
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_08_CGF
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_09_DDD
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_10_DFF
#print axioms ThomsonNine.LocalLDL.HessianBridge.psd_original_11_GDF
#print axioms ThomsonNine.Interval.SparsePolynomial.mem_powSigned
#print axioms ThomsonNine.Interval.SparsePolynomial.eval_mem
#print axioms ThomsonNine.Interval.SparsePolynomial.formalDerivative_mem
#print axioms ThomsonNine.Interval.SparsePolynomial.formalHessianEntry_mem
#print axioms ThomsonNine.Interval.SparsePolynomial.formalHessianEntry_mem_of_bounds
#print axioms ThomsonNine.Interval.SparsePolynomial.mem_powerCache
#print axioms ThomsonNine.Interval.SparsePolynomial.hasDerivAt_monomial_axis
#print axioms ThomsonNine.Interval.SparsePolynomial.hasDerivAt_eval_axis
#print axioms ThomsonNine.Interval.SparsePolynomial.hasDerivAt_formalDerivative_axis
#print axioms ThomsonNine.Interval.SparsePolynomial.hasDerivAt_axisDeriv_eval
#print axioms ThomsonNine.Interval.SparsePolynomial.axisDeriv_axisDeriv_eval
#print axioms ThomsonNine.Interval.SparsePolynomial.axisDeriv_axisDeriv_eval_mem_of_bounds

#print axioms ThomsonNine.LocalSparseHessianAAA.actual_h00_mem

#print axioms ThomsonNine.Interval.SparsePolynomial.shifted_pow
#print axioms ThomsonNine.Interval.SparsePolynomial.monomial_shift
#print axioms ThomsonNine.Interval.SparsePolynomial.term_shift
#print axioms ThomsonNine.Interval.SparsePolynomial.eval_shift
#print axioms ThomsonNine.Interval.SparsePolynomial.expandedCoefficient_mem
#print axioms ThomsonNine.Interval.SparsePolynomial.axisShiftCoeff_mem
#print axioms ThomsonNine.Interval.SparsePolynomial.powInterval_mem
#print axioms ThomsonNine.Interval.SparsePolynomial.shiftAxis_mem
#print axioms ThomsonNine.Interval.SparsePolynomial.shiftAxes_mem
#print axioms ThomsonNine.Interval.SparsePolynomial.shiftAxes_mem_of_contains
#print axioms ThomsonNine.TargetBinding.target_t126_interval_bound

#print axioms ThomsonNine.TwoSourceBinding.target_t026_0_0_26_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t136_0_10_9_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t153_0_26_0_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t245_1_8_9_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t254_1_9_8_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t331_2_7_8_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t339_2_8_7_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t405_3_6_7_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t412_3_7_6_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t471_4_5_6_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t477_4_6_5_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t533_5_4_6_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t544_5_6_4_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t592_6_3_7_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t598_6_4_5_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t604_6_5_4_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t613_6_7_3_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t649_7_2_8_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t656_7_3_6_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t669_7_6_3_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t676_7_8_2_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t700_8_1_9_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t708_8_2_7_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t724_8_7_2_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t729_8_9_1_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t741_9_0_10_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t750_9_1_8_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t765_9_8_1_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t768_9_10_0_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t778_10_0_9_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t788_10_9_0_interval_bound
#print axioms ThomsonNine.TwoSourceBinding.target_t805_26_0_0_interval_bound

#print axioms ThomsonNine.ChainBinding.target_t024_0_0_24_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t025_0_0_25_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t104_0_7_10_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t115_0_8_10_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t134_0_10_7_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t135_0_10_8_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t151_0_24_0_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t152_0_25_0_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t225_1_6_9_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t235_1_7_9_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t252_1_9_6_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t253_1_9_7_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t313_2_5_8_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t322_2_6_8_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t337_2_8_5_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t338_2_8_6_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t389_3_4_7_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t397_3_5_7_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t410_3_7_4_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t411_3_7_5_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t457_4_3_7_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t482_4_7_3_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t518_5_2_8_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t526_5_3_7_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t548_5_7_3_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t551_5_8_2_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t575_6_1_9_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t584_6_2_8_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t616_6_8_2_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t618_6_9_1_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t630_7_0_10_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t640_7_1_9_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t654_7_3_4_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t655_7_3_5_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t661_7_4_3_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t665_7_5_3_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t678_7_9_1_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t679_7_10_0_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t690_8_0_10_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t706_8_2_5_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t707_8_2_6_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t718_8_5_2_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t721_8_6_2_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t730_8_10_0_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t748_9_1_6_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t749_9_1_7_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t761_9_6_1_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t763_9_7_1_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t776_10_0_7_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t777_10_0_8_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t786_10_7_0_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t787_10_8_0_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t803_24_0_0_interval_bound
#print axioms ThomsonNine.ChainBinding.target_t804_25_0_0_interval_bound

#print axioms ThomsonNine.GatheredBinding.t126_gathered_mem

#print axioms ThomsonNine.GatheredTwoSource.t026_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t136_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t153_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t245_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t254_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t331_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t339_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t405_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t412_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t471_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t477_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t533_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t544_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t592_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t598_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t604_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t613_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t649_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t656_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t669_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t676_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t700_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t708_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t724_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t729_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t741_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t750_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t765_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t768_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t778_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t788_gathered_mem
#print axioms ThomsonNine.GatheredTwoSource.t805_gathered_mem

#print axioms ThomsonNine.GatheredChain.t024_gathered_mem
#print axioms ThomsonNine.GatheredChain.t025_gathered_mem
#print axioms ThomsonNine.GatheredChain.t104_gathered_mem
#print axioms ThomsonNine.GatheredChain.t115_gathered_mem
#print axioms ThomsonNine.GatheredChain.t134_gathered_mem
#print axioms ThomsonNine.GatheredChain.t135_gathered_mem
#print axioms ThomsonNine.GatheredChain.t151_gathered_mem
#print axioms ThomsonNine.GatheredChain.t152_gathered_mem
#print axioms ThomsonNine.GatheredChain.t225_gathered_mem
#print axioms ThomsonNine.GatheredChain.t235_gathered_mem
#print axioms ThomsonNine.GatheredChain.t252_gathered_mem
#print axioms ThomsonNine.GatheredChain.t253_gathered_mem
#print axioms ThomsonNine.GatheredChain.t313_gathered_mem
#print axioms ThomsonNine.GatheredChain.t322_gathered_mem
#print axioms ThomsonNine.GatheredChain.t337_gathered_mem
#print axioms ThomsonNine.GatheredChain.t338_gathered_mem
#print axioms ThomsonNine.GatheredChain.t389_gathered_mem
#print axioms ThomsonNine.GatheredChain.t397_gathered_mem
#print axioms ThomsonNine.GatheredChain.t410_gathered_mem
#print axioms ThomsonNine.GatheredChain.t411_gathered_mem
#print axioms ThomsonNine.GatheredChain.t457_gathered_mem
#print axioms ThomsonNine.GatheredChain.t482_gathered_mem
#print axioms ThomsonNine.GatheredChain.t518_gathered_mem
#print axioms ThomsonNine.GatheredChain.t526_gathered_mem
#print axioms ThomsonNine.GatheredChain.t548_gathered_mem
#print axioms ThomsonNine.GatheredChain.t551_gathered_mem
#print axioms ThomsonNine.GatheredChain.t575_gathered_mem
#print axioms ThomsonNine.GatheredChain.t584_gathered_mem
#print axioms ThomsonNine.GatheredChain.t616_gathered_mem
#print axioms ThomsonNine.GatheredChain.t618_gathered_mem
#print axioms ThomsonNine.GatheredChain.t630_gathered_mem
#print axioms ThomsonNine.GatheredChain.t640_gathered_mem
#print axioms ThomsonNine.GatheredChain.t654_gathered_mem
#print axioms ThomsonNine.GatheredChain.t655_gathered_mem
#print axioms ThomsonNine.GatheredChain.t661_gathered_mem
#print axioms ThomsonNine.GatheredChain.t665_gathered_mem
#print axioms ThomsonNine.GatheredChain.t678_gathered_mem
#print axioms ThomsonNine.GatheredChain.t679_gathered_mem
#print axioms ThomsonNine.GatheredChain.t690_gathered_mem
#print axioms ThomsonNine.GatheredChain.t706_gathered_mem
#print axioms ThomsonNine.GatheredChain.t707_gathered_mem
#print axioms ThomsonNine.GatheredChain.t718_gathered_mem
#print axioms ThomsonNine.GatheredChain.t721_gathered_mem
#print axioms ThomsonNine.GatheredChain.t730_gathered_mem
#print axioms ThomsonNine.GatheredChain.t748_gathered_mem
#print axioms ThomsonNine.GatheredChain.t749_gathered_mem
#print axioms ThomsonNine.GatheredChain.t761_gathered_mem
#print axioms ThomsonNine.GatheredChain.t763_gathered_mem
#print axioms ThomsonNine.GatheredChain.t776_gathered_mem
#print axioms ThomsonNine.GatheredChain.t777_gathered_mem
#print axioms ThomsonNine.GatheredChain.t786_gathered_mem
#print axioms ThomsonNine.GatheredChain.t787_gathered_mem
#print axioms ThomsonNine.GatheredChain.t803_gathered_mem
#print axioms ThomsonNine.GatheredChain.t804_gathered_mem

#print axioms ThomsonNine.SingleSource.t027_gathered_mem
#print axioms ThomsonNine.SingleSource.t137_gathered_mem
#print axioms ThomsonNine.SingleSource.t154_gathered_mem
#print axioms ThomsonNine.SingleSource.t255_gathered_mem
#print axioms ThomsonNine.SingleSource.t340_gathered_mem
#print axioms ThomsonNine.SingleSource.t413_gathered_mem
#print axioms ThomsonNine.SingleSource.t478_gathered_mem
#print axioms ThomsonNine.SingleSource.t539_gathered_mem
#print axioms ThomsonNine.SingleSource.t599_gathered_mem
#print axioms ThomsonNine.SingleSource.t609_gathered_mem
#print axioms ThomsonNine.SingleSource.t657_gathered_mem
#print axioms ThomsonNine.SingleSource.t673_gathered_mem
#print axioms ThomsonNine.SingleSource.t709_gathered_mem
#print axioms ThomsonNine.SingleSource.t727_gathered_mem
#print axioms ThomsonNine.SingleSource.t751_gathered_mem
#print axioms ThomsonNine.SingleSource.t767_gathered_mem
#print axioms ThomsonNine.SingleSource.t779_gathered_mem
#print axioms ThomsonNine.SingleSource.t789_gathered_mem
#print axioms ThomsonNine.SingleSource.t806_gathered_mem

#print axioms ThomsonNine.FiveSource.t023_gathered_mem
#print axioms ThomsonNine.FiveSource.t093_gathered_mem
#print axioms ThomsonNine.FiveSource.t133_gathered_mem
#print axioms ThomsonNine.FiveSource.t150_gathered_mem
#print axioms ThomsonNine.FiveSource.t215_gathered_mem
#print axioms ThomsonNine.FiveSource.t251_gathered_mem
#print axioms ThomsonNine.FiveSource.t304_gathered_mem
#print axioms ThomsonNine.FiveSource.t336_gathered_mem
#print axioms ThomsonNine.FiveSource.t449_gathered_mem
#print axioms ThomsonNine.FiveSource.t485_gathered_mem
#print axioms ThomsonNine.FiveSource.t509_gathered_mem
#print axioms ThomsonNine.FiveSource.t553_gathered_mem
#print axioms ThomsonNine.FiveSource.t565_gathered_mem
#print axioms ThomsonNine.FiveSource.t619_gathered_mem
#print axioms ThomsonNine.FiveSource.t705_gathered_mem
#print axioms ThomsonNine.FiveSource.t715_gathered_mem
#print axioms ThomsonNine.FiveSource.t747_gathered_mem
#print axioms ThomsonNine.FiveSource.t759_gathered_mem
#print axioms ThomsonNine.FiveSource.t775_gathered_mem
#print axioms ThomsonNine.FiveSource.t785_gathered_mem
#print axioms ThomsonNine.FiveSource.t802_gathered_mem

#print axioms ThomsonNine.ChainRest.t022_gathered_mem
#print axioms ThomsonNine.ChainRest.t082_gathered_mem
#print axioms ThomsonNine.ChainRest.t132_gathered_mem
#print axioms ThomsonNine.ChainRest.t149_gathered_mem
#print axioms ThomsonNine.ChainRest.t205_gathered_mem
#print axioms ThomsonNine.ChainRest.t250_gathered_mem
#print axioms ThomsonNine.ChainRest.t295_gathered_mem
#print axioms ThomsonNine.ChainRest.t335_gathered_mem
#print axioms ThomsonNine.ChainRest.t373_gathered_mem
#print axioms ThomsonNine.ChainRest.t416_gathered_mem
#print axioms ThomsonNine.ChainRest.t440_gathered_mem
#print axioms ThomsonNine.ChainRest.t487_gathered_mem
#print axioms ThomsonNine.ChainRest.t499_gathered_mem
#print axioms ThomsonNine.ChainRest.t554_gathered_mem
#print axioms ThomsonNine.ChainRest.t704_gathered_mem
#print axioms ThomsonNine.ChainRest.t712_gathered_mem
#print axioms ThomsonNine.ChainRest.t746_gathered_mem
#print axioms ThomsonNine.ChainRest.t757_gathered_mem
#print axioms ThomsonNine.ChainRest.t774_gathered_mem
#print axioms ThomsonNine.ChainRest.t784_gathered_mem
#print axioms ThomsonNine.ChainRest.t801_gathered_mem

#print axioms ThomsonNine.SevenSource.t021_gathered_mem
#print axioms ThomsonNine.SevenSource.t071_gathered_mem
#print axioms ThomsonNine.SevenSource.t131_gathered_mem
#print axioms ThomsonNine.SevenSource.t148_gathered_mem
#print axioms ThomsonNine.SevenSource.t195_gathered_mem
#print axioms ThomsonNine.SevenSource.t249_gathered_mem
#print axioms ThomsonNine.SevenSource.t364_gathered_mem
#print axioms ThomsonNine.SevenSource.t418_gathered_mem
#print axioms ThomsonNine.SevenSource.t430_gathered_mem
#print axioms ThomsonNine.SevenSource.t488_gathered_mem
#print axioms ThomsonNine.SevenSource.t745_gathered_mem
#print axioms ThomsonNine.SevenSource.t755_gathered_mem
#print axioms ThomsonNine.SevenSource.t773_gathered_mem
#print axioms ThomsonNine.SevenSource.t783_gathered_mem
#print axioms ThomsonNine.SevenSource.t800_gathered_mem

#print axioms ThomsonNine.EightSource.t020_gathered_mem
#print axioms ThomsonNine.EightSource.t060_gathered_mem
#print axioms ThomsonNine.EightSource.t130_gathered_mem
#print axioms ThomsonNine.EightSource.t147_gathered_mem
#print axioms ThomsonNine.EightSource.t185_gathered_mem
#print axioms ThomsonNine.EightSource.t248_gathered_mem
#print axioms ThomsonNine.EightSource.t277_gathered_mem
#print axioms ThomsonNine.EightSource.t342_gathered_mem
#print axioms ThomsonNine.EightSource.t354_gathered_mem
#print axioms ThomsonNine.EightSource.t419_gathered_mem
#print axioms ThomsonNine.EightSource.t744_gathered_mem
#print axioms ThomsonNine.EightSource.t753_gathered_mem
#print axioms ThomsonNine.EightSource.t772_gathered_mem
#print axioms ThomsonNine.EightSource.t782_gathered_mem
#print axioms ThomsonNine.EightSource.t799_gathered_mem

#print axioms ThomsonNine.NineSource.t019_gathered_mem
#print axioms ThomsonNine.NineSource.t049_gathered_mem
#print axioms ThomsonNine.NineSource.t129_gathered_mem
#print axioms ThomsonNine.NineSource.t146_gathered_mem
#print axioms ThomsonNine.NineSource.t267_gathered_mem
#print axioms ThomsonNine.NineSource.t343_gathered_mem
#print axioms ThomsonNine.NineSource.t771_gathered_mem
#print axioms ThomsonNine.NineSource.t781_gathered_mem
#print axioms ThomsonNine.NineSource.t798_gathered_mem

#print axioms ThomsonNine.TenSource.t018_gathered_mem
#print axioms ThomsonNine.TenSource.t038_gathered_mem
#print axioms ThomsonNine.TenSource.t128_gathered_mem
#print axioms ThomsonNine.TenSource.t145_gathered_mem
#print axioms ThomsonNine.TenSource.t165_gathered_mem
#print axioms ThomsonNine.TenSource.t256_gathered_mem
#print axioms ThomsonNine.TenSource.t770_gathered_mem
#print axioms ThomsonNine.TenSource.t780_gathered_mem
#print axioms ThomsonNine.TenSource.t797_gathered_mem

#print axioms ThomsonNine.ElevenSource.t017_gathered_mem
#print axioms ThomsonNine.ElevenSource.t144_gathered_mem
#print axioms ThomsonNine.ElevenSource.t796_gathered_mem

#print axioms ThomsonNine.TwelveSource.t016_gathered_mem
#print axioms ThomsonNine.TwelveSource.t143_gathered_mem
#print axioms ThomsonNine.TwelveSource.t795_gathered_mem

#print axioms ThomsonNine.ThirteenSource.t015_gathered_mem
#print axioms ThomsonNine.ThirteenSource.t142_gathered_mem
#print axioms ThomsonNine.ThirteenSource.t794_gathered_mem

#print axioms ThomsonNine.FourteenSource.t014_gathered_mem
#print axioms ThomsonNine.FourteenSource.t141_gathered_mem
#print axioms ThomsonNine.FourteenSource.t793_gathered_mem

#print axioms ThomsonNine.FifteenSource.t013_gathered_mem
#print axioms ThomsonNine.FifteenSource.t140_gathered_mem
#print axioms ThomsonNine.FifteenSource.t792_gathered_mem

#print axioms ThomsonNine.SixteenSource.t012_gathered_mem
#print axioms ThomsonNine.SixteenSource.t139_gathered_mem
#print axioms ThomsonNine.SixteenSource.t791_gathered_mem

#print axioms ThomsonNine.SeventeenSource.t011_gathered_mem
#print axioms ThomsonNine.SeventeenSource.t138_gathered_mem
#print axioms ThomsonNine.SeventeenSource.t790_gathered_mem
#print axioms ThomsonNine.MultiCorner.t125_gathered
#print axioms ThomsonNine.MultiCorner.t244_gathered
#print axioms ThomsonNine.MultiCorner.t330_gathered
#print axioms ThomsonNine.MultiCorner.t404_gathered
#print axioms ThomsonNine.MultiCorner.t470_gathered
#print axioms ThomsonNine.MultiCorner.t532_gathered
#print axioms ThomsonNine.MultiCorner.t538_gathered
#print axioms ThomsonNine.MultiCorner.t591_gathered
#print axioms ThomsonNine.MultiCorner.t608_gathered
#print axioms ThomsonNine.MultiCorner.t648_gathered
#print axioms ThomsonNine.MultiCorner.t672_gathered
#print axioms ThomsonNine.MultiCorner.t699_gathered
#print axioms ThomsonNine.MultiCorner.t726_gathered
#print axioms ThomsonNine.MultiCorner.t740_gathered
#print axioms ThomsonNine.MultiCorner.t766_gathered

#print axioms ThomsonNine.MultiCornerPow.t449_gathered
#print axioms ThomsonNine.MultiCornerPow.t464_gathered
#print axioms ThomsonNine.MultiCornerPow.t476_gathered
#print axioms ThomsonNine.MultiCornerPow.t485_gathered
#print axioms ThomsonNine.MultiCornerPow.t509_gathered
#print axioms ThomsonNine.MultiCornerPow.t553_gathered
#print axioms ThomsonNine.MultiCornerPow.t565_gathered
#print axioms ThomsonNine.MultiCornerPow.t619_gathered
#print axioms ThomsonNine.MultiCornerPow.t802_gathered

#print axioms ThomsonNine.MultiCornerP.t234_gathered
#print axioms ThomsonNine.MultiCornerP.t243_gathered
#print axioms ThomsonNine.MultiCornerP.t525_gathered
#print axioms ThomsonNine.MultiCornerP.t543_gathered
#print axioms ThomsonNine.MultiCornerP.t603_gathered
#print axioms ThomsonNine.MultiCornerP.t639_gathered
#print axioms ThomsonNine.MultiCornerP.t668_gathered
#print axioms ThomsonNine.MultiCornerP.t675_gathered
#print axioms ThomsonNine.MultiCornerP.t689_gathered
#print axioms ThomsonNine.MultiCornerP.t698_gathered
#print axioms ThomsonNine.MultiCornerP.t723_gathered
#print axioms ThomsonNine.MultiCornerP.t728_gathered
#print axioms ThomsonNine.MultiCornerP.t764_gathered
#print axioms ThomsonNine.GroupedT114.t114_gathered

#print axioms ThomsonNine.Grouped124.t124_gathered
#print axioms ThomsonNine.Grouped321.t321_gathered
#print axioms ThomsonNine.Grouped329.t329_gathered
#print axioms ThomsonNine.Grouped396.t396_gathered
#print axioms ThomsonNine.Grouped403.t403_gathered
#print axioms ThomsonNine.Grouped583.t583_gathered
#print axioms ThomsonNine.Grouped590.t590_gathered
#print axioms ThomsonNine.Grouped612.t612_gathered
#print axioms ThomsonNine.Grouped647.t647_gathered
#print axioms ThomsonNine.Grouped739.t739_gathered
#print axioms ThomsonNine.Grouped103.t103_gathered
#print axioms ThomsonNine.Grouped123.t123_gathered
#print axioms ThomsonNine.Grouped224.t224_gathered
#print axioms ThomsonNine.Grouped242.t242_gathered
#print axioms ThomsonNine.Grouped312.t312_gathered
#print axioms ThomsonNine.Grouped328.t328_gathered
#print axioms ThomsonNine.Grouped463.t463_gathered
#print axioms ThomsonNine.Grouped469.t469_gathered
#print axioms ThomsonNine.Grouped517.t517_gathered
#print axioms ThomsonNine.Grouped531.t531_gathered
#print axioms ThomsonNine.Grouped547.t547_gathered
#print axioms ThomsonNine.Grouped574.t574_gathered
#print axioms ThomsonNine.Grouped615.t615_gathered
#print axioms ThomsonNine.Grouped629.t629_gathered
