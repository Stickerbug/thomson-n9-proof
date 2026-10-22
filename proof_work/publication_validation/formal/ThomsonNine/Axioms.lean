import MainCoverage.Final
import ThomsonNine.ActualHermiteBounds
import ThomsonNine.ActualHermiteMinorant
import ThomsonNine.AAACenter
import ThomsonNine.ActualHermite
import ThomsonNine.IntervalListPolynomial
import ThomsonNine.IntervalInverse
import ThomsonNine.AAAFixedComplete
import ThomsonNine.GroupedTranslationCache
import ThomsonNine.AAAGroupedPilot
import ThomsonNine.Grouped597
import ThomsonNine.Grouped381
import ThomsonNine.Grouped409
import ThomsonNine.Grouped653
import ThomsonNine.Grouped286
import ThomsonNine.Grouped334
import ThomsonNine.Grouped703
import ThomsonNine.Grouped388
import ThomsonNine.Grouped402
import ThomsonNine.Grouped456
import ThomsonNine.Grouped475
import ThomsonNine.Grouped589
import ThomsonNine.Grouped596
import ThomsonNine.Grouped646
import ThomsonNine.Grouped664
import ThomsonNine.Grouped677
import ThomsonNine.Grouped697
import ThomsonNine.Grouped720
import ThomsonNine.Grouped738
import ThomsonNine.Grouped762
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

#print axioms ThomsonNine.Grouped646.t646_gathered
#print axioms ThomsonNine.Grouped664.t664_gathered
#print axioms ThomsonNine.Grouped677.t677_gathered
#print axioms ThomsonNine.Grouped697.t697_gathered
#print axioms ThomsonNine.Grouped720.t720_gathered
#print axioms ThomsonNine.Grouped738.t738_gathered
#print axioms ThomsonNine.Grouped762.t762_gathered

#print axioms ThomsonNine.Grouped597.t597_gathered
#print axioms ThomsonNine.Grouped381.t381_gathered
#print axioms ThomsonNine.Grouped409.t409_gathered
#print axioms ThomsonNine.Grouped653.t653_gathered
#print axioms ThomsonNine.Grouped286.t286_gathered
#print axioms ThomsonNine.Grouped334.t334_gathered
#print axioms ThomsonNine.Grouped703.t703_gathered
#print axioms ThomsonNine.Grouped388.t388_gathered
#print axioms ThomsonNine.Grouped402.t402_gathered
#print axioms ThomsonNine.Grouped456.t456_gathered
#print axioms ThomsonNine.Grouped475.t475_gathered
#print axioms ThomsonNine.Grouped589.t589_gathered
#print axioms ThomsonNine.Grouped596.t596_gathered

#print axioms ThomsonNine.Interval.SparsePolynomial.Grouped.regroup
#print axioms ThomsonNine.Interval.SparsePolynomial.Grouped.groupedCoeff_eq_gatheredOn
#print axioms ThomsonNine.Interval.SparsePolynomial.Grouped.groupedInterval_mem
#print axioms ThomsonNine.Interval.SparsePolynomial.Grouped.groupedInterval_mem_of_bounds
#print axioms ThomsonNine.AAAGroupedData.allTerms_complete
#print axioms ThomsonNine.AAAGroupedData.computed_mem_gathered
#print axioms ThomsonNine.AAAGroupedData.gathered_mem_of_bounds
#print axioms ThomsonNine.AAAGroupedPilot.bounds286
#print axioms ThomsonNine.AAAGroupedPilot.bounds000
#print axioms ThomsonNine.AAAGroupedPilot.t000_gathered

#print axioms ThomsonNine.Interval.SparsePolynomial.Grouped.cachedFinal_mem
#print axioms ThomsonNine.Interval.SparsePolynomial.Grouped.cachedFinal_mem_of_bounds
#print axioms ThomsonNine.FixedInterval.mem_zero
#print axioms ThomsonNine.FixedInterval.mem_add
#print axioms ThomsonNine.FixedInterval.mem_scale
#print axioms ThomsonNine.FixedInterval.mem_mul
#print axioms ThomsonNine.FixedInterval.power_mem
#print axioms ThomsonNine.FixedInterval.sum_mem
#print axioms ThomsonNine.FixedInterval.mem_of_rat
#print axioms ThomsonNine.FixedInterval.mem_to_rat
#print axioms ThomsonNine.FixedInterval.factor_mem
#print axioms ThomsonNine.FixedInterval.treeCoeff_eq
#print axioms ThomsonNine.FixedInterval.treeCompute_mem
#print axioms ThomsonNine.FixedInterval.gatheredOn_perm
#print axioms ThomsonNine.AAAFixedData.precision_pos
#print axioms ThomsonNine.AAAFixedData.source_bounds
#print axioms ThomsonNine.AAAFixedData.center_bounds
#print axioms ThomsonNine.AAAIndexedData.entries_eq
#print axioms ThomsonNine.AAAIndexedData.entryExp_pack
#print axioms ThomsonNine.AAATreeData.flat_entries
#print axioms ThomsonNine.AAATreeData.range_entries
#print axioms ThomsonNine.AAATreeData.indices_perm
#print axioms ThomsonNine.AAATreeData.tree_perm
#print axioms ThomsonNine.AAATreeData.tree_compatible
#print axioms ThomsonNine.AAATreeData.computed_mem
#print axioms ThomsonNine.AAATreeData.gathered_of_bounds
#print axioms ThomsonNine.AAAFixedComplete.bounds
#print axioms ThomsonNine.AAAFixedComplete.all_gathered
#print axioms ThomsonNine.AAAFixedComplete.gathered_h00_mem
#print axioms ThomsonNine.AAAFixedComplete.t001_gathered
#print axioms ThomsonNine.AAAFixedComplete.t002_gathered
#print axioms ThomsonNine.AAAFixedComplete.t003_gathered
#print axioms ThomsonNine.AAAFixedComplete.t004_gathered
#print axioms ThomsonNine.AAAFixedComplete.t005_gathered
#print axioms ThomsonNine.AAAFixedComplete.t006_gathered
#print axioms ThomsonNine.AAAFixedComplete.t007_gathered
#print axioms ThomsonNine.AAAFixedComplete.t008_gathered
#print axioms ThomsonNine.AAAFixedComplete.t009_gathered
#print axioms ThomsonNine.AAAFixedComplete.t010_gathered
#print axioms ThomsonNine.AAAFixedComplete.t028_gathered
#print axioms ThomsonNine.AAAFixedComplete.t029_gathered
#print axioms ThomsonNine.AAAFixedComplete.t030_gathered
#print axioms ThomsonNine.AAAFixedComplete.t031_gathered
#print axioms ThomsonNine.AAAFixedComplete.t032_gathered
#print axioms ThomsonNine.AAAFixedComplete.t033_gathered
#print axioms ThomsonNine.AAAFixedComplete.t034_gathered
#print axioms ThomsonNine.AAAFixedComplete.t035_gathered
#print axioms ThomsonNine.AAAFixedComplete.t036_gathered
#print axioms ThomsonNine.AAAFixedComplete.t037_gathered
#print axioms ThomsonNine.AAAFixedComplete.t039_gathered
#print axioms ThomsonNine.AAAFixedComplete.t040_gathered
#print axioms ThomsonNine.AAAFixedComplete.t041_gathered
#print axioms ThomsonNine.AAAFixedComplete.t042_gathered
#print axioms ThomsonNine.AAAFixedComplete.t043_gathered
#print axioms ThomsonNine.AAAFixedComplete.t044_gathered
#print axioms ThomsonNine.AAAFixedComplete.t045_gathered
#print axioms ThomsonNine.AAAFixedComplete.t046_gathered
#print axioms ThomsonNine.AAAFixedComplete.t047_gathered
#print axioms ThomsonNine.AAAFixedComplete.t048_gathered
#print axioms ThomsonNine.AAAFixedComplete.t050_gathered
#print axioms ThomsonNine.AAAFixedComplete.t051_gathered
#print axioms ThomsonNine.AAAFixedComplete.t052_gathered
#print axioms ThomsonNine.AAAFixedComplete.t053_gathered
#print axioms ThomsonNine.AAAFixedComplete.t054_gathered
#print axioms ThomsonNine.AAAFixedComplete.t055_gathered
#print axioms ThomsonNine.AAAFixedComplete.t056_gathered
#print axioms ThomsonNine.AAAFixedComplete.t057_gathered
#print axioms ThomsonNine.AAAFixedComplete.t058_gathered
#print axioms ThomsonNine.AAAFixedComplete.t059_gathered
#print axioms ThomsonNine.AAAFixedComplete.t061_gathered
#print axioms ThomsonNine.AAAFixedComplete.t062_gathered
#print axioms ThomsonNine.AAAFixedComplete.t063_gathered
#print axioms ThomsonNine.AAAFixedComplete.t064_gathered
#print axioms ThomsonNine.AAAFixedComplete.t065_gathered
#print axioms ThomsonNine.AAAFixedComplete.t066_gathered
#print axioms ThomsonNine.AAAFixedComplete.t067_gathered
#print axioms ThomsonNine.AAAFixedComplete.t068_gathered
#print axioms ThomsonNine.AAAFixedComplete.t069_gathered
#print axioms ThomsonNine.AAAFixedComplete.t070_gathered
#print axioms ThomsonNine.AAAFixedComplete.t072_gathered
#print axioms ThomsonNine.AAAFixedComplete.t073_gathered
#print axioms ThomsonNine.AAAFixedComplete.t074_gathered
#print axioms ThomsonNine.AAAFixedComplete.t075_gathered
#print axioms ThomsonNine.AAAFixedComplete.t076_gathered
#print axioms ThomsonNine.AAAFixedComplete.t077_gathered
#print axioms ThomsonNine.AAAFixedComplete.t078_gathered
#print axioms ThomsonNine.AAAFixedComplete.t079_gathered
#print axioms ThomsonNine.AAAFixedComplete.t080_gathered
#print axioms ThomsonNine.AAAFixedComplete.t081_gathered
#print axioms ThomsonNine.AAAFixedComplete.t083_gathered
#print axioms ThomsonNine.AAAFixedComplete.t084_gathered
#print axioms ThomsonNine.AAAFixedComplete.t085_gathered
#print axioms ThomsonNine.AAAFixedComplete.t086_gathered
#print axioms ThomsonNine.AAAFixedComplete.t087_gathered
#print axioms ThomsonNine.AAAFixedComplete.t088_gathered
#print axioms ThomsonNine.AAAFixedComplete.t089_gathered
#print axioms ThomsonNine.AAAFixedComplete.t090_gathered
#print axioms ThomsonNine.AAAFixedComplete.t091_gathered
#print axioms ThomsonNine.AAAFixedComplete.t092_gathered
#print axioms ThomsonNine.AAAFixedComplete.t094_gathered
#print axioms ThomsonNine.AAAFixedComplete.t095_gathered
#print axioms ThomsonNine.AAAFixedComplete.t096_gathered
#print axioms ThomsonNine.AAAFixedComplete.t097_gathered
#print axioms ThomsonNine.AAAFixedComplete.t098_gathered
#print axioms ThomsonNine.AAAFixedComplete.t099_gathered
#print axioms ThomsonNine.AAAFixedComplete.t100_gathered
#print axioms ThomsonNine.AAAFixedComplete.t101_gathered
#print axioms ThomsonNine.AAAFixedComplete.t102_gathered
#print axioms ThomsonNine.AAAFixedComplete.t105_gathered
#print axioms ThomsonNine.AAAFixedComplete.t106_gathered
#print axioms ThomsonNine.AAAFixedComplete.t107_gathered
#print axioms ThomsonNine.AAAFixedComplete.t108_gathered
#print axioms ThomsonNine.AAAFixedComplete.t109_gathered
#print axioms ThomsonNine.AAAFixedComplete.t110_gathered
#print axioms ThomsonNine.AAAFixedComplete.t111_gathered
#print axioms ThomsonNine.AAAFixedComplete.t112_gathered
#print axioms ThomsonNine.AAAFixedComplete.t113_gathered
#print axioms ThomsonNine.AAAFixedComplete.t116_gathered
#print axioms ThomsonNine.AAAFixedComplete.t117_gathered
#print axioms ThomsonNine.AAAFixedComplete.t118_gathered
#print axioms ThomsonNine.AAAFixedComplete.t119_gathered
#print axioms ThomsonNine.AAAFixedComplete.t120_gathered
#print axioms ThomsonNine.AAAFixedComplete.t121_gathered
#print axioms ThomsonNine.AAAFixedComplete.t122_gathered
#print axioms ThomsonNine.AAAFixedComplete.t127_gathered
#print axioms ThomsonNine.AAAFixedComplete.t155_gathered
#print axioms ThomsonNine.AAAFixedComplete.t156_gathered
#print axioms ThomsonNine.AAAFixedComplete.t157_gathered
#print axioms ThomsonNine.AAAFixedComplete.t158_gathered
#print axioms ThomsonNine.AAAFixedComplete.t159_gathered
#print axioms ThomsonNine.AAAFixedComplete.t160_gathered
#print axioms ThomsonNine.AAAFixedComplete.t161_gathered
#print axioms ThomsonNine.AAAFixedComplete.t162_gathered
#print axioms ThomsonNine.AAAFixedComplete.t163_gathered
#print axioms ThomsonNine.AAAFixedComplete.t164_gathered
#print axioms ThomsonNine.AAAFixedComplete.t166_gathered
#print axioms ThomsonNine.AAAFixedComplete.t167_gathered
#print axioms ThomsonNine.AAAFixedComplete.t168_gathered
#print axioms ThomsonNine.AAAFixedComplete.t169_gathered
#print axioms ThomsonNine.AAAFixedComplete.t170_gathered
#print axioms ThomsonNine.AAAFixedComplete.t171_gathered
#print axioms ThomsonNine.AAAFixedComplete.t172_gathered
#print axioms ThomsonNine.AAAFixedComplete.t173_gathered
#print axioms ThomsonNine.AAAFixedComplete.t174_gathered
#print axioms ThomsonNine.AAAFixedComplete.t175_gathered
#print axioms ThomsonNine.AAAFixedComplete.t176_gathered
#print axioms ThomsonNine.AAAFixedComplete.t177_gathered
#print axioms ThomsonNine.AAAFixedComplete.t178_gathered
#print axioms ThomsonNine.AAAFixedComplete.t179_gathered
#print axioms ThomsonNine.AAAFixedComplete.t180_gathered
#print axioms ThomsonNine.AAAFixedComplete.t181_gathered
#print axioms ThomsonNine.AAAFixedComplete.t182_gathered
#print axioms ThomsonNine.AAAFixedComplete.t183_gathered
#print axioms ThomsonNine.AAAFixedComplete.t184_gathered
#print axioms ThomsonNine.AAAFixedComplete.t186_gathered
#print axioms ThomsonNine.AAAFixedComplete.t187_gathered
#print axioms ThomsonNine.AAAFixedComplete.t188_gathered
#print axioms ThomsonNine.AAAFixedComplete.t189_gathered
#print axioms ThomsonNine.AAAFixedComplete.t190_gathered
#print axioms ThomsonNine.AAAFixedComplete.t191_gathered
#print axioms ThomsonNine.AAAFixedComplete.t192_gathered
#print axioms ThomsonNine.AAAFixedComplete.t193_gathered
#print axioms ThomsonNine.AAAFixedComplete.t194_gathered
#print axioms ThomsonNine.AAAFixedComplete.t196_gathered
#print axioms ThomsonNine.AAAFixedComplete.t197_gathered
#print axioms ThomsonNine.AAAFixedComplete.t198_gathered
#print axioms ThomsonNine.AAAFixedComplete.t199_gathered
#print axioms ThomsonNine.AAAFixedComplete.t200_gathered
#print axioms ThomsonNine.AAAFixedComplete.t201_gathered
#print axioms ThomsonNine.AAAFixedComplete.t202_gathered
#print axioms ThomsonNine.AAAFixedComplete.t203_gathered
#print axioms ThomsonNine.AAAFixedComplete.t204_gathered
#print axioms ThomsonNine.AAAFixedComplete.t206_gathered
#print axioms ThomsonNine.AAAFixedComplete.t207_gathered
#print axioms ThomsonNine.AAAFixedComplete.t208_gathered
#print axioms ThomsonNine.AAAFixedComplete.t209_gathered
#print axioms ThomsonNine.AAAFixedComplete.t210_gathered
#print axioms ThomsonNine.AAAFixedComplete.t211_gathered
#print axioms ThomsonNine.AAAFixedComplete.t212_gathered
#print axioms ThomsonNine.AAAFixedComplete.t213_gathered
#print axioms ThomsonNine.AAAFixedComplete.t214_gathered
#print axioms ThomsonNine.AAAFixedComplete.t216_gathered
#print axioms ThomsonNine.AAAFixedComplete.t217_gathered
#print axioms ThomsonNine.AAAFixedComplete.t218_gathered
#print axioms ThomsonNine.AAAFixedComplete.t219_gathered
#print axioms ThomsonNine.AAAFixedComplete.t220_gathered
#print axioms ThomsonNine.AAAFixedComplete.t221_gathered
#print axioms ThomsonNine.AAAFixedComplete.t222_gathered
#print axioms ThomsonNine.AAAFixedComplete.t223_gathered
#print axioms ThomsonNine.AAAFixedComplete.t226_gathered
#print axioms ThomsonNine.AAAFixedComplete.t227_gathered
#print axioms ThomsonNine.AAAFixedComplete.t228_gathered
#print axioms ThomsonNine.AAAFixedComplete.t229_gathered
#print axioms ThomsonNine.AAAFixedComplete.t230_gathered
#print axioms ThomsonNine.AAAFixedComplete.t231_gathered
#print axioms ThomsonNine.AAAFixedComplete.t232_gathered
#print axioms ThomsonNine.AAAFixedComplete.t233_gathered
#print axioms ThomsonNine.AAAFixedComplete.t236_gathered
#print axioms ThomsonNine.AAAFixedComplete.t237_gathered
#print axioms ThomsonNine.AAAFixedComplete.t238_gathered
#print axioms ThomsonNine.AAAFixedComplete.t239_gathered
#print axioms ThomsonNine.AAAFixedComplete.t240_gathered
#print axioms ThomsonNine.AAAFixedComplete.t241_gathered
#print axioms ThomsonNine.AAAFixedComplete.t246_gathered
#print axioms ThomsonNine.AAAFixedComplete.t247_gathered
#print axioms ThomsonNine.AAAFixedComplete.t257_gathered
#print axioms ThomsonNine.AAAFixedComplete.t258_gathered
#print axioms ThomsonNine.AAAFixedComplete.t259_gathered
#print axioms ThomsonNine.AAAFixedComplete.t260_gathered
#print axioms ThomsonNine.AAAFixedComplete.t261_gathered
#print axioms ThomsonNine.AAAFixedComplete.t262_gathered
#print axioms ThomsonNine.AAAFixedComplete.t263_gathered
#print axioms ThomsonNine.AAAFixedComplete.t264_gathered
#print axioms ThomsonNine.AAAFixedComplete.t265_gathered
#print axioms ThomsonNine.AAAFixedComplete.t266_gathered
#print axioms ThomsonNine.AAAFixedComplete.t268_gathered
#print axioms ThomsonNine.AAAFixedComplete.t269_gathered
#print axioms ThomsonNine.AAAFixedComplete.t270_gathered
#print axioms ThomsonNine.AAAFixedComplete.t271_gathered
#print axioms ThomsonNine.AAAFixedComplete.t272_gathered
#print axioms ThomsonNine.AAAFixedComplete.t273_gathered
#print axioms ThomsonNine.AAAFixedComplete.t274_gathered
#print axioms ThomsonNine.AAAFixedComplete.t275_gathered
#print axioms ThomsonNine.AAAFixedComplete.t276_gathered
#print axioms ThomsonNine.AAAFixedComplete.t278_gathered
#print axioms ThomsonNine.AAAFixedComplete.t279_gathered
#print axioms ThomsonNine.AAAFixedComplete.t280_gathered
#print axioms ThomsonNine.AAAFixedComplete.t281_gathered
#print axioms ThomsonNine.AAAFixedComplete.t282_gathered
#print axioms ThomsonNine.AAAFixedComplete.t283_gathered
#print axioms ThomsonNine.AAAFixedComplete.t284_gathered
#print axioms ThomsonNine.AAAFixedComplete.t285_gathered
#print axioms ThomsonNine.AAAFixedComplete.t287_gathered
#print axioms ThomsonNine.AAAFixedComplete.t288_gathered
#print axioms ThomsonNine.AAAFixedComplete.t289_gathered
#print axioms ThomsonNine.AAAFixedComplete.t290_gathered
#print axioms ThomsonNine.AAAFixedComplete.t291_gathered
#print axioms ThomsonNine.AAAFixedComplete.t292_gathered
#print axioms ThomsonNine.AAAFixedComplete.t293_gathered
#print axioms ThomsonNine.AAAFixedComplete.t294_gathered
#print axioms ThomsonNine.AAAFixedComplete.t296_gathered
#print axioms ThomsonNine.AAAFixedComplete.t297_gathered
#print axioms ThomsonNine.AAAFixedComplete.t298_gathered
#print axioms ThomsonNine.AAAFixedComplete.t299_gathered
#print axioms ThomsonNine.AAAFixedComplete.t300_gathered
#print axioms ThomsonNine.AAAFixedComplete.t301_gathered
#print axioms ThomsonNine.AAAFixedComplete.t302_gathered
#print axioms ThomsonNine.AAAFixedComplete.t303_gathered
#print axioms ThomsonNine.AAAFixedComplete.t305_gathered
#print axioms ThomsonNine.AAAFixedComplete.t306_gathered
#print axioms ThomsonNine.AAAFixedComplete.t307_gathered
#print axioms ThomsonNine.AAAFixedComplete.t308_gathered
#print axioms ThomsonNine.AAAFixedComplete.t309_gathered
#print axioms ThomsonNine.AAAFixedComplete.t310_gathered
#print axioms ThomsonNine.AAAFixedComplete.t311_gathered
#print axioms ThomsonNine.AAAFixedComplete.t314_gathered
#print axioms ThomsonNine.AAAFixedComplete.t315_gathered
#print axioms ThomsonNine.AAAFixedComplete.t316_gathered
#print axioms ThomsonNine.AAAFixedComplete.t317_gathered
#print axioms ThomsonNine.AAAFixedComplete.t318_gathered
#print axioms ThomsonNine.AAAFixedComplete.t319_gathered
#print axioms ThomsonNine.AAAFixedComplete.t320_gathered
#print axioms ThomsonNine.AAAFixedComplete.t323_gathered
#print axioms ThomsonNine.AAAFixedComplete.t324_gathered
#print axioms ThomsonNine.AAAFixedComplete.t325_gathered
#print axioms ThomsonNine.AAAFixedComplete.t326_gathered
#print axioms ThomsonNine.AAAFixedComplete.t327_gathered
#print axioms ThomsonNine.AAAFixedComplete.t332_gathered
#print axioms ThomsonNine.AAAFixedComplete.t333_gathered
#print axioms ThomsonNine.AAAFixedComplete.t341_gathered
#print axioms ThomsonNine.AAAFixedComplete.t344_gathered
#print axioms ThomsonNine.AAAFixedComplete.t345_gathered
#print axioms ThomsonNine.AAAFixedComplete.t346_gathered
#print axioms ThomsonNine.AAAFixedComplete.t347_gathered
#print axioms ThomsonNine.AAAFixedComplete.t348_gathered
#print axioms ThomsonNine.AAAFixedComplete.t349_gathered
#print axioms ThomsonNine.AAAFixedComplete.t350_gathered
#print axioms ThomsonNine.AAAFixedComplete.t351_gathered
#print axioms ThomsonNine.AAAFixedComplete.t352_gathered
#print axioms ThomsonNine.AAAFixedComplete.t353_gathered
#print axioms ThomsonNine.AAAFixedComplete.t355_gathered
#print axioms ThomsonNine.AAAFixedComplete.t356_gathered
#print axioms ThomsonNine.AAAFixedComplete.t357_gathered
#print axioms ThomsonNine.AAAFixedComplete.t358_gathered
#print axioms ThomsonNine.AAAFixedComplete.t359_gathered
#print axioms ThomsonNine.AAAFixedComplete.t360_gathered
#print axioms ThomsonNine.AAAFixedComplete.t361_gathered
#print axioms ThomsonNine.AAAFixedComplete.t362_gathered
#print axioms ThomsonNine.AAAFixedComplete.t363_gathered
#print axioms ThomsonNine.AAAFixedComplete.t365_gathered
#print axioms ThomsonNine.AAAFixedComplete.t366_gathered
#print axioms ThomsonNine.AAAFixedComplete.t367_gathered
#print axioms ThomsonNine.AAAFixedComplete.t368_gathered
#print axioms ThomsonNine.AAAFixedComplete.t369_gathered
#print axioms ThomsonNine.AAAFixedComplete.t370_gathered
#print axioms ThomsonNine.AAAFixedComplete.t371_gathered
#print axioms ThomsonNine.AAAFixedComplete.t372_gathered
#print axioms ThomsonNine.AAAFixedComplete.t374_gathered
#print axioms ThomsonNine.AAAFixedComplete.t375_gathered
#print axioms ThomsonNine.AAAFixedComplete.t376_gathered
#print axioms ThomsonNine.AAAFixedComplete.t377_gathered
#print axioms ThomsonNine.AAAFixedComplete.t378_gathered
#print axioms ThomsonNine.AAAFixedComplete.t379_gathered
#print axioms ThomsonNine.AAAFixedComplete.t380_gathered
#print axioms ThomsonNine.AAAFixedComplete.t382_gathered
#print axioms ThomsonNine.AAAFixedComplete.t383_gathered
#print axioms ThomsonNine.AAAFixedComplete.t384_gathered
#print axioms ThomsonNine.AAAFixedComplete.t385_gathered
#print axioms ThomsonNine.AAAFixedComplete.t386_gathered
#print axioms ThomsonNine.AAAFixedComplete.t387_gathered
#print axioms ThomsonNine.AAAFixedComplete.t390_gathered
#print axioms ThomsonNine.AAAFixedComplete.t391_gathered
#print axioms ThomsonNine.AAAFixedComplete.t392_gathered
#print axioms ThomsonNine.AAAFixedComplete.t393_gathered
#print axioms ThomsonNine.AAAFixedComplete.t394_gathered
#print axioms ThomsonNine.AAAFixedComplete.t395_gathered
#print axioms ThomsonNine.AAAFixedComplete.t398_gathered
#print axioms ThomsonNine.AAAFixedComplete.t399_gathered
#print axioms ThomsonNine.AAAFixedComplete.t400_gathered
#print axioms ThomsonNine.AAAFixedComplete.t401_gathered
#print axioms ThomsonNine.AAAFixedComplete.t406_gathered
#print axioms ThomsonNine.AAAFixedComplete.t407_gathered
#print axioms ThomsonNine.AAAFixedComplete.t408_gathered
#print axioms ThomsonNine.AAAFixedComplete.t414_gathered
#print axioms ThomsonNine.AAAFixedComplete.t415_gathered
#print axioms ThomsonNine.AAAFixedComplete.t417_gathered
#print axioms ThomsonNine.AAAFixedComplete.t420_gathered
#print axioms ThomsonNine.AAAFixedComplete.t421_gathered
#print axioms ThomsonNine.AAAFixedComplete.t422_gathered
#print axioms ThomsonNine.AAAFixedComplete.t423_gathered
#print axioms ThomsonNine.AAAFixedComplete.t424_gathered
#print axioms ThomsonNine.AAAFixedComplete.t425_gathered
#print axioms ThomsonNine.AAAFixedComplete.t426_gathered
#print axioms ThomsonNine.AAAFixedComplete.t427_gathered
#print axioms ThomsonNine.AAAFixedComplete.t428_gathered
#print axioms ThomsonNine.AAAFixedComplete.t429_gathered
#print axioms ThomsonNine.AAAFixedComplete.t431_gathered
#print axioms ThomsonNine.AAAFixedComplete.t432_gathered
#print axioms ThomsonNine.AAAFixedComplete.t433_gathered
#print axioms ThomsonNine.AAAFixedComplete.t434_gathered
#print axioms ThomsonNine.AAAFixedComplete.t435_gathered
#print axioms ThomsonNine.AAAFixedComplete.t436_gathered
#print axioms ThomsonNine.AAAFixedComplete.t437_gathered
#print axioms ThomsonNine.AAAFixedComplete.t438_gathered
#print axioms ThomsonNine.AAAFixedComplete.t439_gathered
#print axioms ThomsonNine.AAAFixedComplete.t441_gathered
#print axioms ThomsonNine.AAAFixedComplete.t442_gathered
#print axioms ThomsonNine.AAAFixedComplete.t443_gathered
#print axioms ThomsonNine.AAAFixedComplete.t444_gathered
#print axioms ThomsonNine.AAAFixedComplete.t445_gathered
#print axioms ThomsonNine.AAAFixedComplete.t446_gathered
#print axioms ThomsonNine.AAAFixedComplete.t447_gathered
#print axioms ThomsonNine.AAAFixedComplete.t448_gathered
#print axioms ThomsonNine.AAAFixedComplete.t450_gathered
#print axioms ThomsonNine.AAAFixedComplete.t451_gathered
#print axioms ThomsonNine.AAAFixedComplete.t452_gathered
#print axioms ThomsonNine.AAAFixedComplete.t453_gathered
#print axioms ThomsonNine.AAAFixedComplete.t454_gathered
#print axioms ThomsonNine.AAAFixedComplete.t455_gathered
#print axioms ThomsonNine.AAAFixedComplete.t458_gathered
#print axioms ThomsonNine.AAAFixedComplete.t459_gathered
#print axioms ThomsonNine.AAAFixedComplete.t460_gathered
#print axioms ThomsonNine.AAAFixedComplete.t461_gathered
#print axioms ThomsonNine.AAAFixedComplete.t462_gathered
#print axioms ThomsonNine.AAAFixedComplete.t465_gathered
#print axioms ThomsonNine.AAAFixedComplete.t466_gathered
#print axioms ThomsonNine.AAAFixedComplete.t467_gathered
#print axioms ThomsonNine.AAAFixedComplete.t468_gathered
#print axioms ThomsonNine.AAAFixedComplete.t472_gathered
#print axioms ThomsonNine.AAAFixedComplete.t473_gathered
#print axioms ThomsonNine.AAAFixedComplete.t474_gathered
#print axioms ThomsonNine.AAAFixedComplete.t479_gathered
#print axioms ThomsonNine.AAAFixedComplete.t480_gathered
#print axioms ThomsonNine.AAAFixedComplete.t481_gathered
#print axioms ThomsonNine.AAAFixedComplete.t483_gathered
#print axioms ThomsonNine.AAAFixedComplete.t484_gathered
#print axioms ThomsonNine.AAAFixedComplete.t486_gathered
#print axioms ThomsonNine.AAAFixedComplete.t489_gathered
#print axioms ThomsonNine.AAAFixedComplete.t490_gathered
#print axioms ThomsonNine.AAAFixedComplete.t491_gathered
#print axioms ThomsonNine.AAAFixedComplete.t492_gathered
#print axioms ThomsonNine.AAAFixedComplete.t493_gathered
#print axioms ThomsonNine.AAAFixedComplete.t494_gathered
#print axioms ThomsonNine.AAAFixedComplete.t495_gathered
#print axioms ThomsonNine.AAAFixedComplete.t496_gathered
#print axioms ThomsonNine.AAAFixedComplete.t497_gathered
#print axioms ThomsonNine.AAAFixedComplete.t498_gathered
#print axioms ThomsonNine.AAAFixedComplete.t500_gathered
#print axioms ThomsonNine.AAAFixedComplete.t501_gathered
#print axioms ThomsonNine.AAAFixedComplete.t502_gathered
#print axioms ThomsonNine.AAAFixedComplete.t503_gathered
#print axioms ThomsonNine.AAAFixedComplete.t504_gathered
#print axioms ThomsonNine.AAAFixedComplete.t505_gathered
#print axioms ThomsonNine.AAAFixedComplete.t506_gathered
#print axioms ThomsonNine.AAAFixedComplete.t507_gathered
#print axioms ThomsonNine.AAAFixedComplete.t508_gathered
#print axioms ThomsonNine.AAAFixedComplete.t510_gathered
#print axioms ThomsonNine.AAAFixedComplete.t511_gathered
#print axioms ThomsonNine.AAAFixedComplete.t512_gathered
#print axioms ThomsonNine.AAAFixedComplete.t513_gathered
#print axioms ThomsonNine.AAAFixedComplete.t514_gathered
#print axioms ThomsonNine.AAAFixedComplete.t515_gathered
#print axioms ThomsonNine.AAAFixedComplete.t516_gathered
#print axioms ThomsonNine.AAAFixedComplete.t519_gathered
#print axioms ThomsonNine.AAAFixedComplete.t520_gathered
#print axioms ThomsonNine.AAAFixedComplete.t521_gathered
#print axioms ThomsonNine.AAAFixedComplete.t522_gathered
#print axioms ThomsonNine.AAAFixedComplete.t523_gathered
#print axioms ThomsonNine.AAAFixedComplete.t524_gathered
#print axioms ThomsonNine.AAAFixedComplete.t527_gathered
#print axioms ThomsonNine.AAAFixedComplete.t528_gathered
#print axioms ThomsonNine.AAAFixedComplete.t529_gathered
#print axioms ThomsonNine.AAAFixedComplete.t530_gathered
#print axioms ThomsonNine.AAAFixedComplete.t534_gathered
#print axioms ThomsonNine.AAAFixedComplete.t535_gathered
#print axioms ThomsonNine.AAAFixedComplete.t536_gathered
#print axioms ThomsonNine.AAAFixedComplete.t537_gathered
#print axioms ThomsonNine.AAAFixedComplete.t540_gathered
#print axioms ThomsonNine.AAAFixedComplete.t541_gathered
#print axioms ThomsonNine.AAAFixedComplete.t542_gathered
#print axioms ThomsonNine.AAAFixedComplete.t545_gathered
#print axioms ThomsonNine.AAAFixedComplete.t546_gathered
#print axioms ThomsonNine.AAAFixedComplete.t549_gathered
#print axioms ThomsonNine.AAAFixedComplete.t550_gathered
#print axioms ThomsonNine.AAAFixedComplete.t552_gathered
#print axioms ThomsonNine.AAAFixedComplete.t555_gathered
#print axioms ThomsonNine.AAAFixedComplete.t556_gathered
#print axioms ThomsonNine.AAAFixedComplete.t557_gathered
#print axioms ThomsonNine.AAAFixedComplete.t558_gathered
#print axioms ThomsonNine.AAAFixedComplete.t559_gathered
#print axioms ThomsonNine.AAAFixedComplete.t560_gathered
#print axioms ThomsonNine.AAAFixedComplete.t561_gathered
#print axioms ThomsonNine.AAAFixedComplete.t562_gathered
#print axioms ThomsonNine.AAAFixedComplete.t563_gathered
#print axioms ThomsonNine.AAAFixedComplete.t564_gathered
#print axioms ThomsonNine.AAAFixedComplete.t566_gathered
#print axioms ThomsonNine.AAAFixedComplete.t567_gathered
#print axioms ThomsonNine.AAAFixedComplete.t568_gathered
#print axioms ThomsonNine.AAAFixedComplete.t569_gathered
#print axioms ThomsonNine.AAAFixedComplete.t570_gathered
#print axioms ThomsonNine.AAAFixedComplete.t571_gathered
#print axioms ThomsonNine.AAAFixedComplete.t572_gathered
#print axioms ThomsonNine.AAAFixedComplete.t573_gathered
#print axioms ThomsonNine.AAAFixedComplete.t576_gathered
#print axioms ThomsonNine.AAAFixedComplete.t577_gathered
#print axioms ThomsonNine.AAAFixedComplete.t578_gathered
#print axioms ThomsonNine.AAAFixedComplete.t579_gathered
#print axioms ThomsonNine.AAAFixedComplete.t580_gathered
#print axioms ThomsonNine.AAAFixedComplete.t581_gathered
#print axioms ThomsonNine.AAAFixedComplete.t582_gathered
#print axioms ThomsonNine.AAAFixedComplete.t585_gathered
#print axioms ThomsonNine.AAAFixedComplete.t586_gathered
#print axioms ThomsonNine.AAAFixedComplete.t587_gathered
#print axioms ThomsonNine.AAAFixedComplete.t588_gathered
#print axioms ThomsonNine.AAAFixedComplete.t593_gathered
#print axioms ThomsonNine.AAAFixedComplete.t594_gathered
#print axioms ThomsonNine.AAAFixedComplete.t595_gathered
#print axioms ThomsonNine.AAAFixedComplete.t600_gathered
#print axioms ThomsonNine.AAAFixedComplete.t601_gathered
#print axioms ThomsonNine.AAAFixedComplete.t602_gathered
#print axioms ThomsonNine.AAAFixedComplete.t605_gathered
#print axioms ThomsonNine.AAAFixedComplete.t606_gathered
#print axioms ThomsonNine.AAAFixedComplete.t607_gathered
#print axioms ThomsonNine.AAAFixedComplete.t610_gathered
#print axioms ThomsonNine.AAAFixedComplete.t611_gathered
#print axioms ThomsonNine.AAAFixedComplete.t614_gathered
#print axioms ThomsonNine.AAAFixedComplete.t617_gathered
#print axioms ThomsonNine.AAAFixedComplete.t620_gathered
#print axioms ThomsonNine.AAAFixedComplete.t621_gathered
#print axioms ThomsonNine.AAAFixedComplete.t622_gathered
#print axioms ThomsonNine.AAAFixedComplete.t623_gathered
#print axioms ThomsonNine.AAAFixedComplete.t624_gathered
#print axioms ThomsonNine.AAAFixedComplete.t625_gathered
#print axioms ThomsonNine.AAAFixedComplete.t626_gathered
#print axioms ThomsonNine.AAAFixedComplete.t627_gathered
#print axioms ThomsonNine.AAAFixedComplete.t628_gathered
#print axioms ThomsonNine.AAAFixedComplete.t631_gathered
#print axioms ThomsonNine.AAAFixedComplete.t632_gathered
#print axioms ThomsonNine.AAAFixedComplete.t633_gathered
#print axioms ThomsonNine.AAAFixedComplete.t634_gathered
#print axioms ThomsonNine.AAAFixedComplete.t635_gathered
#print axioms ThomsonNine.AAAFixedComplete.t636_gathered
#print axioms ThomsonNine.AAAFixedComplete.t637_gathered
#print axioms ThomsonNine.AAAFixedComplete.t638_gathered
#print axioms ThomsonNine.AAAFixedComplete.t641_gathered
#print axioms ThomsonNine.AAAFixedComplete.t642_gathered
#print axioms ThomsonNine.AAAFixedComplete.t643_gathered
#print axioms ThomsonNine.AAAFixedComplete.t644_gathered
#print axioms ThomsonNine.AAAFixedComplete.t645_gathered
#print axioms ThomsonNine.AAAFixedComplete.t650_gathered
#print axioms ThomsonNine.AAAFixedComplete.t651_gathered
#print axioms ThomsonNine.AAAFixedComplete.t652_gathered
#print axioms ThomsonNine.AAAFixedComplete.t658_gathered
#print axioms ThomsonNine.AAAFixedComplete.t659_gathered
#print axioms ThomsonNine.AAAFixedComplete.t660_gathered
#print axioms ThomsonNine.AAAFixedComplete.t662_gathered
#print axioms ThomsonNine.AAAFixedComplete.t663_gathered
#print axioms ThomsonNine.AAAFixedComplete.t666_gathered
#print axioms ThomsonNine.AAAFixedComplete.t667_gathered
#print axioms ThomsonNine.AAAFixedComplete.t670_gathered
#print axioms ThomsonNine.AAAFixedComplete.t671_gathered
#print axioms ThomsonNine.AAAFixedComplete.t674_gathered
#print axioms ThomsonNine.AAAFixedComplete.t680_gathered
#print axioms ThomsonNine.AAAFixedComplete.t681_gathered
#print axioms ThomsonNine.AAAFixedComplete.t682_gathered
#print axioms ThomsonNine.AAAFixedComplete.t683_gathered
#print axioms ThomsonNine.AAAFixedComplete.t684_gathered
#print axioms ThomsonNine.AAAFixedComplete.t685_gathered
#print axioms ThomsonNine.AAAFixedComplete.t686_gathered
#print axioms ThomsonNine.AAAFixedComplete.t687_gathered
#print axioms ThomsonNine.AAAFixedComplete.t688_gathered
#print axioms ThomsonNine.AAAFixedComplete.t691_gathered
#print axioms ThomsonNine.AAAFixedComplete.t692_gathered
#print axioms ThomsonNine.AAAFixedComplete.t693_gathered
#print axioms ThomsonNine.AAAFixedComplete.t694_gathered
#print axioms ThomsonNine.AAAFixedComplete.t695_gathered
#print axioms ThomsonNine.AAAFixedComplete.t696_gathered
#print axioms ThomsonNine.AAAFixedComplete.t701_gathered
#print axioms ThomsonNine.AAAFixedComplete.t702_gathered
#print axioms ThomsonNine.AAAFixedComplete.t710_gathered
#print axioms ThomsonNine.AAAFixedComplete.t711_gathered
#print axioms ThomsonNine.AAAFixedComplete.t713_gathered
#print axioms ThomsonNine.AAAFixedComplete.t714_gathered
#print axioms ThomsonNine.AAAFixedComplete.t716_gathered
#print axioms ThomsonNine.AAAFixedComplete.t717_gathered
#print axioms ThomsonNine.AAAFixedComplete.t719_gathered
#print axioms ThomsonNine.AAAFixedComplete.t722_gathered
#print axioms ThomsonNine.AAAFixedComplete.t725_gathered
#print axioms ThomsonNine.AAAFixedComplete.t731_gathered
#print axioms ThomsonNine.AAAFixedComplete.t732_gathered
#print axioms ThomsonNine.AAAFixedComplete.t733_gathered
#print axioms ThomsonNine.AAAFixedComplete.t734_gathered
#print axioms ThomsonNine.AAAFixedComplete.t735_gathered
#print axioms ThomsonNine.AAAFixedComplete.t736_gathered
#print axioms ThomsonNine.AAAFixedComplete.t737_gathered
#print axioms ThomsonNine.AAAFixedComplete.t742_gathered
#print axioms ThomsonNine.AAAFixedComplete.t743_gathered
#print axioms ThomsonNine.AAAFixedComplete.t752_gathered
#print axioms ThomsonNine.AAAFixedComplete.t754_gathered
#print axioms ThomsonNine.AAAFixedComplete.t756_gathered
#print axioms ThomsonNine.AAAFixedComplete.t758_gathered
#print axioms ThomsonNine.AAAFixedComplete.t760_gathered
#print axioms ThomsonNine.AAAFixedComplete.t769_gathered

#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.mem_lowerBox
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.tripleSum_eq_box
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.map_filter_sum
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.tripleSum_eq_targets
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.exchange
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.expandedEval_eq_gathered
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.eval_shift_collected
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.natMask_mem
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.encode_inj
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.mem_of_code
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.downward_nat
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.lower_closed_of_steps
#print axioms ThomsonNine.Interval.SparsePolynomial.Collected.lower_closed_of_mask
#print axioms ThomsonNine.AAASupport.support_eq
#print axioms ThomsonNine.AAASupport.codes_eq
#print axioms ThomsonNine.AAASupport.mask_eq
#print axioms ThomsonNine.AAASupport.codes_nodup
#print axioms ThomsonNine.AAASupport.support_nodup
#print axioms ThomsonNine.AAASupport.support_bounded
#print axioms ThomsonNine.AAASupport.predecessor0
#print axioms ThomsonNine.AAASupport.predecessor1
#print axioms ThomsonNine.AAASupport.predecessor2
#print axioms ThomsonNine.AAASupport.support_lower_closed
#print axioms ThomsonNine.Interval.SparsePolynomial.axisDeriv_translate
#print axioms ThomsonNine.Interval.SparsePolynomial.axisDeriv_axisDeriv_translate
#print axioms ThomsonNine.AAACollected.eval_eq_map_sum
#print axioms ThomsonNine.AAACollected.eval_shift_gathered
#print axioms ThomsonNine.AAACollected.terms_eq_allTerms
#print axioms ThomsonNine.AAACollected.source_h00_mem
#print axioms ThomsonNine.Interval.RatInterval.mem_sqrt_of_bounds
#print axioms ThomsonNine.RadiusLo.sqrt0_mem
#print axioms ThomsonNine.RadiusLo.sqrt1_mem
#print axioms ThomsonNine.RadiusLo.sqrt2_mem
#print axioms ThomsonNine.RadiusLo.sqrt3_mem
#print axioms ThomsonNine.RadiusLo.sqrt4_mem
#print axioms ThomsonNine.RadiusLo.term0_mem
#print axioms ThomsonNine.RadiusLo.term1_mem
#print axioms ThomsonNine.RadiusLo.term2_mem
#print axioms ThomsonNine.RadiusLo.term3_mem
#print axioms ThomsonNine.RadiusLo.term4_mem
#print axioms ThomsonNine.RadiusLo.result_mem
#print axioms ThomsonNine.RadiusLo.derivative_neg
#print axioms ThomsonNine.RadiusHi.sqrt0_mem
#print axioms ThomsonNine.RadiusHi.sqrt1_mem
#print axioms ThomsonNine.RadiusHi.sqrt2_mem
#print axioms ThomsonNine.RadiusHi.sqrt3_mem
#print axioms ThomsonNine.RadiusHi.sqrt4_mem
#print axioms ThomsonNine.RadiusHi.term0_mem
#print axioms ThomsonNine.RadiusHi.term1_mem
#print axioms ThomsonNine.RadiusHi.term2_mem
#print axioms ThomsonNine.RadiusHi.term3_mem
#print axioms ThomsonNine.RadiusHi.term4_mem
#print axioms ThomsonNine.RadiusHi.result_mem
#print axioms ThomsonNine.RadiusHi.derivative_pos
#print axioms ThomsonNine.RefinedRadius.rational_bounds
#print axioms ThomsonNine.RefinedRadius.exists_root
#print axioms ThomsonNine.RefinedRadius.radius_mem
#print axioms ThomsonNine.RefinedRadius.radius_derivative_zero
#print axioms ThomsonNine.RefinedRadius.radius_pos
#print axioms ThomsonNine.RefinedRadius.radius_lt_one
#print axioms ThomsonNine.RefinedRadius.radius_stationary
#print axioms ThomsonNine.RefinedRadius.radius_unique
#print axioms ThomsonNine.RefinedRadius.centerComputed_mem
#print axioms ThomsonNine.RefinedRadius.center_bounds
#print axioms ThomsonNine.RefinedRadius.aaaCenter_mem
#print axioms ThomsonNine.RefinedRadius.source_h00_at_actual_center
#print axioms ThomsonNine.RadiusTightLo.sqrt0_mem
#print axioms ThomsonNine.RadiusTightLo.sqrt1_mem
#print axioms ThomsonNine.RadiusTightLo.sqrt2_mem
#print axioms ThomsonNine.RadiusTightLo.sqrt3_mem
#print axioms ThomsonNine.RadiusTightLo.sqrt4_mem
#print axioms ThomsonNine.RadiusTightLo.term0_mem
#print axioms ThomsonNine.RadiusTightLo.term1_mem
#print axioms ThomsonNine.RadiusTightLo.term2_mem
#print axioms ThomsonNine.RadiusTightLo.term3_mem
#print axioms ThomsonNine.RadiusTightLo.term4_mem
#print axioms ThomsonNine.RadiusTightLo.result_mem
#print axioms ThomsonNine.RadiusTightLo.derivative_neg
#print axioms ThomsonNine.RadiusTightHi.sqrt0_mem
#print axioms ThomsonNine.RadiusTightHi.sqrt1_mem
#print axioms ThomsonNine.RadiusTightHi.sqrt2_mem
#print axioms ThomsonNine.RadiusTightHi.sqrt3_mem
#print axioms ThomsonNine.RadiusTightHi.sqrt4_mem
#print axioms ThomsonNine.RadiusTightHi.term0_mem
#print axioms ThomsonNine.RadiusTightHi.term1_mem
#print axioms ThomsonNine.RadiusTightHi.term2_mem
#print axioms ThomsonNine.RadiusTightHi.term3_mem
#print axioms ThomsonNine.RadiusTightHi.term4_mem
#print axioms ThomsonNine.RadiusTightHi.result_mem
#print axioms ThomsonNine.RadiusTightHi.derivative_pos
#print axioms ThomsonNine.RefinedRadius.tight_rational_bounds
#print axioms ThomsonNine.RefinedRadius.tight_width
#print axioms ThomsonNine.RefinedRadius.exists_tight_root
#print axioms ThomsonNine.RefinedRadius.radius_mem_tight
#print axioms ThomsonNine.HermiteFactor.square_linear_dvd_of_eval_derivative_zero
#print axioms ThomsonNine.HermiteFactor.G_eval_zero
#print axioms ThomsonNine.HermiteFactor.G_derivative_eval_zero
#print axioms ThomsonNine.HermiteFactor.pairwise_coprime_square_linear
#print axioms ThomsonNine.HermiteFactor.product_square_linear_dvd
#print axioms ThomsonNine.HermiteFactor.exists_hermite_quotient
#print axioms ThomsonNine.HermiteFactor.minorant_of_G_nonneg
#print axioms ThomsonNine.HermiteFactor.minorant_of_factor
#print axioms ThomsonNine.HermiteInterpolation.basis_eval_self
#print axioms ThomsonNine.HermiteInterpolation.basis_eval_ne
#print axioms ThomsonNine.HermiteInterpolation.valueBasis_eval
#print axioms ThomsonNine.HermiteInterpolation.derivativeBasis_eval
#print axioms ThomsonNine.HermiteInterpolation.valueBasis_derivative_eval
#print axioms ThomsonNine.HermiteInterpolation.derivativeBasis_derivative_eval
#print axioms ThomsonNine.HermiteInterpolation.interpolate_eval
#print axioms ThomsonNine.HermiteInterpolation.interpolate_derivative_eval
#print axioms ThomsonNine.HermiteInterpolation.basis_natDegree
#print axioms ThomsonNine.HermiteInterpolation.valueBasis_natDegree
#print axioms ThomsonNine.HermiteInterpolation.derivativeBasis_natDegree
#print axioms ThomsonNine.HermiteInterpolation.interpolate_natDegree
#print axioms ThomsonNine.HermiteInterpolation.basis_derivative_at_node
#print axioms ThomsonNine.ActualHermite.computed_mem
#print axioms ThomsonNine.ActualHermite.node_bounds
#print axioms ThomsonNine.ActualHermite.node_mem
#print axioms ThomsonNine.ActualHermite.node_separated
#print axioms ThomsonNine.ActualHermite.node_strictMono
#print axioms ThomsonNine.ActualHermite.node_injective
#print axioms ThomsonNine.ActualHermite.node_upper_bounds
#print axioms ThomsonNine.ActualHermite.node_lt_one
#print axioms ThomsonNine.ActualHermite.H_eval
#print axioms ThomsonNine.ActualHermite.H_derivative_eval
#print axioms ThomsonNine.ActualHermite.value_square
#print axioms ThomsonNine.ActualHermite.H_natDegree
#print axioms ThomsonNine.ActualHermite.exists_quotient
#print axioms ThomsonNine.FixedInterval.mem_neg
#print axioms ThomsonNine.FixedInterval.mem_constant
#print axioms ThomsonNine.ListPolynomial.polynomial_zipAdd
#print axioms ThomsonNine.ListPolynomial.polynomial_map_mul
#print axioms ThomsonNine.ListPolynomial.polynomial_multiply
#print axioms ThomsonNine.ListPolynomial.polynomial_coeff
#print axioms ThomsonNine.ListPolynomial.rel_zipAdd
#print axioms ThomsonNine.ListPolynomial.mem_map_mul
#print axioms ThomsonNine.ListPolynomial.mem_multiply
#print axioms ThomsonNine.ListPolynomial.mem_coeff
#print axioms ThomsonNine.ListPolynomial.polynomial_sumCoefficients
#print axioms ThomsonNine.ListPolynomial.polynomial_productCoefficients
#print axioms ThomsonNine.ListPolynomial.rel_map
#print axioms ThomsonNine.ListPolynomial.mem_sumCoefficients
#print axioms ThomsonNine.ListPolynomial.mem_productCoefficients
#print axioms ThomsonNine.ListPolynomial.polynomial_map_neg
#print axioms ThomsonNine.ListPolynomial.mem_map_neg
#print axioms ThomsonNine.Interval.RatInterval.mem_inv_of_bounds

#print axioms ThomsonNine.ActualHermite.CoefficientData.unitScale_pos
#print axioms ThomsonNine.ActualHermite.CoefficientData.inverse_signs
#print axioms ThomsonNine.ActualHermite.CoefficientData.inverse_bounds
#print axioms ThomsonNine.ActualHermite.CoefficientData.inverse_mem
#print axioms ThomsonNine.ActualHermite.CoefficientData.sqrt_bounds
#print axioms ThomsonNine.ActualHermite.CoefficientData.sqrt_positive
#print axioms ThomsonNine.ActualHermite.CoefficientData.value_bounds
#print axioms ThomsonNine.ActualHermite.CoefficientData.value_mem
#print axioms ThomsonNine.ActualHermite.CoefficientData.node_fixed_bounds
#print axioms ThomsonNine.ActualHermite.CoefficientData.inverse_fixed_bounds
#print axioms ThomsonNine.ActualHermite.CoefficientData.value_fixed_bounds
#print axioms ThomsonNine.ActualHermite.CoefficientData.inputNode_mem
#print axioms ThomsonNine.ActualHermite.CoefficientData.inputInverse_mem
#print axioms ThomsonNine.ActualHermite.CoefficientData.inputValue_mem
#print axioms ThomsonNine.ActualHermite.Coefficients.others_ne
#print axioms ThomsonNine.ActualHermite.Coefficients.others_nodup
#print axioms ThomsonNine.ActualHermite.Coefficients.others_finset
#print axioms ThomsonNine.ActualHermite.Coefficients.linearBasis_polynomial
#print axioms ThomsonNine.ActualHermite.Coefficients.basis_polynomial
#print axioms ThomsonNine.ActualHermite.Coefficients.linearBasis_mem
#print axioms ThomsonNine.ActualHermite.Coefficients.basis_mem
#print axioms ThomsonNine.ActualHermite.Coefficients.slope_eq_derivative
#print axioms ThomsonNine.ActualHermite.Coefficients.slope_mem
#print axioms ThomsonNine.ActualHermite.Coefficients.subtract_mem
#print axioms ThomsonNine.ActualHermite.Coefficients.cube_mem
#print axioms ThomsonNine.ActualHermite.Coefficients.mid_mem
#print axioms ThomsonNine.ActualHermite.Coefficients.linear_mem
#print axioms ThomsonNine.ActualHermite.Coefficients.term_mem
#print axioms ThomsonNine.ActualHermite.Coefficients.term_polynomial
#print axioms ThomsonNine.ActualHermite.Coefficients.coefficients_mem
#print axioms ThomsonNine.ActualHermite.Coefficients.coefficients_polynomial
#print axioms ThomsonNine.ActualHermite.Coefficients.fixed_coefficient_mem
#print axioms ThomsonNine.ActualHermite.CertifiedCoefficients.computed_bounds
#print axioms ThomsonNine.ActualHermite.CertifiedCoefficients.H_coefficient_mem
#print axioms ThomsonNine.ActualHermite.QuotientStructure.factor
#print axioms ThomsonNine.ActualHermite.QuotientStructure.W_monic
#print axioms ThomsonNine.ActualHermite.QuotientStructure.W_natDegree
#print axioms ThomsonNine.ActualHermite.QuotientStructure.W_top_coefficient
#print axioms ThomsonNine.ActualHermite.QuotientStructure.G_natDegree
#print axioms ThomsonNine.ActualHermite.QuotientStructure.Q_natDegree
#print axioms ThomsonNine.ActualHermite.QuotientStructure.Q_coefficient_zero
#print axioms ThomsonNine.ActualHermite.QuotientStructure.monic_quotient_coefficient
#print axioms ThomsonNine.IntervalMonicSolve.realTail_lookup
#print axioms ThomsonNine.IntervalMonicSolve.tail_correction_lookup
#print axioms ThomsonNine.IntervalMonicSolve.lookup_mem
#print axioms ThomsonNine.IntervalMonicSolve.solveTail_mem
#print axioms ThomsonNine.IntervalMonicSolve.polynomial_realTail
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.linear_mem
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.square_mem
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.W_mem
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.square_polynomial
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.W_polynomial
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.G_mem
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.G_polynomial
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.w_mem
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.g_mem
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.Q_zero
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.Q_recurrence
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.Q_mem
#print axioms ThomsonNine.ActualHermite.QuotientCoefficients.fixed_coefficient_mem
#print axioms ThomsonNine.RationalListPolynomial.nil
#print axioms ThomsonNine.RationalListPolynomial.cons
#print axioms ThomsonNine.RationalListPolynomial.append
#print axioms ThomsonNine.RationalListPolynomial.zeroes
#print axioms ThomsonNine.RationalListPolynomial.unit_polynomial
#print axioms ThomsonNine.RationalListPolynomial.add
#print axioms ThomsonNine.RationalListPolynomial.scale
#print axioms ThomsonNine.RationalListPolynomial.mul
#print axioms ThomsonNine.RationalListPolynomial.pow
#print axioms ThomsonNine.RationalListPolynomial.basis_polynomial
#print axioms ThomsonNine.RationalListPolynomial.sum
#print axioms ThomsonNine.RationalListPolynomial.linearCombination_polynomial
#print axioms ThomsonNine.RationalListPolynomial.B_nonnegative
#print axioms ThomsonNine.ActualHermite.QuotientBernstein.matrix_identity
#print axioms ThomsonNine.ActualHermite.QuotientBernstein.monomial_identity
#print axioms ThomsonNine.ActualHermite.QuotientBernstein.matrixInput_bounds
#print axioms ThomsonNine.ActualHermite.QuotientBernstein.matrixInput_mem
#print axioms ThomsonNine.ActualHermite.QuotientBernstein.beta_mem
#print axioms ThomsonNine.ActualHermite.QuotientBernstein.betaInput_positive
#print axioms ThomsonNine.ActualHermite.QuotientBernstein.beta_positive
#print axioms ThomsonNine.ActualHermite.QuotientBernstein.Q_bernstein_representation
#print axioms ThomsonNine.ActualHermite.QuotientBernstein.Q_nonnegative
#print axioms ThomsonNine.ActualHermite.QuotientBernstein.H_minorant

#print axioms ThomsonNine.ActualKernel.N_mem_archive
#print axioms ThomsonNine.ActualKernel.Syzygy.p_annihilates_N
#print axioms ThomsonNine.ActualKernel.Syzygy.c_annihilates_N
#print axioms ThomsonNine.ActualKernel.Syzygy.A_p_zero
#print axioms ThomsonNine.ActualKernel.Syzygy.A_c_zero
#print axioms ThomsonNine.ActualKernel.feature_eq_sum
#print axioms ThomsonNine.ActualContact.SystemCertificate.selected_equations
#print axioms ThomsonNine.ActualContact.SystemCertificate.X_mem_archive
#print axioms ThomsonNine.CertificateMatrices.actual_reduced_psd
#print axioms ThomsonNine.CertificateMatrices.actual_A_psd
#print axioms ThomsonNine.CertificateMatrices.actual_A_mem
#print axioms ThomsonNine.CertificateMatrices.contact_energy_eq_family
#print axioms ThomsonNine.QPolynomial.eval_eq_Q3
#print axioms ThomsonNine.ActualF.F_eq_matrix_pairing
#print axioms ThomsonNine.ActualF.F_eq_contact_basis
#print axioms ThomsonNine.ActualF.Certified.actual_coefficient_mem
#print axioms ThomsonNine.ActualF.Refined.actual_coefficient_mem
#print axioms ThomsonNine.ActualF.Constants.actual_c_mem
#print axioms ThomsonNine.ActualF.Constants.actual_F111_mem
#print axioms ThomsonNine.ActualF.Constants.actual_familyEnergy_mem
#print axioms ThomsonNine.ActualR.Certified.family_mem
#print axioms ThomsonNine.ActualR.polynomial_eq_residual
#print axioms ThomsonNine.ActualR.source_function_eq
#print axioms ThomsonNine.ActualR.actual_source_h00_mem
#print axioms ThomsonNine.CandidateMoment.factor_identity
#print axioms ThomsonNine.CandidateMoment.constructed_weightedF_zero
#print axioms ThomsonNine.CandidateMoment.constructed_weightedF_stationary
#print axioms ThomsonNine.ActualContact.FJet_along
#print axioms ThomsonNine.ActualContact.weighted_polynomialContact
#print axioms ThomsonNine.ActualContact.CFG_equation
#print axioms ThomsonNine.ActualContact.CFG_residual_zero
#print axioms ThomsonNine.ActualContact.all_value_equations
#print axioms ThomsonNine.ActualContact.all_actual_contact_values
#print axioms ThomsonNine.ActualContact.polynomialContact_derivative
#print axioms ThomsonNine.ActualContact.actual_weightedGradient_zero
#print axioms ThomsonNine.ActualGlobal.actual_moment_nonnegative
#print axioms ThomsonNine.ActualGlobal.hermite_sum_le_energy
#print axioms ThomsonNine.ActualGlobal.energy_lower_bound
#print axioms ThomsonNine.ActualGlobal.frozen_claim_of_bounded_residual
#print axioms ThomsonNine.ActualContact.all_45_equations
#print axioms ThomsonNine.ActualLocal.all_twelve_residual_nonnegative
#print axioms ThomsonNine.ActualLocal.C00.actual_residual_nonnegative_on_source
#print axioms ThomsonNine.ActualLocal.C01.actual_residual_nonnegative_on_source
#print axioms ThomsonNine.ActualLocal.C02.actual_residual_nonnegative_on_source
#print axioms ThomsonNine.ActualLocal.C03.actual_residual_nonnegative_on_source
#print axioms ThomsonNine.ActualLocal.C04.actual_residual_nonnegative_on_source
#print axioms ThomsonNine.ActualLocal.C05.actual_residual_nonnegative_on_source
#print axioms ThomsonNine.ActualBoundary.C06.actual_residual_nonnegative
#print axioms ThomsonNine.ActualBoundary.C07.actual_residual_nonnegative
#print axioms ThomsonNine.ActualLocal.C08.actual_residual_nonnegative_on_source
#print axioms ThomsonNine.ActualBoundary.C09.actual_residual_nonnegative
#print axioms ThomsonNine.ActualLocal.C10.actual_residual_nonnegative_on_source
#print axioms ThomsonNine.ActualLocal.C11.actual_residual_nonnegative_on_source
#print axioms ThomsonNine.PackedMain.actual_axes_lower
#print axioms ThomsonNine.PackedMain.actual_root_frame
#print axioms ThomsonNine.PackedMain.actual_dominates
#print axioms ThomsonNine.PackedMain.actual_local_lower
#print axioms ThomsonNine.PackedMain.frozen_claim_of_ordered_residual
#print axioms ThomsonNine.PackedMain.claim_from_certified_frontier
#print axioms ThomsonNine.PackedMain.root_cut_checked
#print axioms ThomsonNine.thomsonNineClaim_proved
