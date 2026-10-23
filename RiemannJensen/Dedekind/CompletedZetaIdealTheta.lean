module

public import Mathlib
public import RiemannJensen.Dedekind.P2MUtil

/-!
# Ideal lattice theta functions

Poisson summation for positive definite Gaussians on `ℤ^n`, and the theta transformation
formula it gives for the theta function of an ideal lattice of a number field, with one or with
several scaling parameters. This is the first part of the proof that the completed Dedekind zeta
function continues analytically and satisfies its functional equation; the result is assembled in
`RiemannJensen.Dedekind.CompletedZetaPackageSource`.

## Main definitions

* `gapsw80_t1_completedDedekindZeta`: the completed Dedekind zeta function for `1 < re s`.
* `gapsw80_t4_multiIdealTheta`: the theta function of an ideal lattice with one scaling
  parameter at each infinite place.

## Main results

* `gapsw80_t2_rankNGaussianPoisson`: Poisson summation for a positive definite Gaussian on
  `ℤ^n`.
* `gapsw80_t4_multiIdealTheta_transformation`: the theta transformation formula of an ideal
  lattice.
-/

@[expose] public section

namespace P2MW.S_NumberField_exists_completedDedekindZeta_package

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Asymptotics

p2m_export "Asymptotics" "IsBigO IsBigO.of_bound isBigO_atTop_natCast_rpow_of_tendsto_div_rpow"
p2m_open "Asymptotics"

end Asymptotics

namespace Classical

p2m_export "Classical" "choose_spec em by_cases choose"
p2m_open "Classical"

end Classical

namespace Complex

p2m_export "Complex" "ofReal_sub log_exp one_re continuous_re measurable_ofReal add_conj one_cpow re sqrt norm_cpow_eq_rpow_re_of_pos re_ofNat ofReal_re add_re ofRealHom sqrt_one natCast_im ofReal_ne_zero lift norm_real intCast_im ofReal_tsum ofReal_prod real_smul one_im im_ofNat ofReal_inv ofReal_zpow cpow_ne_zero_iff re_le_norm Gammaℝ re_sum add_im ofReal_natCast norm_natCast ofReal_eq_one Gamma_nat_eq_factorial re_ofReal_mul ofReal_sum cpow_one Gamma_eq_integral ofReal_neg im hasSum_iff ofReal_intCast exp_sum Gamma_ne_zero normSq_eq_norm_sq ofReal_pow arg log_inv Gamma_ofReal hasSum_re I_sq ofReal_eq_zero normSq_apply Gamma rank_real_complex cpow_zero cpow_neg cpow_natCast exists mk.injEq ofReal ofReal_zero ofReal_mul exp_neg intCast_re im_sum neg_re sub_re inv_cpow I_re div_ofNat_re cpow_add continuous_exp coe_smul cpow_nat_mul' mul_cpow_ofReal_nonneg exp mk arg_ofReal_of_nonneg norm_exp pos_iff sub_im ofReal_add Gammaℝ_ne_zero_of_re_pos exp_zero measurable_exp ofReal_div cpow exp_log natCast_re cpow_intCast Gammaℂ ofReal_cpow continuous_ofReal cpow_neg_one log_zero I_im tsum_exp_neg_quadratic cpow_nat_mul ofReal_one mul_re im_ofReal_mul log_mul GammaIntegral ofReal_im log Gammaℝ_def ofReal_ofNat ofReal_exp div_re Gammaℂ_def ext I Gamma_add_one exp_nat_mul I_mul_I normSq_ofNat mul_im measurable_log hasDerivAt_log exp_add"
p2m_open "Complex"

end Complex

namespace ContinuousLinearMap

p2m_export "ContinuousLinearMap" "proj coe_mk zero_apply apply toLinearMap smulRight_apply comp add coe_proj zero det_pi coe_coe sub_apply mk.injEq restrict bound det snd one_apply mul_apply pi comp_apply sub smul_apply neg smulRight ext sum_apply coe_pi single inl neg_apply ring coe_smul add_apply proj_pi single_apply inr mul mk coe_comp"
p2m_open "ContinuousLinearMap"

end ContinuousLinearMap

namespace ENNReal

p2m_export "ENNReal" "ofReal_pow tsum_const ofReal_zero log_rpow ofReal_ofNat ofReal_add coe_smul ofReal_eq_one ofReal_ne_top ofReal_le_ofReal log_zero continuous_ofReal rpow_two log_inv toReal_mono summable_toReal coe_finset_sum ofReal_pos rpow_neg_one ofReal_mul smul_def continuous_sub_right one_le_rpow inv_rpow toReal_one one_ne_top add_left_inj toReal_prod rpow_le_rpow_of_exponent_ge mul_pos eq_div_iff zpow_pos ofReal_lt_top prod_lt_top log one_lt_two log_pow div_eq_zero_iff tsum_eq_add_tsum_ite measurable_ofReal ofReal_natCast exp_log continuous_exp rpow_le_rpow_of_exponent_le ofReal_prod_of_nonneg log_le_log rpow_one ofReal_tsum_of_nonneg rpow_natCast ofReal_sub measurable_log ofReal_eq_zero one_lt_top toReal_ofReal ofReal_one Icc_mem_nhds rpow_mul rpow_neg"
p2m_open "ENNReal"

end ENNReal

namespace FLT

namespace KwDyf2RealGammaLogBound

end FLT.KwDyf2RealGammaLogBound

namespace FLT

namespace KwDyf2XiEntireOrderDecomp

end FLT.KwDyf2XiEntireOrderDecomp

namespace FLT

namespace KwDyf2XiOrderBoundDecomp

end FLT.KwDyf2XiOrderBoundDecomp

namespace FLT

namespace KwDyf2XiStripBoundAttack

end FLT.KwDyf2XiStripBoundAttack

namespace FLT

namespace Gapsw48T2OdlyzkoDeg24PinCarrier

end FLT.Gapsw48T2OdlyzkoDeg24PinCarrier

namespace FLT

namespace Gapsw50T2ExplicitFormulaDecompositionPin

end FLT.Gapsw50T2ExplicitFormulaDecompositionPin

namespace FLT

namespace Gapsw52T2CarrierContentAtoms

end FLT.Gapsw52T2CarrierContentAtoms

namespace FLT

namespace Gapsw80T10DedekindZetaBridgeA1Discharge

end FLT.Gapsw80T10DedekindZetaBridgeA1Discharge

namespace FLT

namespace Gapsw80T11ExplicitFormulaA34Decomp

end FLT.Gapsw80T11ExplicitFormulaA34Decomp

namespace FLT

namespace Gapsw80T15XiOrderOneB1Decomp

end FLT.Gapsw80T15XiOrderOneB1Decomp

namespace FLT

namespace Gapsw80T16XiRightHalfBoundProof

end FLT.Gapsw80T16XiRightHalfBoundProof

namespace FLT

namespace Gapsw80T1OdlyzkoFoundationAtomDecomposition

end FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition

namespace FLT

namespace Gapsw80T21D2SubDecompWire

end FLT.Gapsw80T21D2SubDecompWire

namespace FLT

namespace Gapsw80T25B4pppStripSinglePointAbsorption

end FLT.Gapsw80T25B4pppStripSinglePointAbsorption

namespace FLT

namespace Gapsw80T2RankNGaussianPoisson

end FLT.Gapsw80T2RankNGaussianPoisson

namespace FLT

namespace Gapsw80T30D2d0cLocalEulerFactorProof

end FLT.Gapsw80T30D2d0cLocalEulerFactorProof

namespace FLT

namespace Gapsw80T31D1HadamardSubDecomp

end FLT.Gapsw80T31D1HadamardSubDecomp

namespace FLT

namespace Gapsw80T32D1aBoundaryCaseDecomp

end FLT.Gapsw80T32D1aBoundaryCaseDecomp

namespace FLT

namespace Gapsw80T35D1apa0ThreeFourOneIneqProof

end FLT.Gapsw80T35D1apa0ThreeFourOneIneqProof

namespace FLT

namespace Gapsw80T36D1appXiEndpointResidueProof

end FLT.Gapsw80T36D1appXiEndpointResidueProof

namespace FLT

namespace Gapsw80T37D1bGenericHadamardDecomp

end FLT.Gapsw80T37D1bGenericHadamardDecomp

namespace FLT

namespace Gapsw80T38D1b1CanonicalProductLogDerivProof

end FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof

namespace FLT

namespace Gapsw80T39D1b0HadamardQuotientDecomp

end FLT.Gapsw80T39D1b0HadamardQuotientDecomp

namespace FLT

namespace Gapsw80T3IdealLatticeThetaTransformation

end FLT.Gapsw80T3IdealLatticeThetaTransformation

namespace FLT

namespace Gapsw80T40D1b0bZeroFreeExpLinearProof

end FLT.Gapsw80T40D1b0bZeroFreeExpLinearProof

namespace FLT

namespace Gapsw80T41D1b0aHadamardFactorSubDecomp

end FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp

namespace FLT

namespace Gapsw80T42D1b0a0XiNonzeroInfZerosProof

end FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof

namespace FLT

namespace Gapsw80T4MultiVarIdealThetaTransformation

end FLT.Gapsw80T4MultiVarIdealThetaTransformation

namespace FLT

namespace Gapsw80T5HeckeThetaKernel

end FLT.Gapsw80T5HeckeThetaKernel

namespace FLT

namespace Gapsw80T6TraceDualBridge

end FLT.Gapsw80T6TraceDualBridge

namespace FLT

namespace Gapsw80T7ClosedFEWeakPair

end FLT.Gapsw80T7ClosedFEWeakPair

namespace FLT

namespace Gapsw80T8MellinGammaPartialZeta

end FLT.Gapsw80T8MellinGammaPartialZeta

namespace FLT

namespace Gapsw80T9ClassSumA1Closure

end FLT.Gapsw80T9ClassSumA1Closure

namespace Filter

p2m_export "Filter" "mem_bot ker mk pi Tendsto pi_mono atTop EventuallyEq.rfl eventually_gt_atTop eventually_of_mem unique mk.injEq EventuallyEq map eventually_ge_atTop Eventually.of_forall"
p2m_open "Filter"

end Filter

namespace FourierTransform

p2m_export "FourierTransform" "mk"
p2m_open "FourierTransform"

end FourierTransform

namespace Ideal

p2m_export "Ideal" "absNorm_span_singleton absNorm_eq_zero_iff pi mem_bot span prod Quotient.mk map span_singleton_eq_top absNorm_ne_zero_iff_mem_nonZeroDivisors ext absNorm Quotient.lift finite_setOf_absNorm_eq card_norm_le_eq_card_norm_le_add_one subset_span absNorm_ne_zero_of_nonZeroDivisors absNorm_eq_one_iff"
p2m_open "Ideal"

end Ideal

namespace InnerProductSpace

p2m_export "InnerProductSpace" "mk"
p2m_open "InnerProductSpace"

end InnerProductSpace

namespace Matrix

p2m_export "Matrix" "PosDef.diagonal vecMul_fromBlocks det_smul J stdBasis transpose_one diagonal_one reindex diagonal_eq_diagonal_iff invOf_eq_nonsing_inv ext diagonal_transpose add sub_apply vecMul_sub map_apply smul_mulVec det_diagonal det_reindex_self sub zero fromBlocks_apply₁₁ exp_neg fromBlocks_apply₂₂ conjTranspose_eq_transpose_of_trivial det_one repr fromBlocks₂₂Invertible one_mulVec gram dotProduct_mulVec fromBlocks_apply₁₂ det_fin_zero IsHermitian transpose_apply fromBlocks_mulVec gram_eq_conjTranspose_mul nonsing_inv_mul transpose_transpose comp submatrix_apply isUnit_iff_isUnit_det toBlocks₂₂ add_mulVec fromBlocks_apply₂₁ det_transpose neg det_apply fromBlocks rank smul inv_eq_right_inv mulVec_mulVec det_mul zero_apply of_apply posDef_gram_of_linearIndependent single det_fromBlocks₂₂ posDef_iff_dotProduct_mulVec isHermitian_fromBlocks_iff mulVec_diagonal mulVec_injective_of_isUnit mulVec_sub ext_iff diagonal_mul one_apply mulVec_transpose neg_apply smul_apply toBlocks₁₂ PosDef vecMul_transpose toBlocks₂₁ det neg_mulVec toBlocks₁₁ diagonal inv_reindex add_apply comp_apply of smul_mul sum_apply transpose_smul fromBlocks_toBlocks inv invertibleOfIsUnitDet zpow_add_one map mulVec_zero discr single_apply mul_apply unique transpose_sub trace invOf_fromBlocks₂₂_eq transpose_mul vecMul_vecMul mulVec_smul transpose_nonsing_inv diagonal_mul_diagonal reindex_apply mul_inv_rev mulVec add_vecMul"
p2m_open "Matrix"

end Matrix

namespace MeasureTheory

p2m_export "MeasureTheory" "HasFiniteIntegral Measure.quasiMeasurePreserving_snd Measure.restrict_apply_univ Measure.smul_absolutelyContinuous integrable_const volume_preserving_piUnique lintegral_image_eq_lintegral_abs_det_fderiv_mul Measure Measure.volume_eq_prod setIntegral_congr_fun continuousOn_of_dominated MeasurePreserving lintegral_comp hasFiniteIntegral_iff_enorm integral_sub lintegral_prod integral_nonneg lintegral_congr measure_preimage_add integral_tsum setIntegral_const measurePreserving_vadd withDensity_absolutelyContinuous IntegrableOn volume_pi lintegral_withDensity_eq_lintegral_mul norm_setIntegral_le_of_norm_le_const Measure.prod_restrict Measure.ext_of_lintegral Measure.pi Measure.pi_pi ae_restrict_mem integrableOn_const Measure.measurePreserving_neg Measure.map enorm_integral_le_lintegral_enorm setIntegral_prod IsAddFundamentalDomain covolume IsFiniteMeasure lintegral_mono HasFiniteIntegral.mono' setLIntegral_univ setLIntegral_congr_fun AEStronglyMeasurable.tsum lintegral_map integral_fintype_prod_eq_prod integral_smul_measure VAddInvariantMeasure measureReal_def lintegral_tsum MeasurePreserving.id setIntegral_mono_on norm_integral_le_integral_norm ae_restrict_of_forall_mem Integrable lintegral_mono_ae lintegral_smul_measure setLIntegral_prod Measure.restrict_univ integral_add integral_const_mul integral_map AEStronglyMeasurable ofReal_integral_eq_lintegral_ofReal volume_preserving_piEquivPiSubtypeProd lintegral_const_mul' integrable_const_iff Measure.restrict_pi_pi ae_of_all"
p2m_open "MeasureTheory"

end MeasureTheory

namespace Module

p2m_export "Module" "Basis.map_repr Basis.coe_span_apply Basis.mem_span_iff_repr_mem Basis.repr_reindex_apply Free.ChooseBasisIndex Basis.span finrank_eq_card_basis Basis.toMatrix_apply finrank Free mk Finite.of_injective Basis.equivFun_symm_apply Basis.det_apply Basis.map_apply Basis.coe_reindex finrank_pos finrank_eq_card_chooseBasisIndex Basis"
p2m_open "Module"

end Module

namespace Nat

p2m_export "Nat" "cast_nonneg cast_ne_zero log_pos floor_le lt_floor_add_one card_eq_fintype_card log_pow log sqrt_one le_floor div_pos one_lt_ofNat add_le_add succ sqrt_pos card_eq_zero coe_castRingHom cast_sum factorial_le choose cast_eq_zero cast_natAbs cast_sub card_ne_zero card_univ sqrt cast_injective sqrt_le_sqrt zero_le eq_zero_or_pos cast_pos cast_le ne_of_gt card_fin cast_ofNat castRingHom one_le_cast pred sub_le succ_le_succ one_le_iff_ne_zero card_congr pow_succ' factorial_le_pow zero mul_eq_zero cast_one factorial_pos dist_zero_right"
p2m_open "Nat"

end Nat

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"
p2m_open "NumberField"

end NumberField

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"

namespace InfinitePlace

p2m_export "NumberField.InfinitePlace" "nrRealPlaces mult_isReal embedding_of_isReal_apply IsReal IsComplex smul_apply mult_isComplex card_eq_nrRealPlaces_add_nrComplexPlaces not_isComplex_iff_isReal mult_pos mult mk embedding_of_isReal not_isReal_iff_isComplex ext nrComplexPlaces pos_iff isReal_or_isComplex apply prod_eq_prod_mul_prod card_add_two_mul_card_eq_rank embedding"
p2m_open "NumberField.InfinitePlace NumberField"

end NumberField.InfinitePlace

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"

namespace Units

p2m_export "NumberField.Units" "fundSystem pos_at_place rank regulator_pos torsionOrder equivFinRank exist_unique_eq_mul_prod mem_torsion torsion coe_coe regulator torsionOrder_pos"
p2m_open "NumberField.Units NumberField"

end NumberField.Units

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"

namespace Units

p2m_export "NumberField.Units" "fundSystem pos_at_place rank regulator_pos torsionOrder equivFinRank exist_unique_eq_mul_prod mem_torsion torsion coe_coe regulator torsionOrder_pos"

namespace dirichletUnitTheorem

p2m_export "NumberField.Units.dirichletUnitTheorem" "w₀ logSpace"
p2m_open "NumberField.Units.dirichletUnitTheorem NumberField.Units NumberField"

end NumberField.Units.dirichletUnitTheorem

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"

namespace mixedEmbedding

p2m_export "NumberField.mixedEmbedding" "indexEquiv mem_idealLattice covolume_idealLattice euclidean.toMixed index norm_real euclidean.stdOrthonormalBasis normAtAllPlaces indexEquiv_apply_isComplex_snd mixedEmbedding_apply_isComplex euclidean.stdOrthonormalBasis_map_eq volume_fundamentalDomain_stdBasis fundamentalCone idealLattice normAtPlace norm_eq_norm fractionalIdealLatticeBasis normAtPlace_nonneg stdBasis_apply_isReal mixedSpace mixedEmbedding_apply_isReal indexEquiv_apply_isReal euclidean.mixedSpace stdBasis unitSMul_smul indexEquiv_apply_isComplex_fst stdBasis_apply_isComplex_snd normAtPlace_apply fractionalIdealLatticeBasis_apply span_idealLatticeBasis normAtAllPlaces_apply normAtPlace_apply_of_isReal norm_smul stdBasis_apply_isComplex_fst realSpace normAtPlace_apply_of_isComplex"
p2m_open "NumberField.mixedEmbedding NumberField"

end NumberField.mixedEmbedding

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"

namespace mixedEmbedding

p2m_export "NumberField.mixedEmbedding" "indexEquiv mem_idealLattice covolume_idealLattice euclidean.toMixed index norm_real euclidean.stdOrthonormalBasis normAtAllPlaces indexEquiv_apply_isComplex_snd mixedEmbedding_apply_isComplex euclidean.stdOrthonormalBasis_map_eq volume_fundamentalDomain_stdBasis fundamentalCone idealLattice normAtPlace norm_eq_norm fractionalIdealLatticeBasis normAtPlace_nonneg stdBasis_apply_isReal mixedSpace mixedEmbedding_apply_isReal indexEquiv_apply_isReal euclidean.mixedSpace stdBasis unitSMul_smul indexEquiv_apply_isComplex_fst stdBasis_apply_isComplex_snd normAtPlace_apply fractionalIdealLatticeBasis_apply span_idealLatticeBasis normAtAllPlaces_apply normAtPlace_apply_of_isReal norm_smul stdBasis_apply_isComplex_fst realSpace normAtPlace_apply_of_isComplex"

namespace fundamentalCone

p2m_export "NumberField.mixedEmbedding.fundamentalCone" "prod_expMapBasis_pow expMapBasis_apply completeBasis_apply_of_ne expMap_target expMap_apply setLIntegral_expMapBasis_image expMapBasis_pos expMapBasis_apply' expMap equivFinRank completeBasis continuous_expMapBasis expMapBasis expMap_add"
p2m_open "NumberField.mixedEmbedding.fundamentalCone NumberField.mixedEmbedding NumberField"

end NumberField.mixedEmbedding.fundamentalCone

namespace Real

p2m_export "Real" "sqrt_pos log_le_sub_one_of_pos log_pos continuous_const_rpow norm volume_Ico norm_natCast log_nonneg exp_zero sqrt_le_sqrt rpow_mul pi_ne_zero pi_gt_three rpow_nonneg log_zero continuousOn_log log_exp measurable_exp sqrt_sq_eq_abs Gamma convexOn_log_Gamma log_inv two_le_pi Gamma_nat_eq_factorial exp_nat_mul exp_one_lt_d9 exp Gamma_ne_zero tendsto_log_atTop rpow_two exp_pos exp_le_exp sqrt_nonneg exp_nonneg measurable_log pi_nonneg rpow_le_rpow_of_exponent_le rpow_neg_one exp_sum rpow_neg log_rpow sqrt_one rpow_pos_of_pos rpow_natCast continuousAt_rpow_const continuous_exp log norm_of_nonneg norm_eq_abs exp_neg inv_rpow inner_apply mk pi_pos exp_log Gamma_eq_integral Gamma_add_one log_mul summable_abs_int_rpow rpow_one sq_sqrt log_le_log one_le_rpow mul_rpow rpow_le_rpow_of_exponent_ge hasDerivAt_log le_log_iff_exp_le add_one_le_exp exp_add sqrt_sq log_pow log_div sqrt"
p2m_open "Real"

end Real

namespace RealInnerProductSpace

p2m_open "RealInnerProductSpace"

end RealInnerProductSpace

namespace Set

p2m_export "Set" "eq_univ_of_forall exists_min_image restrict prod_pow indicator_apply univ_nonempty Icc diagonal Icc_succ_left_eq_Ioc mem_compl_iff ext univ_prod finite_singleton coe_eq_subtype mem_univ_pi pi Ioc unit card_singleton MapsTo mem_singleton_iff mem_univ pi_mono Ioi EqOn mem_Ici prod_insert mapsTo_univ Countable.isConnected_compl_of_one_lt_rank mem_singleton InjOn Ici mem_setOf_eq Ico_subset_Icc_self mem_insert_iff univ Ico mem_insert prod prod_empty range mem_Ioi mem_iInter"
p2m_open "Set"

end Set

namespace Topology

p2m_open "Topology"

end Topology

namespace WithLp

p2m_export "WithLp" "toLp ofLp"
p2m_open "WithLp"

end WithLp

section

p2m_open "Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology FourierTransform P2MW.S_NumberField_exists_completedDedekindZeta_package.FourierTransform RealInnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.RealInnerProductSpace ENNReal P2MW.S_NumberField_exists_completedDedekindZeta_package.ENNReal"

open _root_.Complex hiding exp

p2m_open "WithLp P2MW.S_NumberField_exists_completedDedekindZeta_package.WithLp"

noncomputable section

namespace FLT

namespace GaussianFourierPosDef

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-- For Euclidean vectors `x y : EuclideanSpace ℝ (Fin n)`, the dot product of their underlying
coordinate vectors equals the inner product `⟪x, y⟫`. -/
lemma dotProduct_ofLp_eq_inner (x y : EuclideanSpace ℝ (Fin n)) :
    ofLp x ⬝ᵥ ofLp y = ⟪x, y⟫ := by
  simp [dotProduct, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- For a positive definite `A` and a Hermitian `M` having the eigenvectors of `A`
(`hA.1.eigenvectorBasis`) as eigenvectors with eigenvalues `μ j`, the quadratic form `x ⬝ᵥ M *ᵥ x`
equals $\sum_i \mu_i c_i^2$, where `c_i` are the coordinates of `x` in that eigenvector basis. -/
lemma dotProduct_mulVec_eigen (hA : A.PosDef)
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) {μ : Fin n → ℝ}
    (hMb : ∀ j, M *ᵥ ofLp (hA.1.eigenvectorBasis j) = μ j • ofLp (hA.1.eigenvectorBasis j))
    (x : EuclideanSpace ℝ (Fin n)) :
    ofLp x ⬝ᵥ M *ᵥ ofLp x = ∑ i, μ i * (ofLp (hA.1.eigenvectorBasis.repr x) i) ^ 2 := by
  classical
  set bs := hA.1.eigenvectorBasis with hbs
  set w : EuclideanSpace ℝ (Fin n) := toLp 2 (M *ᵥ ofLp x) with hw
  have hcoe : ofLp w = M *ᵥ ofLp x := rfl
  have hMT : Mᵀ = M := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hM
  have h1 : ofLp x ⬝ᵥ M *ᵥ ofLp x = ⟪w, x⟫ := by
    rw [← dotProduct_ofLp_eq_inner, hcoe, dotProduct_comm]
  have h2 : ⟪w, x⟫ = ∑ i, ofLp (bs.repr w) i * ofLp (bs.repr x) i := by
    rw [← LinearIsometryEquiv.inner_map_map bs.repr w x, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h3 : ∀ i, ofLp (bs.repr w) i = μ i * ofLp (bs.repr x) i := by
    intro i
    have hr : ofLp (bs.repr w) i = ⟪bs i, w⟫ := bs.repr_apply_apply w i
    have hr' : ofLp (bs.repr x) i = ⟪bs i, x⟫ := bs.repr_apply_apply x i
    rw [hr, hr', ← dotProduct_ofLp_eq_inner, ← dotProduct_ofLp_eq_inner, hcoe,
      dotProduct_mulVec, ← Matrix.mulVec_transpose, hMT, hMb i, smul_dotProduct]
    rfl
  rw [h1, h2]
  exact Finset.sum_congr rfl fun i _ => by rw [h3 i]; ring

/-- For a positive definite `A`, the quadratic form `x ⬝ᵥ A *ᵥ x` equals $\sum_i \lambda_i c_i^2$,
where `λ_i` are the eigenvalues of `A` and `c_i` the coordinates of `x` in its eigenvector basis.
-/
lemma quadForm_eq_sum_eigen (hA : A.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    ofLp x ⬝ᵥ A *ᵥ ofLp x
      = ∑ i, hA.1.eigenvalues i * (ofLp (hA.1.eigenvectorBasis.repr x) i) ^ 2 :=
  dotProduct_mulVec_eigen hA hA.1 (hA.1.mulVec_eigenvectorBasis) x

section MainComputation

variable {t : ℝ}

end MainComputation

section SATInstances

end SATInstances

section Falsifier

end Falsifier

end FLT.GaussianFourierPosDef

end

end

section

namespace FLT

namespace Gapsw80T15XiOrderOneB1Decomp

open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp

/-- If `2 ≤ ‖s‖` for a complex number `s`, then `s ≠ 0` and `s ≠ 1`. -/
theorem gapsw80_t15_norm_ge_two_ne_zero_one {s : ℂ} (hs : 2 ≤ ‖s‖) :
    s ≠ 0 ∧ s ≠ 1 := by
  constructor <;> rintro rfl <;> norm_num at hs

/-- For every complex `s` with `2 ≤ ‖s‖`, one has $\log\|s(s-1)\| \le 2\|s\|\log\|s\|$. -/
theorem gapsw80_t15_sat_polynomialFactor_orderBound :
    ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖s * (s - 1)‖ ≤ 2 * ‖s‖ * Real.log ‖s‖ := by
  intro s hs
  obtain ⟨h0, h1⟩ := gapsw80_t15_norm_ge_two_ne_zero_one hs
  have hns : (0:ℝ) < ‖s‖ := lt_of_lt_of_le (by norm_num) hs
  have hprod_pos : (0:ℝ) < ‖s * (s - 1)‖ := by
    rw [norm_mul]
    exact mul_pos (norm_pos_iff.mpr h0) (norm_pos_iff.mpr (sub_ne_zero.mpr h1))
  have hub : ‖s * (s - 1)‖ ≤ 2 * ‖s‖ ^ 2 := by
    rw [norm_mul, sq]
    have hs1 : ‖s - 1‖ ≤ 2 * ‖s‖ := by linarith [norm_sub_le s 1, norm_one (α := ℂ)]
    nlinarith [norm_nonneg s]
  have hlog1 : Real.log ‖s * (s - 1)‖ ≤ Real.log (2 * ‖s‖ ^ 2) :=
    Real.log_le_log hprod_pos hub
  have hlog2 : Real.log (2 * ‖s‖ ^ 2) = Real.log 2 + 2 * Real.log ‖s‖ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring

  have hlogs : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hs
  have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : Real.log 2 + 2 * Real.log ‖s‖ ≤ 2 * ‖s‖ * Real.log ‖s‖ := by
    have hprod : (1:ℝ) * Real.log 2 ≤ (‖s‖ - 1) * Real.log ‖s‖ :=
      mul_le_mul (by linarith) hlogs hlog2_pos.le (by linarith)
    nlinarith [hprod]
  linarith

end FLT.Gapsw80T15XiOrderOneB1Decomp

end

section

namespace FLT

namespace Gapsw80T1OdlyzkoFoundationAtomDecomposition

open FLT.Gapsw48T2OdlyzkoDeg24PinCarrier
open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex"

/-- The completed Dedekind zeta function of a number field `K`, equal to
$|\Delta_K|^{s/2}\,\Gamma_{\mathbb R}(s)^{r_1}\,\Gamma_{\mathbb C}(s)^{r_2}\,\zeta_K(s)$ where
`r₁`, `r₂` are the numbers of real and complex places and `Δ_K` is the discriminant. -/
noncomputable def gapsw80_t1_completedDedekindZeta
    (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((|discr K| : ℤ) : ℂ)) ^ (s / 2)
    * Gammaℝ s ^ nrRealPlaces K
    * Gammaℂ s ^ nrComplexPlaces K
    * dedekindZeta K s

/-- The proposition that for every number field `K` there is a function `Λ : ℂ → ℂ`, differentiable
away from `0` and `1`, agreeing with `gapsw80_t1_completedDedekindZeta K s` for `1 < s.re` and
satisfying `Λ (1 - s) = Λ s` for all `s`. -/
def gapsw80_t1_DedekindCompletedFE : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ Λ : ℂ → ℂ,
      DifferentiableOn ℂ Λ {(0 : ℂ), 1}ᶜ ∧
      (∀ s : ℂ, 1 < s.re → Λ s = gapsw80_t1_completedDedekindZeta K s) ∧
      (∀ s : ℂ, Λ (1 - s) = Λ s)

end FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition

end

section

noncomputable section

namespace FLT

namespace Gapsw80T3IdealLatticeThetaTransformation

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T2RankNGaussianPoisson Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

/-- The degree `[K : ℚ]` of the number field `K`, as the `ℚ`-dimension of `K`. -/
abbrev nK := finrank ℚ K

/-- An equivalence between the index type `index K` of the standard basis of the mixed space of `K`
and `Fin (nK K)`. -/
def eIdx : index K ≃ Fin (nK K) :=
  Fintype.equivFinOfCardEq (by
    rw [← Module.finrank_eq_card_basis (stdBasis K), mixedEmbedding.finrank])

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- An equivalence between the index type of a chosen `ℤ`-basis of the fractional ideal `I` and
`Fin (nK K)`. -/
def eI : Free.ChooseBasisIndex ℤ (I : FractionalIdeal (𝓞 K)⁰ K) ≃ Fin (nK K) :=
  Fintype.equivFinOfCardEq (by
    rw [← Module.finrank_eq_card_chooseBasisIndex, fractionalIdeal_rank, RingOfIntegers.rank])

/-- The `i`-th vector of the `ℤ`-basis of the ideal lattice of `I`, indexed by `Fin (nK K)` and
viewed in the Euclidean version of the mixed space of `K`. -/
def latE (i : Fin (nK K)) : euclidean.mixedSpace K :=
  (euclidean.toMixed K).symm (fractionalIdealLatticeBasis K I ((eI K I).symm i))

/-- The vectors `latE K I i` (`i : Fin (nK K)`) are linearly independent over `ℝ`. -/
theorem latE_linearIndependent : LinearIndependent ℝ (latE K I) :=
  ((fractionalIdealLatticeBasis K I).linearIndependent.map'
    (euclidean.toMixed K).symm.toLinearMap (LinearEquiv.ker _)).comp _ (eI K I).symm.injective

/-- The `ℤ`-basis vectors `fractionalIdealLatticeBasis K I` of the ideal lattice are linearly
independent over `ℤ`. -/
theorem fILB_linearIndependent_int :
    LinearIndependent ℤ (⇑(fractionalIdealLatticeBasis K I)) :=
  (fractionalIdealLatticeBasis K I).linearIndependent.restrict_scalars
    (by simpa only [zsmul_one] using Int.cast_injective)

/-- The `ℤ`-basis of the ideal lattice `mixedEmbedding.idealLattice K I`, indexed by `Fin (nK K)`,
obtained by reindexing the lattice basis of `I`. -/
def idealZBasis : Basis (Fin (nK K)) ℤ (mixedEmbedding.idealLattice K I) :=
  ((Basis.span (fILB_linearIndependent_int K I)).map
      (LinearEquiv.ofEq _ _ (span_idealLatticeBasis K I))).reindex (eI K I)

/-- The `i`-th vector of `idealZBasis K I`, viewed in `mixedSpace K`, equals
`fractionalIdealLatticeBasis K I ((eI K I).symm i)`. -/
@[scoped simp]
theorem idealZBasis_apply (i : Fin (nK K)) :
    (idealZBasis K I i : mixedSpace K)
      = fractionalIdealLatticeBasis K I ((eI K I).symm i) := by
  have h : ((Basis.span (fILB_linearIndependent_int K I)) ((eI K I).symm i) : mixedSpace K)
      = fractionalIdealLatticeBasis K I ((eI K I).symm i) :=
    Basis.coe_span_apply _ _
  simp only [idealZBasis, Basis.coe_reindex, Function.comp_apply, Basis.map_apply]
  exact h

/-- The Gram matrix over `ℝ` of the basis vectors `latE K I`, whose `(i, j)` entry is the inner
product of `latE K I i` and `latE K I j`. -/
def gapsw80_t3_idealGram : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.gram ℝ (latE K I)

/-- The Gram matrix `gapsw80_t3_idealGram K I` of the ideal lattice basis is positive definite. -/
theorem gapsw80_t3_idealGram_posDef : (gapsw80_t3_idealGram K I).PosDef :=
  Matrix.posDef_gram_of_linearIndependent (latE_linearIndependent K I)

/-- The standard orthonormal basis of the Euclidean mixed space of `K`, indexed by `Fin (nK K)`. -/
def stdONBFin : OrthonormalBasis (Fin (nK K)) ℝ (euclidean.mixedSpace K) :=
  (euclidean.stdOrthonormalBasis K).reindex (eIdx K)

/-- The standard `ℝ`-basis of the mixed space of `K`, indexed by `Fin (nK K)`. -/
def stdBasisFin : Basis (Fin (nK K)) ℝ (mixedSpace K) :=
  (mixedEmbedding.stdBasis K).reindex (eIdx K)

/-- The `i`-th coordinate of `x` in `stdBasisFin K` equals the `i`-th coordinate of its image under
`(euclidean.toMixed K).symm` in `stdONBFin K`. -/
theorem stdBasisFin_repr_eq (x : mixedSpace K) (i : Fin (nK K)) :
    (stdBasisFin K).repr x i
      = (stdONBFin K).repr ((euclidean.toMixed K).symm x) i := by
  simp only [stdBasisFin, stdONBFin, Basis.repr_reindex_apply,
    OrthonormalBasis.repr_reindex, ← euclidean.stdOrthonormalBasis_map_eq K,
    Basis.map_repr, LinearEquiv.trans_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  rfl

/-- The real `nK K × nK K` matrix whose `(i, j)` entry is the `i`-th coordinate, in the standard
orthonormal basis, of the basis vector `latE K I j`. -/
def coordMatrix : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.of fun i j => (stdONBFin K).repr (latE K I j) i

/-- The Gram matrix of the ideal lattice basis equals `(coordMatrix K I)ᵀ * coordMatrix K I`. -/
theorem gapsw80_t3_idealGram_eq_transpose_mul :
    gapsw80_t3_idealGram K I = (coordMatrix K I)ᵀ * (coordMatrix K I) := by
  have h := Matrix.gram_eq_conjTranspose_mul (stdONBFin K) (latE K I)
  simpa only [gapsw80_t3_idealGram, coordMatrix, Matrix.conjTranspose_eq_transpose_of_trivial]
    using h

/-- `coordMatrix K I` equals the matrix of the `ℤ`-basis vectors of the ideal lattice, written in
the basis `stdBasisFin K`. -/
theorem coordMatrix_eq_toMatrix :
    coordMatrix K I = (stdBasisFin K).toMatrix (fun i => ↑(idealZBasis K I i)) := by
  ext i j
  rw [coordMatrix, Matrix.of_apply, Basis.toMatrix_apply, idealZBasis_apply,
    stdBasisFin_repr_eq]
  rfl

/-- The fundamental domain of `stdBasisFin K` in the mixed space has real volume `1`. -/
theorem volume_fundamentalDomain_stdBasisFin :
    MeasureTheory.volume.real (ZSpan.fundamentalDomain (stdBasisFin K)) = 1 := by
  rw [stdBasisFin, ZSpan.fundamentalDomain_reindex, MeasureTheory.measureReal_def,
    volume_fundamentalDomain_stdBasis, ENNReal.toReal_one]

/-- The absolute value of `(coordMatrix K I).det` equals the covolume of the ideal lattice
`mixedEmbedding.idealLattice K I`. -/
theorem abs_det_coordMatrix :
    |(coordMatrix K I).det| = ZLattice.covolume (mixedEmbedding.idealLattice K I) := by
  have h := ZLattice.covolume_eq_det_mul_measureReal
    (b := idealZBasis K I) (b₀ := stdBasisFin K)
  rw [volume_fundamentalDomain_stdBasisFin, mul_one] at h
  rw [coordMatrix_eq_toMatrix, ← Basis.det_apply]
  exact h.symm

/-- The `ℤ`-linear equivalence from `Fin (nK K) → ℤ` onto the ideal lattice
`mixedEmbedding.idealLattice K I` sending a coordinate vector to the corresponding combination of
the `ℤ`-basis `idealZBasis K I`. -/
def zEquiv : (Fin (nK K) → ℤ) ≃ₗ[ℤ] mixedEmbedding.idealLattice K I :=
  (idealZBasis K I).equivFun.symm

/-- For `v : Fin (nK K) → ℤ`, the image `zEquiv K I v` in `mixedSpace K` equals $\sum_i v_i\,b_i$
where `b_i = fractionalIdealLatticeBasis K I ((eI K I).symm i)`. -/
theorem coe_zEquiv_apply (v : Fin (nK K) → ℤ) :
    (zEquiv K I v : mixedSpace K)
      = ∑ i, (v i : ℝ) • fractionalIdealLatticeBasis K I ((eI K I).symm i) := by
  calc (zEquiv K I v : mixedSpace K)
      = ((∑ i, v i • idealZBasis K I i : idealLattice K I) : mixedSpace K) := by
        rw [zEquiv, (idealZBasis K I).equivFun_symm_apply v]
    _ = ∑ i, v i • (idealZBasis K I i : mixedSpace K) := by push_cast; ring_nf
    _ = ∑ i, (v i : ℝ) • fractionalIdealLatticeBasis K I ((eI K I).symm i) :=
        Finset.sum_congr rfl fun i _ => by
          rw [idealZBasis_apply, ← Int.cast_smul_eq_zsmul ℝ]

section Census

end Census

end FLT.Gapsw80T3IdealLatticeThetaTransformation

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

section

p2m_open "Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix"
p2m_open_scoped "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix"

namespace FLT

namespace Gapsw80T2RankNGaussianPoisson

noncomputable section

variable {n : ℕ}

/-- The coordinatewise cast of an integer vector `v : Fin n → ℤ` to a real vector `Fin n → ℝ`. -/
abbrev zcastR (v : Fin n → ℤ) : Fin n → ℝ := fun i => (v i : ℝ)

/-- The real quadratic form `v ⬝ᵥ (A *ᵥ v)` of a real matrix `A` evaluated at `v : Fin n → ℝ`. -/
abbrev rQuad (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ := v ⬝ᵥ (A *ᵥ v)

/-- The complex bilinear quadratic form `v ⬝ᵥ (A *ᵥ v)` of a complex matrix `A` evaluated at
`v : Fin n → ℂ`. -/
abbrev cQuad (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℂ := v ⬝ᵥ (A *ᵥ v)

/-- The entrywise coercion of a real `n × n` matrix `A` to a complex matrix. -/
abbrev liftC (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  A.map ((↑) : ℝ → ℂ)

/-- The term of the theta series indexed by `v : Fin n → ℤ`, namely
$\exp(-\pi t\, v^{T}Av + 2\pi \sum_i b_i v_i)$. -/
def thetaTerm (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (b : Fin n → ℂ)
    (v : Fin n → ℤ) : ℂ :=
  cexp (-(π : ℂ) * (t : ℂ) * (rQuad A (zcastR v) : ℂ) + 2 * π * ∑ i, b i * (v i : ℂ))

/-- The term of the dual theta series indexed by `w : Fin n → ℤ`, namely
$\exp\!\big(-\tfrac{\pi}{t}\,(w+ib)^{T}A^{-1}(w+ib)\big)$. -/
def dualTerm (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (b : Fin n → ℂ)
    (w : Fin n → ℤ) : ℂ :=
  cexp (-(π : ℂ) / (t : ℂ) *
    cQuad (liftC A⁻¹) (fun i => (w i : ℂ) + Complex.I * b i))

/-- The Poisson summation identity for the Gaussian of `A`: $\sum_v$ `thetaTerm A t b v` equals
$(t^n\det A)^{-1/2}\sum_w$ `dualTerm A t b w`. -/
def PoissonLaw (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (b : Fin n → ℂ) : Prop :=
  (∑' v, thetaTerm A t b v)
    = (((t ^ n * A.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) * ∑' w, dualTerm A t b w

section Summability

/-- For a positive definite real matrix `A`, there is `c > 0` such that `c * (x ⬝ᵥ x) ≤ rQuad A x`
for all `x : Fin n → ℝ`. -/
theorem gapsw80_t2_posDef_quadForm_lower {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, c * (x ⬝ᵥ x) ≤ rQuad A x := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hE | hNE
  · exact ⟨1, one_pos, fun x => by simp [rQuad, dotProduct]⟩
  obtain ⟨i₀, hmin⟩ := Finite.exists_min hA.1.eigenvalues
  refine ⟨hA.1.eigenvalues i₀, hA.eigenvalues_pos i₀, fun x => ?_⟩
  have hquad :=
    FLT.GaussianFourierPosDef.quadForm_eq_sum_eigen hA (WithLp.toLp 2 x)
  have hxx : x ⬝ᵥ x
      = ∑ i, (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 := by
    have h1 : x ⬝ᵥ x = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 x) :=
      FLT.GaussianFourierPosDef.dotProduct_ofLp_eq_inner
        (WithLp.toLp 2 x) (WithLp.toLp 2 x)
    have h2 := (hA.1.eigenvectorBasis.repr.inner_map_map
      (WithLp.toLp 2 x) (WithLp.toLp 2 x)).symm
    have h3 := (FLT.GaussianFourierPosDef.dotProduct_ofLp_eq_inner
      (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x))
      (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x))).symm
    rw [h1, h2, h3]; simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  calc hA.1.eigenvalues i₀ * (x ⬝ᵥ x)
      = ∑ i, hA.1.eigenvalues i₀ *
          (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 := by
        rw [hxx, Finset.mul_sum]
    _ ≤ ∑ i, hA.1.eigenvalues i *
          (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg _)
    _ = rQuad A x := hquad.symm

/-- For `a > 0` and `b : ℂ`, the series over `k : ℤ` of $\|\exp(-\pi a k^2 + 2\pi b k)\|$ is
summable. -/
lemma gapsw80_t2_summable_1D {a : ℝ} (ha : 0 < a) (b : ℂ) :
    Summable fun k : ℤ =>
      ‖cexp (-(π : ℂ) * (a : ℂ) * (k : ℂ) ^ 2 + 2 * π * b * (k : ℂ))‖ := by
  have hre : (-(π : ℂ) * (a : ℂ)).re < 0 := by
    simp only [neg_mul, neg_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    exact neg_neg_of_pos (mul_pos pi_pos ha)
  have hO := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact hre (2 * π * b)
    (-2)).isBigO.comp_tendsto Int.tendsto_coe_cofinite
  simp only [Function.comp_def, Complex.ofReal_intCast] at hO
  exact (summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) hO).norm

/-- If each `f i : ℤ → ℝ` is nonnegative and summable, then `v ↦ ∏ i, f i (v i)` is summable over
`v : Fin n → ℤ`. -/
lemma gapsw80_t2_summable_prod_fin :
    ∀ {n : ℕ} {f : Fin n → ℤ → ℝ}, (∀ i k, 0 ≤ f i k) → (∀ i, Summable (f i)) →
      Summable fun v : Fin n → ℤ => ∏ i, f i (v i) := by
  intro n
  induction n with
  | zero =>
    intro f _ _
    have hU : Subsingleton (Fin 0 → ℤ) := inferInstance
    refine ⟨1, ?_⟩
    have hconst : (fun v : Fin 0 → ℤ => ∏ i, f i (v i)) = fun _ => 1 := by
      funext v; exact Finset.prod_empty
    rw [hconst]
    simp
  | succ m IH =>
    intro f hpos hsum
    set e : (Fin (m + 1) → ℤ) ≃ (Fin m → ℤ) × ℤ :=
      { toFun := fun v => ⟨v ∘ Fin.castSucc, v (Fin.last m)⟩
        invFun := fun p => Fin.snoc p.1 p.2
        left_inv := fun v => by
          funext i; dsimp only
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last]
        right_inv := fun p => by
          ext
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last] }
    have hIH : Summable fun v : Fin m → ℤ => ∏ i, f (Fin.castSucc i) (v i) :=
      IH (fun i k => hpos _ k) fun i => hsum _
    have hprod :
        Summable fun p : (Fin m → ℤ) × ℤ =>
          (∏ i, f (Fin.castSucc i) (p.1 i)) * f (Fin.last m) p.2 :=
      hIH.mul_of_nonneg (hsum _) (fun v => Finset.prod_nonneg fun i _ => hpos _ _)
        (fun k => hpos _ k)
    have hprod' :
        Summable fun p : (Fin m → ℤ) × ℤ =>
          ∏ i, f i ((Fin.snoc p.1 p.2 : Fin (m + 1) → ℤ) i) := by
      refine hprod.congr fun p => ?_
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact e.symm.summable_iff.mp hprod'

/-- For `a > 0` and real `r`, the function `k ↦ exp(-(a k^2) + r k)` is summable over `k : ℤ`. -/
lemma gapsw80_t2_summable_1D_real {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Summable fun k : ℤ => rexp (-(a * (k : ℝ) ^ 2) + r * (k : ℝ)) := by
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  have h := gapsw80_t2_summable_1D (a := a / π) (div_pos ha pi_pos)
    (((r / (2 * π)) : ℝ) : ℂ)
  refine h.congr fun k => ?_
  have heq : (-(π : ℂ) * ((a / π : ℝ) : ℂ) * (k : ℂ) ^ 2
        + 2 * π * (((r / (2 * π)) : ℝ) : ℂ) * (k : ℂ))
      = (((-(a * (k : ℝ) ^ 2) + r * (k : ℝ)) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [heq, Complex.norm_exp, Complex.ofReal_re]

/-- For `c > 0`, the function `v ↦ exp(-(c * ∑ i, (v i)^2))` is summable over `v : Fin n → ℤ`. -/
lemma gapsw80_t2_summable_gaussian_Zn {c : ℝ} (hc : 0 < c) :
    Summable fun v : Fin n → ℤ => rexp (-(c * ∑ i, (v i : ℝ) ^ 2)) := by
  have hrew : (fun v : Fin n → ℤ => rexp (-(c * ∑ i, (v i : ℝ) ^ 2)))
      = fun v => ∏ i, rexp (-(c * (v i : ℝ) ^ 2)) := by
    funext v; rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hrew]
  exact gapsw80_t2_summable_prod_fin (n := n)
    (f := fun _ k => rexp (-(c * (k : ℝ) ^ 2)))
    (fun _ _ => (Real.exp_pos _).le)
    (fun _ => (gapsw80_t2_summable_1D_real hc 0).congr fun k => by
      rw [zero_mul, add_zero])

/-- For real `A` and `z : Fin n → ℂ`, the real part of `cQuad (liftC A) z` equals
`rQuad A (Re z) - rQuad A (Im z)`. -/
lemma gapsw80_t2_re_cQuad_liftC (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) :
    (cQuad (liftC A) z).re
      = rQuad A (fun i => (z i).re) - rQuad A (fun i => (z i).im) := by
  have hmv : ∀ i, ((liftC A) *ᵥ z) i = ∑ j, (A i j : ℂ) * z j := fun i => by
    simp only [Matrix.mulVec, dotProduct, liftC, Matrix.map_apply]
  have hmvR : ∀ (x : Fin n → ℝ) i, (A *ᵥ x) i = ∑ j, A i j * x j := fun x i => by
    simp only [Matrix.mulVec, dotProduct]
  unfold cQuad rQuad
  simp only [dotProduct, hmv, hmvR]
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_re, Complex.re_sum, Complex.im_sum]
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]

/-- For a positive definite `A` and `0 < t`, the family `‖thetaTerm A t b v‖` is summable over
`v : Fin n → ℤ`. -/
theorem gapsw80_t2_summable_thetaTerm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {t : ℝ} (ht : 0 < t) (b : Fin n → ℂ) :
    Summable fun v : Fin n → ℤ => ‖thetaTerm A t b v‖ := by
  obtain ⟨c, hc, hQ⟩ := gapsw80_t2_posDef_quadForm_lower hA
  have hxx : ∀ v : Fin n → ℤ, zcastR v ⬝ᵥ zcastR v = ∑ i, (v i : ℝ) ^ 2 := fun v => by
    simp only [dotProduct, zcastR]; exact Finset.sum_congr rfl fun i _ => (sq _).symm
  set g : Fin n → ℤ → ℝ := fun i k =>
    rexp (-(π * t * c * (k : ℝ) ^ 2) + 2 * π * (b i).re * (k : ℝ))
  have hmajor : Summable fun v : Fin n → ℤ => ∏ i, g i (v i) :=
    gapsw80_t2_summable_prod_fin (n := n) (f := g)
      (fun _ _ => (Real.exp_pos _).le)
      (fun i => (gapsw80_t2_summable_1D_real (a := π * t * c) (by positivity)
          (2 * π * (b i).re)).congr
        fun k => by unfold g; ring_nf)
  refine hmajor.of_nonneg_of_le (fun v => norm_nonneg _) fun v => ?_
  unfold thetaTerm
  rw [Complex.norm_exp]
  have hre : (-(π : ℂ) * (t : ℂ) * (rQuad A (zcastR v) : ℂ)
        + 2 * π * ∑ i, b i * (v i : ℂ)).re
      = -(π * t * rQuad A (zcastR v)) + 2 * π * ∑ i, (b i).re * (v i : ℝ) := by
    have h1 : -(π : ℂ) * (t : ℂ) * (rQuad A (zcastR v) : ℂ)
        = (((-(π * t * rQuad A (zcastR v))) : ℝ) : ℂ) := by push_cast; ring
    have h2 : (2 : ℂ) * (π : ℂ) = (((2 * π) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
      Complex.re_sum]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by
      simp [Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
  rw [hre, show (∏ i, g i (v i)) = rexp (∑ i,
      (-(π * t * c * (v i : ℝ) ^ 2) + 2 * π * (b i).re * (v i : ℝ))) from
    (Real.exp_sum _ _).symm]
  apply Real.exp_le_exp.mpr
  have hQv := hQ (zcastR v); rw [hxx v] at hQv
  have hsplit : (∑ i, (-(π * t * c * (v i : ℝ) ^ 2) + 2 * π * (b i).re * (v i : ℝ)))
      = -(π * t) * (c * ∑ i, (v i : ℝ) ^ 2)
        + (2 * π) * ∑ i, (b i).re * (v i : ℝ) := by
    rw [Finset.sum_add_distrib]; congr 1
    · rw [← mul_assoc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  nlinarith [mul_pos pi_pos ht]

/-- For a positive definite `A` and `0 < t`, the family `‖dualTerm A t b w‖` is summable over
`w : Fin n → ℤ`. -/
theorem gapsw80_t2_summable_dualTerm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {t : ℝ} (ht : 0 < t) (b : Fin n → ℂ) :
    Summable fun w : Fin n → ℤ => ‖dualTerm A t b w‖ := by
  obtain ⟨c, hc, hQ⟩ := gapsw80_t2_posDef_quadForm_lower hA.inv
  set d : Fin n → ℝ := fun i => (b i).im
  set C₁ : ℝ := rexp (π / t * rQuad A⁻¹ (fun i => (b i).re))
  have hC₁ : 0 ≤ C₁ := (Real.exp_pos _).le

  have hconst : ∀ w : Fin n → ℤ,
      ‖dualTerm A t b w‖
        = C₁ * rexp (-(π / t) * rQuad A⁻¹ (fun i => (w i : ℝ) - d i)) := by
    intro w
    unfold dualTerm
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    have hcoef : -(π : ℂ) / (t : ℂ) = (((-(π / t)) : ℝ) : ℂ) := by push_cast; ring
    rw [hcoef, Complex.re_ofReal_mul, gapsw80_t2_re_cQuad_liftC]
    have hre : (fun i => ((w i : ℂ) + Complex.I * b i).re)
        = fun i => (w i : ℝ) - d i := by
      funext i; simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, d]; ring
    have him : (fun i => ((w i : ℂ) + Complex.I * b i).im)
        = fun i => (b i).re := by
      funext i; simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [hre, him]; ring

  set g : Fin n → ℤ → ℝ := fun i k => rexp (-(π * c / t) * ((k : ℝ) - d i) ^ 2)
  have hg_sum : ∀ i, Summable (g i) := fun i => by
    refine ((gapsw80_t2_summable_1D_real (a := π * c / t) (by positivity)
        (2 * (π * c / t) * d i)).mul_left (rexp (-(π * c / t) * (d i) ^ 2))).congr
      fun k => ?_
    unfold g; rw [← Real.exp_add]; ring_nf
  have hmajor : Summable fun w : Fin n → ℤ => ∏ i, g i (w i) :=
    gapsw80_t2_summable_prod_fin (n := n) (f := g)
      (fun _ _ => (Real.exp_pos _).le) hg_sum
  refine (hmajor.mul_left C₁).of_nonneg_of_le (fun w => norm_nonneg _) fun w => ?_
  rw [hconst w]
  refine mul_le_mul_of_nonneg_left ?_ hC₁
  rw [show (∏ i, g i (w i))
      = rexp (∑ i, -(π * c / t) * ((w i : ℝ) - d i) ^ 2) from (Real.exp_sum _ _).symm]
  apply Real.exp_le_exp.mpr
  have hQw := hQ (fun i => (w i : ℝ) - d i)
  have hdot : (fun i => (w i : ℝ) - d i) ⬝ᵥ (fun i => (w i : ℝ) - d i)
      = ∑ i, ((w i : ℝ) - d i) ^ 2 := by
    simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => (sq _).symm
  rw [hdot] at hQw
  rw [← Finset.mul_sum, show -(π * c / t) = -(π / t) * c by ring, mul_assoc]
  have hnp : -(π / t) ≤ 0 := neg_nonpos_of_nonneg (div_pos pi_pos ht).le
  exact mul_le_mul_of_nonpos_left hQw hnp

end Summability

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

section BilinearSchur

variable {R : Type*} [CommRing R] {m k : ℕ}

/-- For a symmetric invertible block `D`, the quadratic form of the block matrix
`fromBlocks P q qᵀ D` at `Sum.elim x y` (written with `ᵥ*`) equals
`(D⁻¹qᵀx + y)ᵀ D (D⁻¹qᵀx + y) + xᵀ(P - qD⁻¹qᵀ)x`. -/
theorem gapsw80_t2_bilin_schur_eq₂₂
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin k) R)
    (D : Matrix (Fin k) (Fin k) R) [Invertible D] (hD : Dᵀ = D)
    (x : Fin m → R) (y : Fin k → R) :
    (Sum.elim x y) ᵥ* (fromBlocks P q qᵀ D) ⬝ᵥ (Sum.elim x y)
      = ((⅟D * qᵀ) *ᵥ x + y) ᵥ* D ⬝ᵥ ((⅟D * qᵀ) *ᵥ x + y)
        + x ᵥ* (P - q * ⅟D * qᵀ) ⬝ᵥ x := by

  have hDinv : (⅟D)ᵀ = ⅟D := by
    have : Dᵀ * (⅟D)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, invOf_mul_self, Matrix.transpose_one]
    rw [hD] at this
    exact (invOf_eq_right_inv this).symm
  have hz : ((⅟D * qᵀ) *ᵥ x) ᵥ* D = x ᵥ* q := by
    rw [← vecMul_transpose, Matrix.transpose_mul, hDinv, Matrix.transpose_transpose,
      vecMul_vecMul, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
  have hDz : D *ᵥ ((⅟D * qᵀ) *ᵥ x) = qᵀ *ᵥ x := by
    rw [mulVec_mulVec, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  have hxy : x ᵥ* q ⬝ᵥ y = y ᵥ* qᵀ ⬝ᵥ x := by
    rw [← dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hqS : x ᵥ* (q * ⅟D * qᵀ) ⬝ᵥ x = x ᵥ* q ⬝ᵥ ((⅟D * qᵀ) *ᵥ x) := by
    rw [Matrix.mul_assoc, ← vecMul_vecMul, ← dotProduct_mulVec]
  have hyDz : y ᵥ* D ⬝ᵥ ((⅟D * qᵀ) *ᵥ x) = y ᵥ* qᵀ ⬝ᵥ x := by
    rw [← dotProduct_mulVec, hDz, dotProduct_mulVec]
  simp only [vecMul_fromBlocks, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, add_vecMul, vecMul_sub, add_dotProduct,
    dotProduct_add, sub_dotProduct, hz, hyDz, hqS]
  ring

/-- For a symmetric invertible block `D`, the quadratic form `z ⬝ᵥ (fromBlocks P q qᵀ D *ᵥ z)` at
`z = Sum.elim x y` equals `(D⁻¹qᵀx + y) ⬝ᵥ D(D⁻¹qᵀx + y) + x ⬝ᵥ (P - qD⁻¹qᵀ)x`. -/
theorem gapsw80_t2_bilin_schur_eq₂₂'
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin k) R)
    (D : Matrix (Fin k) (Fin k) R) [Invertible D] (hD : Dᵀ = D)
    (x : Fin m → R) (y : Fin k → R) :
    (Sum.elim x y) ⬝ᵥ ((fromBlocks P q qᵀ D) *ᵥ (Sum.elim x y))
      = ((⅟D * qᵀ) *ᵥ x + y) ⬝ᵥ (D *ᵥ ((⅟D * qᵀ) *ᵥ x + y))
        + x ⬝ᵥ ((P - q * ⅟D * qᵀ) *ᵥ x) := by
  rw [dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec]
  exact gapsw80_t2_bilin_schur_eq₂₂ P q D hD x y

/-- For symmetric `P`, a column `q`, invertible scalar `a` with `P - q a⁻¹ qᵀ` invertible, the
quadratic form of the inverse of `fromBlocks P q qᵀ (a • 1)` at `Sum.elim X (fun _ => Y)` equals
the quadratic form of `(P - q a⁻¹ qᵀ)⁻¹` at `X - (a⁻¹ Y) q` plus `a⁻¹ Y^2`. -/
theorem gapsw80_t2_bilin_schur_inv_scalar
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin 1) R)
    (a : R) [Invertible a] (hP : Pᵀ = P)
    [Invertible (P - q * ⅟a • qᵀ)]
    (X : Fin m → R) (Y : R) :
    (Sum.elim X (fun _ => Y)) ⬝ᵥ
        ((fromBlocks P q qᵀ ((a : R) • (1 : Matrix (Fin 1) (Fin 1) R)))⁻¹
          *ᵥ (Sum.elim X (fun _ => Y)))
      = (X - (⅟a * Y) • (fun i => q i 0)) ⬝ᵥ
          ((P - q * ⅟a • qᵀ)⁻¹ *ᵥ (X - (⅟a * Y) • (fun i => q i 0)))
        + ⅟a * Y ^ 2 := by
  classical
  set D : Matrix (Fin 1) (Fin 1) R := (a : R) • 1 with hD
  have hDi : Invertible D :=
    ⟨⅟a • 1, by rw [hD, smul_mul_smul_comm, invOf_mul_self, one_mul, one_smul],
      by rw [hD, smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul]⟩
  have hiD : ⅟D = (⅟a : R) • (1 : Matrix (Fin 1) (Fin 1) R) :=
    invOf_eq_right_inv
      (by rw [hD, smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul])
  set S : Matrix (Fin m) (Fin m) R := P - q * ⅟a • qᵀ with hS
  have hSeq : P - q * ⅟D * qᵀ = S := by
    rw [hS, hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  have : Invertible (P - q * ⅟D * qᵀ) := hSeq ▸ (inferInstance : Invertible S)
  have hMi : Invertible (fromBlocks P q qᵀ D) := fromBlocks₂₂Invertible P q qᵀ D

  set q₀ : Fin m → R := fun i => q i 0
  have hq0T : ∀ x : Fin m → R, qᵀ *ᵥ x = fun _ => q₀ ⬝ᵥ x := fun x => by
    funext j; fin_cases j; simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, q₀]
  have hq0 : ∀ y : Fin 1 → R, q *ᵥ y = y 0 • q₀ := fun y => by
    funext i; simp [Matrix.mulVec, dotProduct, q₀, mul_comm]
  have hF1 : ∀ (c : R) (y : Fin 1 → R), (fun _ => c) ⬝ᵥ y = c * y 0 := fun c y => by
    simp [dotProduct]
  have hSiT : (⅟S)ᵀ = ⅟S := by
    have hST : Sᵀ = S := by
      rw [hS, Matrix.transpose_sub, hP, Matrix.transpose_mul, Matrix.transpose_smul,
        Matrix.transpose_transpose, Matrix.smul_mul, ← Matrix.mul_smul]
    have h1 : Sᵀ * (⅟S)ᵀ = 1 := by rw [← Matrix.transpose_mul, invOf_mul_self,
      Matrix.transpose_one]
    rw [hST] at h1; exact (invOf_eq_right_inv h1).symm
  have hswap : ∀ x y : Fin m → R, x ⬝ᵥ (⅟S *ᵥ y) = y ⬝ᵥ (⅟S *ᵥ x) := fun x y => by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose (⅟S) x, hSiT, dotProduct_comm]
  have hDy : ⅟D *ᵥ (fun _ => Y : Fin 1 → R) = fun _ => ⅟a * Y := by
    funext j; fin_cases j
    simp only [hiD, smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]

  rw [← Matrix.invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq, Matrix.fromBlocks_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
  simp only [hSeq]

  have hTop : (⅟S *ᵥ X + (-(⅟S * q * ⅟D)) *ᵥ fun _ => Y)
      = ⅟S *ᵥ X - (⅟a * Y) • (⅟S *ᵥ q₀) := by
    rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDy,
      hq0, Matrix.mulVec_smul, sub_eq_add_neg]
  have hBot : ((-(⅟D * qᵀ * ⅟S)) *ᵥ X + (⅟D + ⅟D * qᵀ * ⅟S * q * ⅟D) *ᵥ fun _ => Y)
      = fun _ => -(⅟a * (q₀ ⬝ᵥ (⅟S *ᵥ X)))
          + (⅟a * Y + ⅟a ^ 2 * Y * (q₀ ⬝ᵥ (⅟S *ᵥ q₀))) := by
    funext j; fin_cases j
    simp only [Matrix.neg_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      hq0, Matrix.mulVec_smul, hq0T, hiD, smul_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, smul_smul]
    ring
  rw [hTop, hBot, hF1]
  rw [← Matrix.invOf_eq_nonsing_inv, Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hswap X q₀]
  ring

/-- If the real block matrix `fromBlocks P q qᵀ D` is positive definite with `D` Hermitian and
invertible, then the Schur complement `P - q * ⅟D * qᵀ` is positive definite. -/
theorem gapsw80_t2_posDef_schur
    {P : Matrix (Fin m) (Fin m) ℝ} {q : Matrix (Fin m) (Fin k) ℝ}
    {D : Matrix (Fin k) (Fin k) ℝ} [Invertible D] (hD : D.IsHermitian)
    (hM : (fromBlocks P q qᵀ D).PosDef) :
    (P - q * ⅟D * qᵀ).PosDef := by
  have hMi := (posDef_iff_dotProduct_mulVec).mp hM
  have hDT : Dᵀ = D := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hD
  have hDiT : (⅟D)ᵀ = ⅟D := by
    have : Dᵀ * (⅟D)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, invOf_mul_self, Matrix.transpose_one]
    rw [hDT] at this; exact (invOf_eq_right_inv this).symm
  have hPherm : P.IsHermitian := (Matrix.isHermitian_fromBlocks_iff.mp hMi.1).1
  have hPT : Pᵀ = P := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hPherm
  have hSH : (P - q * ⅟D * qᵀ).IsHermitian := by
    show (P - q * ⅟D * qᵀ)ᴴ = P - q * ⅟D * qᵀ
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hPT, hDiT, Matrix.mul_assoc]
  refine (posDef_iff_dotProduct_mulVec).mpr ⟨hSH, fun x hx => ?_⟩

  set y : Fin k → ℝ := -((⅟D * qᵀ) *ᵥ x) with hy
  have hxy : Sum.elim x y ≠ 0 := fun h => hx (funext fun i => by
    have := congrFun h (Sum.inl i); simpa using this)
  have key : 0 < star (Sum.elim x y) ⬝ᵥ ((fromBlocks P q qᵀ D) *ᵥ Sum.elim x y) :=
    hMi.2 hxy
  rw [show star (Sum.elim x y) = Sum.elim x y from rfl,
    gapsw80_t2_bilin_schur_eq₂₂' P q D hDT x y] at key
  simp only [hy] at key
  simpa [show star x = x from rfl] using key

end BilinearSchur

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

section InductionStep

variable {m : ℕ}

/-- The Poisson summation identity for the Gaussian of a matrix `M` indexed by `Fin m ⊕ Fin 1` at
parameter `t` and shift `b`, stating that the theta sum over `(Fin m ⊕ Fin 1) → ℤ` equals
$(t^{m+1}\det M)^{-1/2}$ times the dual sum with `M⁻¹`. -/
def PoissonLawBlock (M : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℝ)
    (t : ℝ) (b : (Fin m ⊕ Fin 1) → ℂ) : Prop :=
  (∑' v : (Fin m ⊕ Fin 1) → ℤ,
      cexp (-(π : ℂ) * t *
          (((fun i => (v i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (v i : ℝ)) : ℝ) : ℂ)
        + 2 * π * ∑ i, b i * (v i : ℂ)))
    = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) *
      ∑' w : (Fin m ⊕ Fin 1) → ℤ,
        cexp (-(π : ℂ) / t *
          ((fun i => (w i : ℂ) + Complex.I * b i) ⬝ᵥ
            ((M⁻¹).map ((↑) : ℝ → ℂ) *ᵥ fun i => (w i : ℂ) + Complex.I * b i)))


/-- If the Gaussian Poisson identity `PoissonLaw` holds in dimension `m` for all positive definite
matrices, positive `t` and all `b`, then `PoissonLawBlock M t b` holds for every positive definite
`M` on `Fin m ⊕ Fin 1` and `t > 0`. -/
theorem gapsw80_t2_poisson_step
    (IH : ∀ (S : Matrix (Fin m) (Fin m) ℝ), S.PosDef →
      ∀ {t : ℝ}, 0 < t → ∀ b : Fin m → ℂ, PoissonLaw S t b)
    (M : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℝ) (hM : M.PosDef)
    {t : ℝ} (ht : 0 < t) (b : (Fin m ⊕ Fin 1) → ℂ) :
    PoissonLawBlock M t b := by
  classical

  set P : Matrix (Fin m) (Fin m) ℝ := M.toBlocks₁₁
  set q : Matrix (Fin m) (Fin 1) ℝ := M.toBlocks₁₂
  set a : ℝ := M (Sum.inr 0) (Sum.inr 0)
  set b' : Fin m → ℂ := b ∘ Sum.inl
  set b₁ : ℂ := b (Sum.inr 0)
  set q₀ : Fin m → ℝ := fun i => q i 0
  have hMT : Mᵀ = M := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hM.1
  have hMblock : M = fromBlocks P q qᵀ ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    conv_lhs => rw [← M.fromBlocks_toBlocks]
    congr 1
    · ext i j
      have := congrFun (congrFun hMT (Sum.inl j)) (Sum.inr i)
      simp [Matrix.transpose_apply] at this
      exact this
    · ext i j; fin_cases i; fin_cases j
      simp [Matrix.toBlocks₂₂, a, Matrix.smul_apply]
  have ha : 0 < a := by
    set v₀ : (Fin m ⊕ Fin 1) → ℝ := Sum.elim 0 (fun _ => (1 : ℝ)) with hv₀
    have hne : v₀ ≠ 0 := fun h =>
      (one_ne_zero : (1 : ℝ) ≠ 0) (by have := congrFun h (Sum.inr 0); simp [hv₀] at this)
    have key : 0 < star v₀ ⬝ᵥ (M *ᵥ v₀) :=
      (posDef_iff_dotProduct_mulVec.mp hM).2 hne
    have heval : star v₀ ⬝ᵥ (M *ᵥ v₀) = a := by
      rw [show (star v₀ : _ → ℝ) = v₀ from rfl, hv₀, hMblock, fromBlocks_mulVec,
        sumElim_dotProduct_sumElim]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, zero_add,
        smul_mulVec, Matrix.one_mulVec, dotProduct,
        Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, mul_one, one_mul,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    rwa [heval] at key
  have haI : Invertible a := invertibleOfNonzero ha.ne'
  have haCI : Invertible (a : ℂ) := invertibleOfNonzero (Complex.ofReal_ne_zero.mpr ha.ne')
  have hia : (⅟a : ℝ) = a⁻¹ := invOf_eq_inv a
  have hiaC : (⅟(a : ℂ) : ℂ) = (a : ℂ)⁻¹ := invOf_eq_inv (a : ℂ)
  have hDi : Invertible ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
    ⟨⅟a • 1, by rw [smul_mul_smul_comm, invOf_mul_self, one_mul, one_smul],
      by rw [smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul]⟩
  have hiD : ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (⅟a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
    invOf_eq_right_inv (by rw [smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul])
  set S : Matrix (Fin m) (Fin m) ℝ := P - q * ⅟a • qᵀ with hS
  have hSpd : S.PosDef := by
    have hDh : ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).IsHermitian := by
      show _ = _; rw [Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.transpose_smul, Matrix.transpose_one]
    have hSalt :
        (P - q * ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ).PosDef :=
      gapsw80_t2_posDef_schur hDh (hMblock ▸ hM)
    rwa [hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Matrix.mul_smul] at hSalt
  have hdetS : 0 < S.det := hSpd.det_pos
  have hSI : Invertible S :=
    Matrix.invertibleOfIsUnitDet S (isUnit_iff_ne_zero.mpr hdetS.ne')
  have hPT : Pᵀ = P := by
    ext i j
    have := congrFun (congrFun hMT (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.transpose_apply, P, Matrix.toBlocks₁₁] using this

  set e : ((Fin m ⊕ Fin 1) → ℤ) ≃ (Fin m → ℤ) × ℤ :=
    { toFun := fun v => ⟨v ∘ Sum.inl, v (Sum.inr 0)⟩
      invFun := fun p => Sum.elim p.1 (fun _ => p.2)
      left_inv := fun v => by funext i; cases i with
        | inl i => rfl
        | inr j => fin_cases j; rfl
      right_inv := fun p => rfl }
  set q₀u : (Fin m → ℤ) → ℝ := fun u => ∑ i, q₀ i * (u i : ℝ)

  have hQsplit : ∀ (u : Fin m → ℤ) (k : ℤ),
      (fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
          ⬝ᵥ (M *ᵥ fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
        = a * (a⁻¹ * q₀u u + (k : ℝ)) ^ 2 + rQuad S (zcastR u) := by
    intro u k
    have hcast : (fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
        = Sum.elim (zcastR u) (fun _ => (k : ℝ)) := by
      funext i; cases i with | inl i => rfl | inr j => rfl
    rw [hcast, hMblock,
      gapsw80_t2_bilin_schur_eq₂₂' P q ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (by rw [Matrix.transpose_smul, Matrix.transpose_one])
        (zcastR u) (fun _ => (k : ℝ))]
    have hSeq : P - q * ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ = S := by
      rw [hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Matrix.mul_smul]
    rw [hSeq]
    congr 1
    have hv : (⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ) *ᵥ zcastR u
          + (fun _ => (k : ℝ))
        = fun _ => a⁻¹ * q₀u u + (k : ℝ) := by
      funext j
      simp only [hiD, Matrix.smul_mul, Matrix.one_mul, smul_mulVec, Matrix.mulVec,
        dotProduct, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
        q₀u, q₀, zcastR, hia, Fin.eq_zero j]
    rw [hv, smul_mulVec, Matrix.one_mulVec]
    simp only [dotProduct, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
    ring

  have hLsplit : ∀ (u : Fin m → ℤ) (k : ℤ),
      (∑ i, b i * ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ))
        = (∑ i, b' i * (u i : ℂ)) + b₁ * (k : ℂ) := by
    intro u k
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one, b', b₁,
      Function.comp_apply]

  set β : (Fin m → ℤ) → ℂ := fun u => b₁ - (t : ℂ) * (q₀u u : ℂ)
  have htare : 0 < ((t * a : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; exact mul_pos ht ha

  have h1D : ∀ u : Fin m → ℤ,
      (∑' k : ℤ, cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (k : ℂ) ^ 2
          + 2 * π * (β u) * (k : ℂ)))
        = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' w : ℤ, cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
              * ((w : ℂ) + Complex.I * (β u)) ^ 2) :=
    fun u => Complex.tsum_exp_neg_quadratic htare (β u)

  set β' : ℤ → (Fin m → ℂ) :=
    fun w i => b' i + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hqsum : ∀ u : Fin m → ℤ,
      (∑ i, (q₀ i : ℂ) * (u i : ℂ)) = ((q₀u u : ℝ) : ℂ) := fun u => by
    simp only [q₀u, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  have hβ'sum : ∀ (w : ℤ) (u : Fin m → ℤ), (∑ i, (β' w) i * (u i : ℂ))
      = (∑ i, b' i * (u i : ℂ))
        + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀u u : ℂ) := fun w u => by
    rw [← hqsum u]
    simp only [β', add_mul, Finset.sum_add_distrib, Finset.mul_sum]; ring_nf

  have hExpEq : ∀ (u : Fin m → ℤ) (w : ℤ),
      (-(π : ℂ) * (t : ℂ)
            * ((a * (a⁻¹ * q₀u u) ^ 2 : ℝ) : ℂ)
          + 2 * π * (∑ i, b' i * (u i : ℂ))
          + (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * (β u)) ^ 2))
        = (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
          + 2 * π * (∑ i, (β' w) i * (u i : ℂ)) := by
    intro u w
    rw [hβ'sum w u]
    simp only [β, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv]
    have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
    field_simp
    ring_nf
    simp only [hI2]
    ring

  set Fuw : (Fin m → ℤ) × ℤ → ℂ := fun p =>
    cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((p.2 : ℂ) + Complex.I * b₁) ^ 2)
      * thetaTerm S t (β' p.2) p.1
  have haiC : ((a : ℂ))⁻¹ = (((a⁻¹ : ℝ)) : ℂ) := by
    rw [Complex.ofReal_inv]
  have hReβ' : ∀ w i, (β' w i).re = (b' i).re - a⁻¹ * b₁.re * q₀ i := fun w i => by
    have h1 : β' w i
        = b' i + (((a⁻¹ * q₀ i : ℝ)) : ℂ) * (Complex.I * (w : ℂ) - b₁) := by
      simp only [β', haiC]; push_cast; ring_nf; simp [Complex.I_sq]; ring
    rw [h1, Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.intCast_im]
    ring
  have hR2' : Summable fun p : (Fin m → ℤ) × ℤ => ‖Fuw p‖ := by
    obtain ⟨c, hc, hQ⟩ := gapsw80_t2_posDef_quadForm_lower hSpd
    set gU : Fin m → ℤ → ℝ := fun i k =>
      rexp (-(π * t * c * (k : ℝ) ^ 2)
        + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (k : ℝ))
    have hUmaj : Summable fun u : Fin m → ℤ => ∏ i, gU i (u i) :=
      gapsw80_t2_summable_prod_fin (n := m) (f := gU)
        (fun _ _ => (Real.exp_pos _).le)
        (fun i => (gapsw80_t2_summable_1D_real (a := π * t * c) (by positivity)
            (2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i))).congr
          fun k => by unfold gU; ring_nf)
    have hWmaj : Summable fun w : ℤ =>
        ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
          * ((w : ℂ) + Complex.I * b₁) ^ 2)‖ := by
      have hcoef : (-(π : ℂ) / ((t * a : ℝ) : ℂ))
          = (((-(π / (t * a))) : ℝ) : ℂ) := by push_cast; ring
      have hnorm : ∀ w : ℤ,
          ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)‖
            = rexp (-(π / (t * a)) * ((w : ℝ) - b₁.im) ^ 2)
              * rexp ((π / (t * a)) * b₁.re ^ 2) := fun w => by
        rw [Complex.norm_exp, hcoef, Complex.re_ofReal_mul, ← Real.exp_add]
        congr 1
        have : ((w : ℂ) + Complex.I * b₁).re = (w : ℝ) - b₁.im ∧
            ((w : ℂ) + Complex.I * b₁).im = b₁.re := by
          refine ⟨?_, ?_⟩ <;>
            simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
              Complex.mul_im, Complex.I_re, Complex.I_im, Complex.intCast_re,
              Complex.intCast_im, zero_mul, one_mul, zero_sub, zero_add]
          ring
        rw [show (((w : ℂ) + Complex.I * b₁) ^ 2).re
            = ((w : ℝ) - b₁.im) ^ 2 - b₁.re ^ 2 by
          rw [sq, Complex.mul_re, this.1, this.2]; ring]
        ring
      simp_rw [hnorm]
      exact (((gapsw80_t2_summable_1D_real (a := π / (t * a))
          (div_pos pi_pos (mul_pos ht ha)) (2 * (π / (t * a)) * b₁.im)).mul_left
        (rexp (-(π / (t * a)) * b₁.im ^ 2))).congr fun w => by
          rw [← Real.exp_add]; ring_nf).mul_right _

    have hbound : ∀ p : (Fin m → ℤ) × ℤ,
        ‖Fuw p‖ ≤ ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
            * ((p.2 : ℂ) + Complex.I * b₁) ^ 2)‖ * ∏ i, gU i (p.1 i) := fun p => by
      unfold Fuw
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      unfold thetaTerm
      rw [Complex.norm_exp,
        show (∏ i, gU i (p.1 i)) = rexp (∑ i,
          (-(π * t * c * (p.1 i : ℝ) ^ 2)
            + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ))) from
          (Real.exp_sum _ _).symm]
      apply Real.exp_le_exp.mpr
      have hre : (-(π : ℂ) * (t : ℂ) * (rQuad S (zcastR p.1) : ℂ)
            + 2 * π * ∑ i, (β' p.2) i * (p.1 i : ℂ)).re
          = -(π * t * rQuad S (zcastR p.1))
            + 2 * π * ∑ i, ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ) := by
        have h1 : -(π : ℂ) * (t : ℂ) * (rQuad S (zcastR p.1) : ℂ)
            = (((-(π * t * rQuad S (zcastR p.1))) : ℝ) : ℂ) := by push_cast; ring
        have h2 : (2 : ℂ) * (π : ℂ) = (((2 * π) : ℝ) : ℂ) := by push_cast; ring
        rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
          Complex.re_sum]
        congr 2
        exact Finset.sum_congr rfl fun i _ => by
          rw [Complex.mul_re, hReβ' p.2 i, Complex.intCast_re, Complex.intCast_im,
            mul_zero, sub_zero]
      rw [hre]
      have hxx : zcastR p.1 ⬝ᵥ zcastR p.1 = ∑ i, (p.1 i : ℝ) ^ 2 := by
        simp only [dotProduct, zcastR]
        exact Finset.sum_congr rfl fun i _ => (sq _).symm
      have hQv := hQ (zcastR p.1); rw [hxx] at hQv
      have hsplit : (∑ i, (-(π * t * c * (p.1 i : ℝ) ^ 2)
            + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ)))
          = -(π * t) * (c * ∑ i, (p.1 i : ℝ) ^ 2)
            + (2 * π) * ∑ i, ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ) := by
        rw [Finset.sum_add_distrib]; congr 1
        · rw [← mul_assoc, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit]
      nlinarith [mul_pos pi_pos ht]
    exact (hUmaj.mul_of_nonneg hWmaj
        (fun u => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)
        (fun w => norm_nonneg _)).of_nonneg_of_le
      (fun p => norm_nonneg _)
      (fun p => by rw [mul_comm]; exact hbound p)

  have hdetM : M.det = a * S.det := by
    have hdD : ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).det = a := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, pow_one]
    rw [hMblock, Matrix.det_fromBlocks₂₂, hdD, hiD, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, ← Matrix.mul_smul]
  have hpref : (1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ))
        * (((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
      = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) := by
    have hta : (0 : ℝ) < t * a := mul_pos ht ha
    have htmS : (0 : ℝ) < t ^ m * S.det := mul_pos (pow_pos ht m) hdetS
    rw [one_div, ← Complex.cpow_neg,
      show ((t ^ (m + 1) * M.det : ℝ) : ℂ)
        = ((t * a : ℝ) : ℂ) * ((t ^ m * S.det : ℝ) : ℂ) by
          push_cast; rw [hdetM]; push_cast; ring,
      ← Complex.mul_cpow_ofReal_nonneg hta.le htmS.le]

  set Pc : Matrix (Fin m) (Fin m) ℂ := P.map ((↑) : ℝ → ℂ)
  set qc : Matrix (Fin m) (Fin 1) ℂ := q.map ((↑) : ℝ → ℂ)
  have hqcT : qcᵀ = qᵀ.map ((↑) : ℝ → ℂ) := by
    ext i j; simp [qc, Matrix.transpose_apply, Matrix.map_apply]
  have hPcT : Pcᵀ = Pc := by
    ext i j; simp only [Pc, Matrix.transpose_apply, Matrix.map_apply]
    rw [← congrFun (congrFun hPT i) j, Matrix.transpose_apply]
  have hMc : (M.map ((↑) : ℝ → ℂ))
      = fromBlocks Pc qc qcᵀ ((a : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
    rw [hMblock]; ext (i | i) (j | j) <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
        Pc, qc, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
        apply_ite ((↑) : ℝ → ℂ)]

  have hMI : Invertible M :=
    Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hM.det_pos.ne')
  have hMinvC : (M⁻¹).map ((↑) : ℝ → ℂ) = (M.map ((↑) : ℝ → ℂ))⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    have h1 : M.map ((↑) : ℝ → ℂ) * (M⁻¹).map ((↑) : ℝ → ℂ)
        = (M * M⁻¹).map ((↑) : ℝ → ℂ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Complex.ofReal_sum,
        Complex.ofReal_mul]
    rw [h1, ← Matrix.invOf_eq_nonsing_inv, mul_invOf_self]
    ext i j; simp [Matrix.map_apply, Matrix.one_apply, apply_ite ((↑) : ℝ → ℂ)]
  have hSinvC' : (S⁻¹).map ((↑) : ℝ → ℂ) = (S.map ((↑) : ℝ → ℂ))⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    have h1 : S.map ((↑) : ℝ → ℂ) * (S⁻¹).map ((↑) : ℝ → ℂ)
        = (S * S⁻¹).map ((↑) : ℝ → ℂ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Complex.ofReal_sum,
        Complex.ofReal_mul]
    rw [h1, ← Matrix.invOf_eq_nonsing_inv, mul_invOf_self]
    ext i j; simp [Matrix.map_apply, Matrix.one_apply, apply_ite ((↑) : ℝ → ℂ)]
  have hdetSc : (liftC S).det = ((S.det : ℝ) : ℂ) := by
    have := (RingHom.map_det Complex.ofRealHom S).symm
    simp [RingHom.mapMatrix_apply] at this
    exact this
  have hSc : liftC S = Pc - qc * ⅟(a : ℂ) • qcᵀ := by
    unfold liftC; rw [hS]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, Pc, qc,
      Matrix.smul_apply, Matrix.transpose_apply, Fin.sum_univ_one, hiaC, hia,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv, smul_eq_mul]
  have hScI : Invertible (Pc - qc * ⅟(a : ℂ) • qcᵀ) := by
    rw [← hSc]
    exact (liftC S).invertibleOfIsUnitDet
      (hdetSc ▸ isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hdetS.ne'))
  have hSinvC : liftC S⁻¹ = (Pc - qc * ⅟(a : ℂ) • qcᵀ)⁻¹ := by
    have h1 : liftC S⁻¹ = (S⁻¹).map ((↑) : ℝ → ℂ) := rfl
    have h2 : S.map ((↑) : ℝ → ℂ) = liftC S := rfl
    rw [h1, hSinvC', h2, hSc]
  have hDualSplit : ∀ (w' : Fin m → ℤ) (w : ℤ),
      cexp (-(π : ℂ) / (t : ℂ)
          * ((fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
                + Complex.I * b i)
            ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
              *ᵥ fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
                + Complex.I * b i)))
        = cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
          * dualTerm S t (β' w) w' := by
    intro w' w
    set X : Fin m → ℂ := fun i => (w' i : ℂ) + Complex.I * b' i
    set Y : ℂ := (w : ℂ) + Complex.I * b₁
    have hcast : (fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
          + Complex.I * b i)
        = Sum.elim X (fun _ => Y) := by
      funext i; cases i with
      | inl i => simp [X, b']
      | inr j => fin_cases j; simp [Y, b₁]
    rw [hcast, hMinvC, hMc,
      gapsw80_t2_bilin_schur_inv_scalar Pc qc (a : ℂ) hPcT X Y]
    unfold dualTerm cQuad
    rw [hSinvC, ← Complex.exp_add]
    congr 1
    have hXshift : (X - (⅟(a : ℂ) * Y) • fun i => qc i 0)
        = fun i => (w' i : ℂ) + Complex.I * (β' w) i := by
      funext i
      have hlhs : (X - (⅟(a : ℂ) * Y) • fun i => qc i 0) i
          = ((w' i : ℂ) + Complex.I * b' i)
            - (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ) := by
        simp only [X, Y, qc, Matrix.map_apply, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, hiaC, q₀]
      have hrhs : (w' i : ℂ) + Complex.I * (β' w) i
          = ((w' i : ℂ) + Complex.I * b' i)
            - (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ) := by
        have hβ'i : (β' w) i
            = b' i + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁)
              * (q₀ i : ℂ) := rfl
        rw [hβ'i, mul_add,
          show Complex.I * (Complex.I * (a : ℂ)⁻¹
              * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ))
            = -((a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)) by
              rw [show Complex.I * (Complex.I * (a : ℂ)⁻¹
                    * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ))
                  = (Complex.I * Complex.I) * ((a : ℂ)⁻¹
                    * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)) from by ring,
                Complex.I_mul_I]; ring]
        ring
      rw [hlhs, hrhs]
    rw [hXshift, hiaC]
    have hcoef2 : (-(π : ℂ) / ((t * a : ℝ) : ℂ))
        = (-(π : ℂ) / (t : ℂ)) * (a : ℂ)⁻¹ := by push_cast; field_simp
    rw [hcoef2, mul_add]
    ring

  set eF : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  have hA' : (Matrix.reindex eF eF M).PosDef := by
    refine (posDef_iff_dotProduct_mulVec).mpr ⟨?_, ?_⟩
    · show _ = _
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply,
        ← congrFun (congrFun hMT (eF.symm i)) (eF.symm j), Matrix.transpose_apply]
    · intro x hx
      have hxe : (fun i => x (eF i)) ≠ 0 := fun h => hx (funext fun j => by
        have := congrFun h (eF.symm j); simpa using this)
      have key := (posDef_iff_dotProduct_mulVec.mp hM).2 hxe
      refine lt_of_lt_of_eq key ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
        Matrix.submatrix_apply, star_trivial]
      refine Fintype.sum_equiv eF (fun i => x (eF i) * ∑ j, M i j * x (eF j))
        (fun i => x i * ∑ j, M (eF.symm i) (eF.symm j) * x j) fun i => ?_
      simp only [Equiv.symm_apply_apply]
      congr 1
      exact Fintype.sum_equiv eF (fun j => M i j * x (eF j))
        (fun j => M i (eF.symm j) * x j) fun j => by
          simp only [Equiv.symm_apply_apply]

  set ePi : (Fin (m + 1) → ℤ) ≃ ((Fin m ⊕ Fin 1) → ℤ) :=
    ⟨fun w => w ∘ eF, fun v => v ∘ eF.symm,
      fun w => funext fun j => congrArg w (eF.apply_symm_apply j),
      fun v => funext fun i => congrArg v (eF.symm_apply_apply i)⟩

  have hQeq : ∀ w : Fin (m + 1) → ℤ,
      rQuad (Matrix.reindex eF eF M) (zcastR w)
        = (fun i => ((ePi w) i : ℝ)) ⬝ᵥ (M *ᵥ fun i => ((ePi w) i : ℝ)) := fun w => by
    simp only [rQuad, zcastR, dotProduct, Matrix.mulVec, Matrix.reindex_apply,
      Matrix.submatrix_apply, ePi, Equiv.coe_fn_mk, Function.comp_apply]
    exact Fintype.sum_equiv eF.symm _ _ fun i => by
      simp only [Equiv.apply_symm_apply]
      exact congrArg _ (Fintype.sum_equiv eF.symm _ _ fun i' => by
        simp only [Equiv.apply_symm_apply])
  have hLeq : ∀ w : Fin (m + 1) → ℤ,
      (∑ j, (b ∘ eF.symm) j * (w j : ℂ)) = ∑ i, b i * ((ePi w) i : ℂ) := fun w =>
    Fintype.sum_equiv eF.symm _ _ fun j => by
      simp only [ePi, Equiv.coe_fn_mk, Function.comp_apply, Equiv.apply_symm_apply]

  let LB : ((Fin m ⊕ Fin 1) → ℤ) → ℂ := fun v =>
    cexp (-(π : ℂ) * t
        * (((fun i => (v i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (v i : ℝ)) : ℝ) : ℂ)
      + 2 * π * ∑ i, b i * (v i : ℂ))
  let RB : ((Fin m ⊕ Fin 1) → ℤ) → ℂ := fun v =>
    cexp (-(π : ℂ) / t *
      ((fun i => (v i : ℂ) + Complex.I * b i) ⬝ᵥ
        ((M⁻¹).map ((↑) : ℝ → ℂ) *ᵥ fun i => (v i : ℂ) + Complex.I * b i)))
  have hLBsum : Summable LB := by
    refine (Equiv.summable_iff ePi).mp
      (((gapsw80_t2_summable_thetaTerm hA' ht (b ∘ eF.symm)).of_norm).congr fun w => ?_)
    show thetaTerm _ _ _ w = LB (ePi w)
    simp only [thetaTerm, LB, hQeq w, hLeq w]
  have hLHSsum : Summable fun p : (Fin m → ℤ) × ℤ => LB (e.symm p) :=
    (e.symm.summable_iff (f := LB)).mpr hLBsum

  have hRBsum : Summable RB := by
    refine (Equiv.summable_iff ePi).mp
      (((gapsw80_t2_summable_dualTerm hA' ht (b ∘ eF.symm)).of_norm).congr fun w => ?_)
    show dualTerm _ _ _ w = RB (ePi w)
    simp only [dualTerm, cQuad, liftC, RB, Matrix.inv_reindex]
    congr 2
    simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.map_apply, ePi, Equiv.coe_fn_mk,
      Function.comp_apply]
    exact Fintype.sum_equiv eF.symm _ _ fun i => by
      simp only [Equiv.apply_symm_apply]
      exact congrArg₂ _ rfl (Fintype.sum_equiv eF.symm _ _ fun i' => by
        simp only [Equiv.apply_symm_apply])
  have hRHSsum : Summable fun p : (Fin m → ℤ) × ℤ => RB (e.symm p) :=
    (e.symm.summable_iff (f := RB)).mpr hRBsum

  have hLHSrw : ∀ p : (Fin m → ℤ) × ℤ,
      LB (e.symm p)
        = cexp (-(π : ℂ) * t * (rQuad S (zcastR p.1) : ℂ)
              + 2 * π * (∑ i, b' i * (p.1 i : ℂ))
            + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u p.1) ^ 2 : ℝ) : ℂ)))
          * cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (p.2 : ℂ) ^ 2
              + 2 * π * (β p.1) * (p.2 : ℂ)) := fun p => by
    show cexp _ = _
    rw [show e.symm p = Sum.elim p.1 (fun _ => p.2) from rfl,
      hQsplit p.1 p.2, hLsplit p.1 p.2, ← Complex.exp_add]
    congr 1; simp only [β]; push_cast; field_simp; ring

  have hFuwEq : ∀ p : (Fin m → ℤ) × ℤ,
      cexp (-(π : ℂ) * t * (rQuad S (zcastR p.1) : ℂ)
            + 2 * π * (∑ i, b' i * (p.1 i : ℂ))
          + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u p.1) ^ 2 : ℝ) : ℂ)))
        * cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((p.2 : ℂ) + Complex.I * (β p.1)) ^ 2)
      = Fuw p := fun p => by
    unfold Fuw thetaTerm rQuad; rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have key := hExpEq p.1 p.2
    linear_combination key

  have hR2'a : Summable Fuw := hR2'.of_norm
  have hFuwcomm : (∑' u, ∑' w, Fuw (u, w)) = ∑' w, ∑' u, Fuw (u, w) :=
    (Summable.tsum_comm (f := fun u w => Fuw (u, w))
      (show Summable (Function.uncurry fun u w => Fuw (u, w)) from hR2'a)).symm
  have hRHScomm : (∑' (w' : Fin m → ℤ), ∑' (w : ℤ), RB (e.symm (w', w)))
      = ∑' (w : ℤ), ∑' (w' : Fin m → ℤ), RB (e.symm (w', w)) :=
    (Summable.tsum_comm (f := fun w' w => RB (e.symm (w', w)))
      (show Summable (Function.uncurry fun w' w => RB (e.symm (w', w))) from
        hRHSsum)).symm
  show (∑' v, LB v) = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) * ∑' w, RB w
  calc (∑' v, LB v)
      = ∑' p : (Fin m → ℤ) × ℤ, LB (e.symm p) := (e.symm.tsum_eq LB).symm
    _ = ∑' u : Fin m → ℤ, ∑' k : ℤ,
          cexp (-(π : ℂ) * t * (rQuad S (zcastR u) : ℂ)
                + 2 * π * (∑ i, b' i * (u i : ℂ))
              + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u u) ^ 2 : ℝ) : ℂ)))
            * cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (k : ℂ) ^ 2
                + 2 * π * (β u) * (k : ℂ)) := by
        rw [tsum_congr hLHSrw, (hLHSsum.congr hLHSrw).tsum_prod]
    _ = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' u : Fin m → ℤ, ∑' w : ℤ, Fuw (u, w) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun u => by
          rw [tsum_mul_left, h1D u, ← mul_assoc,
            mul_comm _ (1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)), mul_assoc,
            ← tsum_mul_left]
          exact congrArg _ (tsum_congr fun w => hFuwEq (u, w))
    _ = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' w : ℤ, cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
                * ((w : ℂ) + Complex.I * b₁) ^ 2)
              * ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                  * ∑' w', dualTerm S t (β' w) w') := by
        rw [hFuwcomm]
        exact congrArg _ (tsum_congr fun w => by
          simp only [Fuw]; rw [tsum_mul_left]
          exact congrArg _ (IH S hSpd ht (β' w)))
    _ = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
          * ∑' w : ℤ, ∑' w' : Fin m → ℤ, RB (e.symm (w', w)) := by
        have hperm : ∀ w : ℤ,
            cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
                * ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                    * ∑' w', dualTerm S t (β' w) w')
              = (((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                * ∑' w', RB (e.symm (w', w)) := fun w => by
          rw [← mul_assoc,
            mul_comm _ ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)), mul_assoc,
            ← tsum_mul_left]
          exact congrArg _ (tsum_congr fun w' => (hDualSplit w' w).symm)
        rw [tsum_congr hperm, tsum_mul_left, ← mul_assoc, hpref]
    _ = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) * ∑' w, RB w := by
        rw [← hRHScomm, ← hRHSsum.tsum_prod, e.symm.tsum_eq]

end InductionStep

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

/-- For `A` on `Fin (m + 1)`, `PoissonLaw A t b` holds if and only if `PoissonLawBlock` holds for
`A` reindexed along `finSumFinEquiv.symm` and `b ∘ finSumFinEquiv`. -/
lemma gapsw80_t2_poissonLaw_reindex {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (t : ℝ) (b : Fin (m + 1) → ℂ) :
    PoissonLaw A t b ↔
      PoissonLawBlock (reindex finSumFinEquiv.symm finSumFinEquiv.symm A) t
        (b ∘ finSumFinEquiv) := by
  set eF : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  set M := reindex eF.symm eF.symm A with hM
  set ePi : (Fin (m + 1) → ℤ) ≃ ((Fin m ⊕ Fin 1) → ℤ) :=
    ⟨fun w => w ∘ eF, fun v => v ∘ eF.symm,
      fun w => funext fun j => congrArg w (eF.apply_symm_apply j),
      fun v => funext fun i => congrArg v (eF.symm_apply_apply i)⟩
  have hMentry : ∀ i j, M i j = A (eF i) (eF j) := fun i j => by
    simp only [hM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  have hdet : M.det = A.det := Matrix.det_reindex_self _ _
  have hMinv : ∀ i j, M⁻¹ i j = A⁻¹ (eF i) (eF j) := fun i j => by
    rw [hM, Matrix.inv_reindex]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  have hQeq : ∀ v : Fin (m + 1) → ℤ,
      rQuad A (zcastR v)
        = (fun i => ((ePi v) i : ℝ)) ⬝ᵥ (M *ᵥ fun i => ((ePi v) i : ℝ)) := fun v => by
    simp only [rQuad, zcastR, dotProduct, Matrix.mulVec, ePi, Equiv.coe_fn_mk,
      Function.comp_apply, hMentry]
    exact (Fintype.sum_equiv eF _ _ fun i => by
      exact congrArg _ (Fintype.sum_equiv eF _ _ fun i' => rfl)).symm
  have hLeq : ∀ v : Fin (m + 1) → ℤ,
      (∑ j, b j * (v j : ℂ)) = ∑ i, (b ∘ eF) i * ((ePi v) i : ℂ) := fun v =>
    (Fintype.sum_equiv eF _ _ fun i => rfl).symm
  have hDeq : ∀ w : Fin (m + 1) → ℤ,
      cQuad (liftC A⁻¹) (fun j => (w j : ℂ) + Complex.I * b j)
        = (fun i => ((ePi w) i : ℂ) + Complex.I * (b ∘ eF) i)
          ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
            *ᵥ fun i => ((ePi w) i : ℂ) + Complex.I * (b ∘ eF) i) := fun w => by
    simp only [cQuad, liftC, dotProduct, Matrix.mulVec, Matrix.map_apply, ePi,
      Equiv.coe_fn_mk, Function.comp_apply, hMinv]
    refine (Fintype.sum_equiv eF _ _ fun i => ?_).symm
    exact congrArg _ (Fintype.sum_equiv eF _ _ fun i' => rfl)
  have hLHSeq : (∑' v, thetaTerm A t b v)
      = ∑' x : (Fin m ⊕ Fin 1) → ℤ,
        cexp (-(π : ℂ) * t
            * (((fun i => (x i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (x i : ℝ)) : ℝ) : ℂ)
          + 2 * π * ∑ i, (b ∘ eF) i * (x i : ℂ)) := by
    rw [← ePi.tsum_eq]
    exact tsum_congr fun v => by unfold thetaTerm; rw [hQeq v, hLeq v]
  have hRHSeq : (∑' w, dualTerm A t b w)
      = ∑' x : (Fin m ⊕ Fin 1) → ℤ,
        cexp (-(π : ℂ) / t
            * ((fun i => (x i : ℂ) + Complex.I * (b ∘ eF) i)
              ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
                *ᵥ fun i => (x i : ℂ) + Complex.I * (b ∘ eF) i))) := by
    rw [← ePi.tsum_eq]
    exact tsum_congr fun w => by unfold dualTerm; rw [hDeq w]
  unfold PoissonLaw PoissonLawBlock
  rw [hLHSeq, hRHSeq, hdet]

/-- For every `n`, positive definite real `A : Matrix (Fin n) (Fin n) ℝ`, `t > 0` and
`b : Fin n → ℂ`, `PoissonLaw A t b` holds. -/
theorem gapsw80_t2_rankNGaussianPoisson :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef →
      ∀ {t : ℝ}, 0 < t → ∀ b : Fin n → ℂ, PoissonLaw A t b := by
  intro n
  induction n with
  | zero =>
    intro A hA t ht b
    unfold PoissonLaw thetaTerm dualTerm rQuad cQuad
    simp only [dotProduct, Matrix.mulVec, Finset.univ_eq_empty, Finset.sum_empty,
      Complex.ofReal_zero, mul_zero, add_zero, Complex.exp_zero, pow_zero,
      one_mul, Matrix.det_fin_zero, Complex.ofReal_one, Complex.one_cpow]
  | succ m IH =>
    intro A hA t ht b
    rw [gapsw80_t2_poissonLaw_reindex]
    refine gapsw80_t2_poisson_step IH _ ?_ ht _
    have hAT : Aᵀ = A := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA.1
    refine (posDef_iff_dotProduct_mulVec).mpr ⟨?_, ?_⟩
    · show _ = _
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
        Equiv.symm_symm,
        ← congrFun (congrFun hAT (finSumFinEquiv i)) (finSumFinEquiv j)]
    · intro x hx
      have hxe : (fun j => x (finSumFinEquiv.symm j)) ≠ 0 := fun h =>
        hx (funext fun i => by
          have := congrFun h (finSumFinEquiv i); simpa using this)
      have key := (posDef_iff_dotProduct_mulVec.mp hA).2 hxe
      refine lt_of_lt_of_eq key ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
        Matrix.submatrix_apply, star_trivial, Equiv.symm_symm]
      refine Fintype.sum_equiv finSumFinEquiv.symm _ _ fun j => ?_
      simp only [Equiv.apply_symm_apply]
      exact congrArg _ (Fintype.sum_equiv finSumFinEquiv.symm _ _ fun j' => by
        simp only [Equiv.apply_symm_apply])

/-- For a positive definite real `A` and `t > 0`, $\sum_{v \in \mathbb Z^n} e^{-\pi t v^T A v}$
equals $(t^n \det A)^{-1/2} \sum_{w \in \mathbb Z^n} e^{-\pi w^T A^{-1} w / t}$. -/
theorem gapsw80_t2_rankNGaussianPoisson_real
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) {t : ℝ} (ht : 0 < t) :
    (∑' v : Fin n → ℤ,
        cexp ((-(π * t * (zcastR v ⬝ᵥ A *ᵥ zcastR v)) : ℝ) : ℂ))
      = (((t ^ n * A.det) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∑' w : Fin n → ℤ,
          cexp ((-(π * (zcastR w ⬝ᵥ A⁻¹ *ᵥ zcastR w) / t) : ℝ) : ℂ) := by
  have h := gapsw80_t2_rankNGaussianPoisson n A hA ht (fun _ => 0)
  have hpos : (0 : ℝ) < t ^ n * A.det := mul_pos (pow_pos ht n) hA.det_pos
  have hpref : (((t ^ n * A.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
      = (((t ^ n * A.det) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    rw [show (-(1 / 2) : ℂ) = (((-(1 / 2) : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hpos.le]
  have hθ0 : ∀ v, thetaTerm A t (fun _ => 0) v
      = cexp ((-(π * t * (zcastR v ⬝ᵥ A *ᵥ zcastR v)) : ℝ) : ℂ) := fun v => by
    unfold thetaTerm rQuad
    simp only [zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
    push_cast; ring_nf
  have hδ0 : ∀ w, dualTerm A t (fun _ => 0) w
      = cexp ((-(π * (zcastR w ⬝ᵥ A⁻¹ *ᵥ zcastR w) / t) : ℝ) : ℂ) := fun w => by
    unfold dualTerm cQuad liftC
    simp only [mul_zero, add_zero]
    congr 1
    have hQ : (fun i => (w i : ℂ)) ⬝ᵥ ((A⁻¹).map ((↑) : ℝ → ℂ) *ᵥ fun i => (w i : ℂ))
        = (((zcastR w ⬝ᵥ A⁻¹ *ᵥ zcastR w : ℝ)) : ℂ) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, zcastR,
        Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [hQ]; push_cast; ring
  unfold PoissonLaw at h
  rw [tsum_congr hθ0, tsum_congr hδ0, hpref] at h
  exact h

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

end FLT.Gapsw80T2RankNGaussianPoisson

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

section

noncomputable section

namespace FLT

namespace Gapsw80T4MultiVarIdealThetaTransformation

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"

open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation

p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

/-- The map sending an index of the standard basis of the mixed space of `K` to the infinite place
of `K` it belongs to, for the real index `inl w` giving `w` and each complex index `inr (w, j)`
giving `w`. -/
def gapsw80_t4_placeOf : index K → InfinitePlace K :=
  Sum.elim (fun w => (w : InfinitePlace K)) (fun p => (p.1 : InfinitePlace K))

omit [NumberField K] in
/-- `gapsw80_t4_placeOf K (Sum.inl w)` equals the underlying infinite place `w` of the real place
`w`. -/
@[scoped simp] theorem placeOf_inl (w : {w : InfinitePlace K // IsReal w}) :
    gapsw80_t4_placeOf K (Sum.inl w) = (w : InfinitePlace K) := rfl

omit [NumberField K] in
/-- `gapsw80_t4_placeOf K (Sum.inr p)` equals the underlying complex infinite place `p.1`. -/
@[scoped simp] theorem placeOf_inr (p : {w : InfinitePlace K // IsComplex w} × Fin 2) :
    gapsw80_t4_placeOf K (Sum.inr p) = (p.1 : InfinitePlace K) := rfl

/-- For `y : InfinitePlace K → ℝ`, the diagonal `nK K × nK K` real matrix whose `i`-th diagonal
entry is `y` at the place of the index `(eIdx K).symm i`. -/
def gapsw80_t4_Dscale (y : InfinitePlace K → ℝ) : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.diagonal fun i => y (gapsw80_t4_placeOf K ((eIdx K).symm i))

/-- If `y w > 0` for all infinite places `w`, then `gapsw80_t4_Dscale K y` is positive definite. -/
theorem Dscale_posDef {y : InfinitePlace K → ℝ} (hy : ∀ w, 0 < y w) :
    (gapsw80_t4_Dscale K y).PosDef :=
  Matrix.PosDef.diagonal fun _ => hy _

/-- For a real infinite place `w`, the set of indices lying over `w` is the singleton
`{Sum.inl ⟨w, hw⟩}`. -/
theorem fiber_placeOf_isReal {w : InfinitePlace K} (hw : IsReal w) :
    (Finset.univ.filter fun j => gapsw80_t4_placeOf K j = w)
      = {Sum.inl ⟨w, hw⟩} := by
  ext j
  rcases j with ⟨v, hv⟩ | ⟨⟨v, hv⟩, k⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inl,
      Finset.mem_singleton, Sum.inl.injEq, Subtype.mk.injEq]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inr, Finset.mem_singleton]
    exact iff_of_false (fun h => (not_isReal_iff_isComplex.mpr hv) (h ▸ hw)) (by simp)

/-- For a complex infinite place `w`, the set of indices lying over `w` is the two-element set
`{Sum.inr (⟨w, hw⟩, 0), Sum.inr (⟨w, hw⟩, 1)}`. -/
theorem fiber_placeOf_isComplex {w : InfinitePlace K} (hw : IsComplex w) :
    (Finset.univ.filter fun j => gapsw80_t4_placeOf K j = w)
      = {Sum.inr (⟨w, hw⟩, 0), Sum.inr (⟨w, hw⟩, 1)} := by
  ext j
  rcases j with ⟨v, hv⟩ | ⟨⟨v, hv⟩, k⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inl,
      Finset.mem_insert, Finset.mem_singleton]
    exact iff_of_false (fun h => (not_isComplex_iff_isReal.mpr hv) (h ▸ hw)) (by simp)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inr,
      Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq, Prod.mk.injEq,
      Subtype.mk.injEq]
    constructor
    · rintro rfl; fin_cases k <;> simp
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl

/-- The determinant of `gapsw80_t4_Dscale K y` equals $\prod_w y(w)^{\text{mult}(w)}$ over the
infinite places `w`. -/
theorem gapsw80_t4_det_Dscale (y : InfinitePlace K → ℝ) :
    (gapsw80_t4_Dscale K y).det = ∏ w : InfinitePlace K, y w ^ mult w := by
  rw [gapsw80_t4_Dscale, Matrix.det_diagonal,
    Fintype.prod_equiv (eIdx K).symm _ (fun j => y (gapsw80_t4_placeOf K j))
      (fun i => by simp),
    ← Finset.prod_fiberwise Finset.univ (fun j => gapsw80_t4_placeOf K j)
      (fun j => y (gapsw80_t4_placeOf K j))]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Finset.prod_eq_pow_card fun j hj => by
      rw [Finset.mem_filter] at hj; rw [hj.2]]
  congr 1
  rcases isReal_or_isComplex w with hw | hw
  · rw [mult, ite_eq_left hw, fiber_placeOf_isReal K hw, Finset.card_singleton]
  · rw [mult, ite_eq_right (not_isReal_iff_isComplex.mpr hw), fiber_placeOf_isComplex K hw,
      Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- For `y : InfinitePlace K → ℝ`, the real matrix
`(coordMatrix K I)ᵀ * gapsw80_t4_Dscale K y * coordMatrix K I`. -/
def gapsw80_t4_scaledGram (y : InfinitePlace K → ℝ) :
    Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  (coordMatrix K I)ᵀ * gapsw80_t4_Dscale K y * coordMatrix K I

/-- The determinant of `coordMatrix K I` is nonzero. -/
theorem det_coordMatrix_ne_zero : (coordMatrix K I).det ≠ 0 := fun h =>
  (ZLattice.covolume_pos (mixedEmbedding.idealLattice K I) MeasureTheory.volume).ne'
    ((abs_det_coordMatrix K I).symm.trans (by rw [h, abs_zero]))

/-- The matrix `coordMatrix K I` is a unit (invertible). -/
theorem isUnit_coordMatrix : IsUnit (coordMatrix K I) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_coordMatrix_ne_zero K I))

/-- If `y w > 0` for all infinite places `w`, then `gapsw80_t4_scaledGram K I y` is positive
definite. -/
theorem gapsw80_t4_scaledGram_posDef {y : InfinitePlace K → ℝ} (hy : ∀ w, 0 < y w) :
    (gapsw80_t4_scaledGram K I y).PosDef := by
  have h := (Dscale_posDef K hy).conjTranspose_mul_mul_same (B := coordMatrix K I)
    (Matrix.mulVec_injective_of_isUnit (isUnit_coordMatrix K I))
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The determinant of `gapsw80_t4_scaledGram K I y` equals $\prod_w y(w)^{\text{mult}(w)}$ times
the square of the covolume of the ideal lattice `mixedEmbedding.idealLattice K I`. -/
theorem gapsw80_t4_det_scaledGram (y : InfinitePlace K → ℝ) :
    (gapsw80_t4_scaledGram K I y).det
      = (∏ w : InfinitePlace K, y w ^ mult w)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2 := by
  rw [gapsw80_t4_scaledGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    gapsw80_t4_det_Dscale, mul_comm (coordMatrix K I).det, mul_assoc, ← sq, ← sq_abs,
    abs_det_coordMatrix]

/-- For `x` in the mixed space and an infinite place `w`, the sum of the squared standard-basis
coordinates of `x` over the indices lying over `w` equals `normAtPlace w x ^ 2`. -/
theorem sum_sq_repr_fiber_eq_normAtPlace_sq (x : mixedSpace K) (w : InfinitePlace K) :
    ∑ j ∈ Finset.univ.filter (fun j => gapsw80_t4_placeOf K j = w),
        ((mixedEmbedding.stdBasis K).repr x j) ^ 2
      = normAtPlace w x ^ 2 := by
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw, fiber_placeOf_isReal K hw, Finset.sum_singleton,
      stdBasis_apply_isReal, Real.norm_eq_abs, sq_abs]
  · rw [normAtPlace_apply_of_isComplex hw, fiber_placeOf_isComplex K hw,
      Finset.sum_insert (by simp), Finset.sum_singleton,
      stdBasis_apply_isComplex_fst, stdBasis_apply_isComplex_snd,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring

/-- For `v : Fin (nK K) → ℤ`, the `i`-th entry of `coordMatrix K I *ᵥ zcastR v` equals the
standard-basis coordinate of `zEquiv K I v` at the index `(eIdx K).symm i`. -/
theorem coordMatrix_mulVec_eq_repr (v : Fin (nK K) → ℤ) (i : Fin (nK K)) :
    ((coordMatrix K I) *ᵥ zcastR v) i
      = (mixedEmbedding.stdBasis K).repr (zEquiv K I v : mixedSpace K) ((eIdx K).symm i) := by

  have hRHS : (mixedEmbedding.stdBasis K).repr (zEquiv K I v : mixedSpace K) ((eIdx K).symm i)
      = ∑ j, (v j : ℝ) * (stdBasisFin K).repr
          (fractionalIdealLatticeBasis K I ((eI K I).symm j)) i := by
    rw [show (mixedEmbedding.stdBasis K).repr (zEquiv K I v : mixedSpace K) ((eIdx K).symm i)
          = (stdBasisFin K).repr (zEquiv K I v : mixedSpace K) i by
        simp only [stdBasisFin, Basis.repr_reindex_apply],
      coe_zEquiv_apply, map_sum]
    simp only [map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hRHS, coordMatrix_eq_toMatrix, Matrix.mulVec]
  simp only [dotProduct, Basis.toMatrix_apply, idealZBasis_apply, zcastR]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- For `v : Fin (nK K) → ℤ`, the quadratic form of `gapsw80_t4_scaledGram K I y` at `zcastR v`
equals $\sum_w y(w)\,\|\,\text{zEquiv}(v)\|_w^2$ over the infinite places `w`. -/
theorem gapsw80_t4_quadForm_scaledGram (y : InfinitePlace K → ℝ) (v : Fin (nK K) → ℤ) :
    zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v
      = ∑ w : InfinitePlace K, y w * normAtPlace w (zEquiv K I v : mixedSpace K) ^ 2 := by

  have hstep1 : zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v
      = ((coordMatrix K I) *ᵥ zcastR v) ⬝ᵥ
          (gapsw80_t4_Dscale K y) *ᵥ ((coordMatrix K I) *ᵥ zcastR v) := by
    rw [gapsw80_t4_scaledGram, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (zcastR v) (coordMatrix K I)ᵀ,
      Matrix.vecMul_transpose]

  rw [hstep1]
  have hstep2 : ∀ u : Fin (nK K) → ℝ, u ⬝ᵥ (gapsw80_t4_Dscale K y) *ᵥ u
      = ∑ i, y (gapsw80_t4_placeOf K ((eIdx K).symm i)) * u i ^ 2 := fun u => by
    simp only [dotProduct, gapsw80_t4_Dscale, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hstep2,
    Fintype.sum_equiv (eIdx K).symm _
      (fun j => y (gapsw80_t4_placeOf K j)
        * ((mixedEmbedding.stdBasis K).repr (zEquiv K I v : mixedSpace K) j) ^ 2)
      (fun i => by rw [coordMatrix_mulVec_eq_repr K I v i]),
    ← Finset.sum_fiberwise Finset.univ (fun j => gapsw80_t4_placeOf K j)
      (fun j => y (gapsw80_t4_placeOf K j)
        * ((mixedEmbedding.stdBasis K).repr (zEquiv K I v : mixedSpace K) j) ^ 2)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← sum_sq_repr_fiber_eq_normAtPlace_sq K (zEquiv K I v : mixedSpace K) w,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j hj => by
    rw [Finset.mem_filter] at hj; rw [hj.2]

/-- The theta series $\sum_{v\in\mathbb Z^{n}}\exp(-\pi\, v^T G_y v)$ where `G_y` is
`gapsw80_t4_scaledGram K I y`, with one scaling parameter `y w` for each infinite place `w`. -/
def gapsw80_t4_multiIdealTheta (y : InfinitePlace K → ℝ) : ℂ :=
  ∑' v : Fin (nK K) → ℤ, cexp ((-(π *
    (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ)

/-- `gapsw80_t4_multiIdealTheta K I y` equals $\sum_{x\in I}\exp(-\pi\sum_w y(w)\,\|x\|_w^2)$,
summed over the ideal lattice `mixedEmbedding.idealLattice K I`. -/
theorem gapsw80_t4_multiIdealTheta_eq_latticeSum (y : InfinitePlace K → ℝ) :
    gapsw80_t4_multiIdealTheta K I y
      = ∑' x : mixedEmbedding.idealLattice K I,
          cexp ((-(π *
            ∑ w : InfinitePlace K, y w * normAtPlace w (x : mixedSpace K) ^ 2) : ℝ) : ℂ) := by
  unfold gapsw80_t4_multiIdealTheta
  rw [← (zEquiv K I).toEquiv.tsum_eq]
  exact tsum_congr fun v => by rw [gapsw80_t4_quadForm_scaledGram]; rfl

/-- For `t : ℝ`, `gapsw80_t4_scaledGram K I (fun _ => t)` equals `t • gapsw80_t3_idealGram K I`. -/
theorem gapsw80_t4_scaledGram_const_eq (t : ℝ) :
    gapsw80_t4_scaledGram K I (fun _ => t) = t • gapsw80_t3_idealGram K I := by
  have hD : gapsw80_t4_Dscale K (fun _ => t) = Matrix.diagonal (fun _ => t) := rfl
  rw [gapsw80_t4_scaledGram, gapsw80_t3_idealGram_eq_transpose_mul, hD,
    show (Matrix.diagonal (fun _ : Fin (nK K) => t) : Matrix _ _ ℝ) = t • 1 by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h],
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- If `y w > 0` for all infinite places `w`, then `gapsw80_t4_multiIdealTheta K I y` equals
$(\prod_w y(w)^{\text{mult}(w)}\cdot \text{covol}^2)^{-1/2}$ times
$\sum_{w\in\mathbb Z^n}\exp(-\pi\, w^T G_y^{-1} w)$, where `G_y` is `gapsw80_t4_scaledGram K I y`
and covol is the covolume of the ideal lattice. -/
theorem gapsw80_t4_multiIdealTheta_transformation {y : InfinitePlace K → ℝ}
    (hy : ∀ w, 0 < y w) :
    gapsw80_t4_multiIdealTheta K I y
      = ((((∏ w : InfinitePlace K, y w ^ mult w)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∑' w : Fin (nK K) → ℤ,
          cexp ((-(π *
            (zcastR w ⬝ᵥ (gapsw80_t4_scaledGram K I y)⁻¹ *ᵥ zcastR w)) : ℝ) : ℂ) := by
  have h := gapsw80_t2_rankNGaussianPoisson_real (gapsw80_t4_scaledGram K I y)
    (gapsw80_t4_scaledGram_posDef K I hy) one_pos
  rw [gapsw80_t4_det_scaledGram, one_pow, one_mul] at h
  simp only [mul_one, div_one] at h
  exact h

/-- If `y w > 0` for all `w`, the inverse of `gapsw80_t4_scaledGram K I y` equals
`(coordMatrix K I)⁻¹ * gapsw80_t4_Dscale K (fun w => (y w)⁻¹) * ((coordMatrix K I)ᵀ)⁻¹`. -/
theorem gapsw80_t4_scaledGram_inv_eq {y : InfinitePlace K → ℝ} (hy : ∀ w, 0 < y w) :
    (gapsw80_t4_scaledGram K I y)⁻¹
      = (coordMatrix K I)⁻¹ * gapsw80_t4_Dscale K (fun w => (y w)⁻¹)
          * ((coordMatrix K I)ᵀ)⁻¹ := by
  have hD : gapsw80_t4_Dscale K (fun w => (y w)⁻¹) = (gapsw80_t4_Dscale K y)⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [show gapsw80_t4_Dscale K y
          = Matrix.diagonal fun i => y (gapsw80_t4_placeOf K ((eIdx K).symm i)) from rfl,
      show gapsw80_t4_Dscale K (fun w => (y w)⁻¹)
          = Matrix.diagonal fun i => (y (gapsw80_t4_placeOf K ((eIdx K).symm i)))⁻¹ from rfl,
      Matrix.diagonal_mul_diagonal, show (1 : Matrix (Fin (nK K)) (Fin (nK K)) ℝ)
          = Matrix.diagonal 1 from (Matrix.diagonal_one).symm]
    exact Matrix.diagonal_eq_diagonal_iff.mpr fun i => mul_inv_cancel₀ (hy _).ne'
  rw [hD, gapsw80_t4_scaledGram, Matrix.mul_assoc, Matrix.mul_inv_rev, Matrix.mul_inv_rev]

end FLT.Gapsw80T4MultiVarIdealThetaTransformation

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation"

