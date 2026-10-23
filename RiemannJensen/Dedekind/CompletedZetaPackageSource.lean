module

public import RiemannJensen.Dedekind.CompletedZetaPartialZeta

/-!
# The completed Dedekind zeta function

For a number field `K`, the completed Dedekind zeta function
$\Lambda_K(s) = |d_K|^{s/2} \Gamma_\mathbb{R}(s)^{r_1} \Gamma_\mathbb{C}(s)^{r_2} \zeta_K(s)$
extends holomorphically to `ℂ \ {0, 1}` and satisfies $\Lambda_K(1 - s) = \Lambda_K(s)$. The
entire function $\xi_K(s) = s(s - 1)\Lambda_K(s)$ has order at most one, does not vanish at `0`
and `1`, and has order exactly one in the sense that $\log |\xi_K(s)|$ is not $O(|s|)$.

The functional equation comes from summing the per-class functional equations of the partial zeta
functions (`RiemannJensen.Dedekind.CompletedZetaPartialZeta`) over the class group.

## Main results

* `solution`: the analytic continuation, functional equation and order properties of the
  completed Dedekind zeta function.
-/

@[expose] public section

namespace P2MW.S_NumberField_exists_completedDedekindZeta_package

set_option autoImplicit false

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

section

namespace FLT

namespace Gapsw80T9ClassSumA1Closure

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"

open FLT.Gapsw80T3IdealLatticeThetaTransformation FLT.Gapsw80T5HeckeThetaKernel
open FLT.Gapsw80T6TraceDualBridge FLT.Gapsw80T7ClosedFEWeakPair
open FLT.Gapsw80T8MellinGammaPartialZeta

p2m_open "Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K]

/-- The constant `torsionOrder K / (2^(r₁+r₂-1) * nK K * regulator K)` in `ℂ`, where `r₁` and `r₂`
are the numbers of real and complex places. -/
noncomputable def gapsw80_t9_constK : ℂ :=
  (torsionOrder K : ℂ)
    / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) * (nK K : ℂ) * (regulator K : ℂ))

/-- `gapsw80_t9_constK K` equals
`torsionOrder K / (2^(nrRealPlaces K + nrComplexPlaces K - 1) * nK K * regulator K)`. -/
theorem gapsw80_t9_constK_def :
    gapsw80_t9_constK K = (torsionOrder K : ℂ)
      / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1)
          * (nK K : ℂ) * (regulator K : ℂ)) := rfl

/-- The constant `gapsw80_t9_constK K` is nonzero. -/
theorem gapsw80_t9_constK_ne_zero : gapsw80_t9_constK K ≠ 0 := by
  refine div_ne_zero ?_ (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · exact_mod_cast (torsionOrder_pos K).ne'
  · exact pow_ne_zero _ two_ne_zero
  · exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  · exact Complex.ofReal_ne_zero.mpr (regulator_pos K).ne'

/-- For an ideal class `C`, the fractional ideal given by the inverse of `FractionalIdeal.mk0` of a
chosen integral ideal whose class is `C`. -/
noncomputable def gapsw80_t9_classRepr (C : ClassGroup (𝓞 K)) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (FractionalIdeal.mk0 K (ClassGroup.mk0_surjective C).choose)⁻¹

/-- The class of `gapsw80_t9_classRepr K C` in the class group is `C⁻¹`. -/
theorem gapsw80_t9_mk_classRepr (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (gapsw80_t9_classRepr K C) = C⁻¹ := by
  unfold gapsw80_t9_classRepr
  rw [map_inv, ClassGroup.mk_mk0, (ClassGroup.mk0_surjective C).choose_spec]

/-- The covolume of the ideal lattice of `gapsw80_t9_classRepr K C` in the mixed space. -/
noncomputable abbrev gapsw80_t9_covolRepr (C : ClassGroup (𝓞 K)) : ℝ :=
  ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t9_classRepr K C))

/-- For every ideal class `C`, `0 < gapsw80_t9_covolRepr K C`. -/
theorem gapsw80_t9_covolRepr_pos (C : ClassGroup (𝓞 K)) :
    0 < gapsw80_t9_covolRepr K C := gapsw80_t7_covol_pos K _

/-- The completed Dedekind zeta function of `K`: `(gapsw80_t9_constK K)⁻¹` times the sum over ideal
classes `C` of $r_C^s \Lambda_C(n s / 2)$, where `r_C = gapsw80_t9_covolRepr K C` and `Λ_C` is the
completed Mellin transform of `gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)`. -/
noncomputable def gapsw80_t9_completedDedekindZeta (s : ℂ) : ℂ :=
  (gapsw80_t9_constK K)⁻¹
    * ∑ C : ClassGroup (𝓞 K),
        ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
          * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ ((nK K : ℂ) * s / 2)

/-- The gamma factor `Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K`. -/
noncomputable abbrev gapsw80_t9_gammaFactor (s : ℂ) : ℂ :=
  Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K

/-- For every `s`, `nK K * (1 - s) / 2 = nK K / 2 - nK K * s / 2` in `ℂ`. -/
theorem gapsw80_t9_sigma_one_sub (s : ℂ) :
    (nK K : ℂ) * (1 - s) / 2
      = (((nK K : ℝ) / 2 : ℝ) : ℂ) - (nK K : ℂ) * s / 2 := by
  push_cast; ring

/-- For every ideal `I` and `s`,
`covol(idealLattice K I)^(1-s) * (gapsw80_t7_heckeWeakFEPair K I).Λ (nK K * (1 - s) / 2)` equals
`covol(idealLattice K I)^(-s) * (gapsw80_t7_heckeWeakFEPair K I).symm.Λ (nK K * s / 2)`. -/
theorem gapsw80_t9_perClass_FE_step (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (1 - s)
        * (gapsw80_t7_heckeWeakFEPair K I).Λ ((nK K : ℂ) * (1 - s) / 2)
      = ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * (gapsw80_t7_heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2) := by
  have hFE := (gapsw80_t7_heckeWeakFEPair K I).functional_equation ((nK K : ℂ) * s / 2)
  have hk : (gapsw80_t7_heckeWeakFEPair K I).k = (nK K : ℝ) / 2 := rfl
  have hε : (gapsw80_t7_heckeWeakFEPair K I).ε
      = ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℂ))⁻¹ := rfl
  rw [hk, hε, smul_eq_mul] at hFE
  have hcov : ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (gapsw80_t7_covol_pos K I).ne'
  rw [gapsw80_t9_sigma_one_sub, hFE, ← mul_assoc]
  congr 1
  rw [show (1:ℂ) - s = (-s) + 1 from by ring, Complex.cpow_add _ _ hcov, Complex.cpow_one,
    mul_assoc, mul_inv_cancel₀ hcov, mul_one]

/-- For every `s`, `4^(-r₂ * s) * ((4⁻¹)^r₂)^(-s) = 1`, where `r₂ = nrComplexPlaces K`. -/
theorem gapsw80_t9_four_cpow_cancel (s : ℂ) :
    ((4:ℝ) : ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
        * (((4:ℝ)⁻¹ ^ nrComplexPlaces K : ℝ) : ℂ) ^ (-s)
      = 1 := by
  have h4 : ((4:ℝ):ℂ) ≠ 0 := by norm_num
  have harg : Complex.arg ((4:ℝ):ℂ) = 0 :=
    Complex.arg_ofReal_of_nonneg (by norm_num)
  have harg' : Complex.arg (((4:ℝ):ℂ)^nrComplexPlaces K) ≠ Real.pi := by
    rw [show ((4:ℝ):ℂ) ^ nrComplexPlaces K = ((4 ^ nrComplexPlaces K : ℝ) : ℂ) from
      by push_cast; ring,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm

  have hinv : (((4:ℝ)⁻¹^nrComplexPlaces K : ℝ):ℂ) = (((4:ℝ):ℂ)^nrComplexPlaces K)⁻¹ := by
    rw [inv_pow]; push_cast; ring
  rw [hinv, Complex.inv_cpow _ _ harg',
    ← Complex.cpow_nat_mul' (x := ((4:ℝ):ℂ))
      (by rw [harg, mul_zero]; linarith [Real.pi_pos])
      (by rw [harg, mul_zero]; exact Real.pi_pos.le) (-s),
    ← Complex.cpow_neg, ← Complex.cpow_add _ _ h4]
  convert Complex.cpow_zero _ using 2
  ring

/-- For every ideal `I` and `s`,
$\operatorname{covol}(I)^{-s} \cdot 4^{-r_2 s} \operatorname{covol}(I^\vee)^{-s} = 1$, where `I^∨`
is the trace-dual ideal of `I` and `r₂ = nrComplexPlaces K`. -/
theorem gapsw80_t9_covol_cancel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * (((4:ℝ) : ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
          * ((ZLattice.covolume (mixedEmbedding.idealLattice K
              (gapsw80_t6_traceDualIdeal K I)) : ℝ) : ℂ) ^ (-s))
      = 1 := by
  have hI := (gapsw80_t7_covol_pos K I).le
  have hJ := (gapsw80_t7_covol_pos K (gapsw80_t6_traceDualIdeal K I)).le
  rw [show ∀ a b c : ℂ, a*(b*c) = b*(a*c) from fun a b c => by ring,
    ← Complex.mul_cpow_ofReal_nonneg hI hJ, ← Complex.ofReal_mul,
    gapsw80_t8_sat_covol_prod]
  exact gapsw80_t9_four_cpow_cancel K s

/-- For `1 < s.re`, $\operatorname{covol}(I)^{-s} \Lambda^\vee_I(n s / 2)$, where `Λ^∨_I` is the
completed Mellin transform of `(gapsw80_t7_heckeWeakFEPair K I).symm`, equals
`gapsw80_t9_constK K * |discr K| ^ (s / 2) * gapsw80_t9_gammaFactor K s` times the partial Dedekind
zeta function of the class `(ClassGroup.mk K I^∨)⁻¹` at `s`, `I^∨` being the trace-dual ideal of
`I`. -/
theorem gapsw80_t9_perClass_identified (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * (gapsw80_t7_heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2)
      = gapsw80_t9_constK K
        * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gapsw80_t9_gammaFactor K s
        * gapsw80_t8_partialDedekindZeta K
            (ClassGroup.mk K (gapsw80_t6_traceDualIdeal K I))⁻¹ s := by
  rw [gapsw80_t8_symmLambda_eq_completedPartialZeta K I hs, ← gapsw80_t9_constK_def]
  linear_combination
    (gapsw80_t9_constK K * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
      * gapsw80_t9_gammaFactor K s
      * gapsw80_t8_partialDedekindZeta K
          (ClassGroup.mk K (gapsw80_t6_traceDualIdeal K I))⁻¹ s)
    * gapsw80_t9_covol_cancel K I s

/-- The different ideal of `𝓞 K` over `ℤ`, regarded as an element of the nonzero-divisor ideals
`(Ideal (𝓞 K))⁰`. -/
noncomputable def gapsw80_t9_diffIdeal : (Ideal (𝓞 K))⁰ :=
  ⟨differentIdeal ℤ (𝓞 K), mem_nonZeroDivisors_iff_ne_zero.mpr differentIdeal_ne_bot⟩

/-- The ideal class of the different ideal of `𝓞 K`. -/
noncomputable def gapsw80_t9_diffClass : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 (gapsw80_t9_diffIdeal K)

/-- The trace-dual ideal of `I` equals `(FractionalIdeal.mk0 K (gapsw80_t9_diffIdeal K))⁻¹ * I⁻¹`.
-/
theorem gapsw80_t9_traceDualIdeal_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    gapsw80_t6_traceDualIdeal K I
      = (FractionalIdeal.mk0 K (gapsw80_t9_diffIdeal K))⁻¹ * I⁻¹ := by
  apply Units.ext
  rw [coe_traceDualIdeal, FractionalIdeal.dual_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0]
  congr 1
  have h := coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)
  rw [gapsw80_t9_diffIdeal, h, inv_inv]

/-- The class of the trace-dual ideal of `I` equals
`(gapsw80_t9_diffClass K)⁻¹ * (ClassGroup.mk K I)⁻¹`. -/
theorem gapsw80_t9_mk_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K (gapsw80_t6_traceDualIdeal K I)
      = (gapsw80_t9_diffClass K)⁻¹ * (ClassGroup.mk K I)⁻¹ := by
  rw [gapsw80_t9_traceDualIdeal_eq, map_mul, map_inv, map_inv, ClassGroup.mk_mk0,
    gapsw80_t9_diffClass]

/-- The self-bijection of the ideal class group sending `C` to `gapsw80_t9_diffClass K * C⁻¹`. -/
noncomputable def gapsw80_t9_classBijection : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
  (Equiv.inv (ClassGroup (𝓞 K))).trans (Equiv.mulLeft (gapsw80_t9_diffClass K))

/-- `gapsw80_t9_classBijection K C = gapsw80_t9_diffClass K * C⁻¹`. -/
theorem gapsw80_t9_classBijection_apply (C : ClassGroup (𝓞 K)) :
    gapsw80_t9_classBijection K C = gapsw80_t9_diffClass K * C⁻¹ := rfl

/-- For every `s`, the sum over ideal classes `C` of
`gapsw80_t8_partialDedekindZeta K (gapsw80_t9_diffClass K * C⁻¹) s` equals the sum over `C` of
`gapsw80_t8_partialDedekindZeta K C s`. -/
theorem gapsw80_t9_sum_bijection_partialZeta (s : ℂ) :
    ∑ C : ClassGroup (𝓞 K),
        gapsw80_t8_partialDedekindZeta K (gapsw80_t9_diffClass K * C⁻¹) s
      = ∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s :=
  Finset.sum_equiv (gapsw80_t9_classBijection K) (fun _ => by simp)
    (fun C _ => by rw [gapsw80_t9_classBijection_apply])

/-- For `1 < s.re`, `gapsw80_t9_completedDedekindZeta K s` equals
`|discr K|^(s/2) * gapsw80_t9_gammaFactor K s` times the sum over ideal classes `C` of
`gapsw80_t8_partialDedekindZeta K C s`. -/
theorem gapsw80_t9_completedDedekindZeta_eq_sum {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K s
      = ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gapsw80_t9_gammaFactor K s
        * ∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s := by
  unfold gapsw80_t9_completedDedekindZeta gapsw80_t9_covolRepr gapsw80_t9_gammaFactor
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [gapsw80_t8_heckeLambda_eq_completedPartialZeta K (gapsw80_t9_classRepr K C) hs,
    gapsw80_t9_mk_classRepr, inv_inv, ← gapsw80_t9_constK_def]
  set cov : ℂ := ((ZLattice.covolume
      (mixedEmbedding.idealLattice K (gapsw80_t9_classRepr K C)) : ℝ) : ℂ)
  have hcov : cov ≠ 0 := Complex.ofReal_ne_zero.mpr (gapsw80_t7_covol_pos K _).ne'
  have key : (gapsw80_t9_constK K)⁻¹ * cov ^ s * (gapsw80_t9_constK K * cov ^ (-s)) = 1 := by
    rw [show ∀ a b c d : ℂ, a*b*(c*d) = (a*c)*(b*d) from fun a b c d => by ring,
      inv_mul_cancel₀ (gapsw80_t9_constK_ne_zero K),
      ← Complex.cpow_add _ _ hcov, add_neg_cancel, Complex.cpow_zero, one_mul]
  linear_combination
    (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K
      * Gammaℂ s ^ nrComplexPlaces K * gapsw80_t8_partialDedekindZeta K C s) * key

/-- For `1 < s.re`, `gapsw80_t9_completedDedekindZeta K (1 - s)` equals
`|discr K|^(s/2) * gapsw80_t9_gammaFactor K s` times the sum over ideal classes `C` of
`gapsw80_t8_partialDedekindZeta K C s`. -/
theorem gapsw80_t9_completedDedekindZeta_one_sub_eq_sum {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K (1 - s)
      = ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gapsw80_t9_gammaFactor K s
        * ∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s := by
  unfold gapsw80_t9_completedDedekindZeta gapsw80_t9_covolRepr
  rw [← gapsw80_t9_sum_bijection_partialZeta, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [gapsw80_t9_perClass_FE_step, gapsw80_t9_perClass_identified K _ hs,
    gapsw80_t9_mk_traceDualIdeal, gapsw80_t9_mk_classRepr, inv_inv, mul_inv, inv_inv]
  linear_combination
    (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gapsw80_t9_gammaFactor K s
      * gapsw80_t8_partialDedekindZeta K (gapsw80_t9_diffClass K * C⁻¹) s)
    * inv_mul_cancel₀ (gapsw80_t9_constK_ne_zero K)

/-- For `1 < s.re`,
`gapsw80_t9_completedDedekindZeta K (1 - s) = gapsw80_t9_completedDedekindZeta K s`. -/
theorem gapsw80_t9_FE_halfplane {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K (1 - s) = gapsw80_t9_completedDedekindZeta K s :=
  (gapsw80_t9_completedDedekindZeta_one_sub_eq_sum K hs).trans
    (gapsw80_t9_completedDedekindZeta_eq_sum K hs).symm

/-- The set `{0, 1}` in `ℂ` is closed. -/
theorem gapsw80_t9_isClosed_pair : IsClosed ({(0:ℂ), 1} : Set ℂ) :=
  ((Set.finite_singleton (1:ℂ)).insert 0).isClosed

/-- The complement of `{0, 1}` in `ℂ` is preconnected. -/
theorem gapsw80_t9_isPreconnected_compl :
    IsPreconnected ({(0:ℂ), 1}ᶜ : Set ℂ) :=
  (Set.Countable.isConnected_compl_of_one_lt_rank
    (rank_real_complex ▸ Nat.one_lt_ofNat)
    (((Set.finite_singleton (1:ℂ)).insert 0).countable)).isPreconnected

/-- `(nK K : ℂ) ≠ 0`. -/
theorem gapsw80_t9_nK_ne_zero : (nK K : ℂ) ≠ 0 := by
  exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'

/-- `gapsw80_t9_completedDedekindZeta K` is complex differentiable on `{0, 1}ᶜ`. -/
theorem gapsw80_t9_differentiableOn_completedDedekindZeta :
    DifferentiableOn ℂ (gapsw80_t9_completedDedekindZeta K) {(0:ℂ), 1}ᶜ := by
  refine (differentiableOn_const _).mul (DifferentiableOn.fun_sum (fun C _ => ?_))
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
  refine ((differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr (gapsw80_t9_covolRepr_pos K C).ne'))).mul ?_
    ).differentiableWithinAt
  refine ((gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).differentiableAt_Λ
    ?_ ?_).comp s ((differentiableAt_const _).mul differentiableAt_id |>.div_const _)
  · left
    exact fun h => hs.1 (by
      have := mul_eq_zero.mp (div_eq_zero_iff.mp h |>.resolve_right two_ne_zero)
      exact this.resolve_left (gapsw80_t9_nK_ne_zero K))
  · left
    intro h
    apply hs.2
    have hk : ((gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).k : ℂ)
        = (nK K : ℂ) / 2 := by
      change (((nK K : ℝ) / 2 : ℝ) : ℂ) = (nK K : ℂ) / 2; push_cast; ring
    rw [hk, div_eq_div_iff (two_ne_zero) (two_ne_zero)] at h
    have h' := mul_right_cancel₀ (two_ne_zero (α := ℂ)) h
    exact mul_left_cancel₀ (gapsw80_t9_nK_ne_zero K) (h'.trans (mul_one _).symm)

/-- `gapsw80_t9_completedDedekindZeta K` is analytic at every point of `{0, 1}ᶜ`. -/
theorem gapsw80_t9_analyticOnNhd_completedDedekindZeta :
    AnalyticOnNhd ℂ (gapsw80_t9_completedDedekindZeta K) {(0:ℂ), 1}ᶜ :=
  (gapsw80_t9_differentiableOn_completedDedekindZeta K).analyticOnNhd
    gapsw80_t9_isClosed_pair.isOpen_compl

/-- For `s ≠ 0` and `s ≠ 1`,
`gapsw80_t9_completedDedekindZeta K (1 - s) = gapsw80_t9_completedDedekindZeta K s`. -/
theorem gapsw80_t9_completedDedekindZeta_FE {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    gapsw80_t9_completedDedekindZeta K (1 - s) = gapsw80_t9_completedDedekindZeta K s := by
  have hAf := gapsw80_t9_analyticOnNhd_completedDedekindZeta K
  have hAg : AnalyticOnNhd ℂ
      (fun z => gapsw80_t9_completedDedekindZeta K (1 - z)) {(0:ℂ), 1}ᶜ := by
    have hswap : Set.MapsTo (fun z : ℂ => 1 - z) {(0:ℂ), 1}ᶜ {(0:ℂ), 1}ᶜ := by
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or, sub_eq_zero, sub_eq_self] at hz ⊢
      exact ⟨fun h => hz.2 h.symm, hz.1⟩
    exact fun z hz => (hAf _ (hswap hz)).comp (analyticAt_const.sub analyticAt_id)
  have hsU : s ∈ ({(0:ℂ), 1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hs0, hs1⟩
  have h2U : (2:ℂ) ∈ ({(0:ℂ), 1}ᶜ : Set ℂ) := by norm_num
  refine (hAg.eqOn_of_preconnected_of_frequently_eq hAf
    gapsw80_t9_isPreconnected_compl h2U ?_ hsU)

  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2mem : (2:ℂ) ∈ {z : ℂ | 1 < z.re} := by simp
  exact ((Filter.eventually_of_mem (hopen.mem_nhds h2mem)
    (fun z hz => gapsw80_t9_FE_halfplane K hz)).filter_mono
      nhdsWithin_le_nhds).frequently

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

end FLT.Gapsw80T9ClassSumA1Closure

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

section

namespace FLT

namespace Gapsw80T10DedekindZetaBridgeA1Discharge

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"

open FLT.Gapsw80T8MellinGammaPartialZeta FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition

p2m_open "Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set Ideal P2MW.S_NumberField_exists_completedDedekindZeta_package.Ideal NumberField.Ideal Asymptotics P2MW.S_NumberField_exists_completedDedekindZeta_package.Asymptotics"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K]

/-- For `n ≠ 0`, the bijection between nonzero-divisor ideals of `𝓞 K` of absolute norm `n` and
ideals of `𝓞 K` of absolute norm `n`, given by the underlying ideal. -/
noncomputable def gapsw80_t10_fiberEquiv {n : ℕ} (hn : n ≠ 0) :
    {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n}
      ≃ {I : Ideal (𝓞 K) // absNorm I = n} where
  toFun J := ⟨J.1.1, J.2⟩
  invFun I := ⟨⟨I.1, Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mp
    (by rw [I.2]; exact hn)⟩, I.2⟩
  left_inv J := by ext; rfl
  right_inv I := rfl

/-- For each `n`, there are finitely many nonzero-divisor ideals of `𝓞 K` of absolute norm `n`. -/
scoped instance gapsw80_t10_fiberFinite (n : ℕ) :
    Finite {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n} := by
  have : Finite {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  exact Finite.of_injective
    (fun J => (⟨J.1.1, J.2⟩ : {I : Ideal (𝓞 K) // absNorm I = n}))
    (fun J₁ J₂ h => Subtype.ext (Subtype.ext (by
      simpa only [Subtype.mk.injEq] using h)))

/-- For `1 < s.re`, the L-series of `n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}` (the
ideal-counting function) is summable at `s`. -/
theorem gapsw80_t10_LSeriesSummable_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s := by
  have key : LSeriesSummable
      (fun n ↦ ((Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) : ℂ)) s := by
    refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ (fun _ => Nat.cast_nonneg _)
      zero_le_one hs

    exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (𝕜 := ℝ) (r := 1) <| by
      simp only [Real.rpow_one]
      refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp
        tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
      simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
      congr
      rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
        show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
        show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by
          simp [Ideal.absNorm_eq_zero_iff],
        Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
        ← Finset.card_preimage_eq_sum_card_image_eq
          (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
      simp [Set.coe_eq_subtype]
  exact (LSeriesSummable_congr s (fun {n} _ => by push_cast; ring)).mp key

/-- For every `s` and `n`, `Nat.card {J : (Ideal (𝓞 K))⁰ // absNorm J = n} * n ^ (-s)` equals
`LSeries.term` of the ideal-counting function at `s` and `n`. -/
theorem gapsw80_t10_term_eq (s : ℂ) (n : ℕ) :
    (Nat.card {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n} : ℂ)
        * ((n : ℂ)) ^ (-s)
      = LSeries.term (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℂ)) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hE : IsEmpty {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = 0} :=
      ⟨fun J => (Ideal.absNorm_ne_zero_of_nonZeroDivisors J.1) J.2⟩
    simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, Nat.card_congr (gapsw80_t10_fiberEquiv K hn),
      div_eq_mul_inv, ← Complex.cpow_neg]

/-- For every `s` and `n`, the family `J ↦ (absNorm J)^(-s)` over nonzero-divisor ideals `J` of
absolute norm `n` has sum `LSeries.term` of the ideal-counting function at `s` and `n`. -/
theorem gapsw80_t10_fiber_hasSum (s : ℂ) (n : ℕ) :
    HasSum (fun J : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} =>
        ((absNorm (J.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      (LSeries.term (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℂ)) s n) := by
  have : Fintype {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} :=
    Fintype.ofFinite _
  have h1 : (fun J : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} =>
      ((absNorm (J.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) = fun _ => (n : ℂ) ^ (-s) := by
    funext J; rw [J.2]
  rw [h1, ← gapsw80_t10_term_eq K s n, ← nsmul_eq_mul, Nat.card_eq_fintype_card,
    ← Finset.card_univ, ← Finset.sum_const]
  exact hasSum_fintype _

/-- For `1 < s.re`, the family `J ↦ (absNorm J)^(-s)` over nonzero-divisor ideals `J` of `𝓞 K` is
summable. -/
theorem gapsw80_t10_summable_idealNorm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : (Ideal (𝓞 K))⁰ ↦
      ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) := by
  rw [← (Equiv.sigmaFiberEquiv
    (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K)))).summable_iff]
  refine Summable.of_norm ?_
  refine (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨?_, ?_⟩
  · exact fun n =>
      haveI : Fintype {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} := Fintype.ofFinite _
      (hasSum_fintype _).summable
  · refine ((gapsw80_t10_LSeriesSummable_dedekindZeta K hs).norm).congr fun n => ?_
    have : Fintype {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} :=
      Fintype.ofFinite _
    rw [tsum_fintype]
    calc ‖LSeries.term (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℂ)) s n‖
        = ‖(Nat.card {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} : ℂ)
            * (n : ℂ) ^ (-s)‖ := by rw [gapsw80_t10_term_eq K s n]
      _ = (Nat.card {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} : ℝ)
            * ‖(n : ℂ) ^ (-s)‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ = ∑ c : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n},
            ‖((fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) ∘
              (Equiv.sigmaFiberEquiv
                (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K))))) ⟨n, c⟩‖ := by
          rw [show (fun c : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} =>
              ‖((fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) ∘
                (Equiv.sigmaFiberEquiv _)) ⟨n, c⟩‖)
              = fun _ => ‖(n : ℂ) ^ (-s)‖ from funext fun c => by
            simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, c.2]]
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]

/-- For `1 < s.re`, the sum over ideal classes `C` of `gapsw80_t8_partialDedekindZeta K C s` equals
`dedekindZeta K s`. -/
theorem gapsw80_t10_sum_partialDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    ∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s
      = dedekindZeta K s := by
  have hSum := gapsw80_t10_summable_idealNorm K hs

  have hHS : HasSum
      (fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      (dedekindZeta K s) := by
    have hSig := (Equiv.sigmaFiberEquiv
      (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K)))).summable_iff.mpr hSum
    refine (Equiv.sigmaFiberEquiv
      (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K)))).hasSum_iff.mp ?_
    exact HasSum.sigma_of_hasSum
      (gapsw80_t10_LSeriesSummable_dedekindZeta K hs).hasSum
      (gapsw80_t10_fiber_hasSum K s) hSig

  have stepC : ∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s
      = ∑' J : (Ideal (𝓞 K))⁰, ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) := by
    have hSig : HasSum
        ((fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) ∘
          (Equiv.sigmaFiberEquiv
            (ClassGroup.mk0 : (Ideal (𝓞 K))⁰ → ClassGroup (𝓞 K))))
        (∑' J : (Ideal (𝓞 K))⁰, ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) :=
      (Equiv.sigmaFiberEquiv
        (ClassGroup.mk0 : (Ideal (𝓞 K))⁰ → ClassGroup (𝓞 K))).hasSum_iff.mpr hSum.hasSum
    have hOuter : HasSum (fun C : ClassGroup (𝓞 K) => gapsw80_t8_partialDedekindZeta K C s)
        (∑' J : (Ideal (𝓞 K))⁰, ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) :=
      hSig.sigma fun C => (hSum.subtype _).hasSum
    exact (hasSum_fintype _).unique hOuter
  rw [stepC, hHS.tsum_eq]

/-- The complex cast of the integer `|discr K|` equals the complex cast of the real number
`|(discr K : ℝ)|`. -/
theorem gapsw80_t10_discrCoercion :
    (((|discr K| : ℤ) : ℂ)) = (((|(discr K : ℝ)| : ℝ) : ℂ)) := by
  rw [← Complex.ofReal_intCast, Int.cast_abs]

/-- For `1 < s.re`, `gapsw80_t9_completedDedekindZeta K s = gapsw80_t1_completedDedekindZeta K s`.
-/
theorem gapsw80_t10_completedDedekindZeta_eq_T1 {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K s
      = gapsw80_t1_completedDedekindZeta K s := by
  rw [gapsw80_t9_completedDedekindZeta_eq_sum K hs,
    gapsw80_t10_sum_partialDedekindZeta_eq K hs,
    gapsw80_t1_completedDedekindZeta, gapsw80_t10_discrCoercion,
    gapsw80_t9_gammaFactor]
  ring

/-- The function on `ℂ` equal to `gapsw80_t9_completedDedekindZeta K 2` at `s = 0` and `s = 1`, and
to `gapsw80_t9_completedDedekindZeta K s` elsewhere. -/
noncomputable def gapsw80_t10_Lambda (s : ℂ) : ℂ :=
  if s = 0 ∨ s = 1 then gapsw80_t9_completedDedekindZeta K 2
  else gapsw80_t9_completedDedekindZeta K s

/-- `gapsw80_t10_Lambda K` agrees with `gapsw80_t9_completedDedekindZeta K` on `{0, 1}ᶜ`. -/
theorem gapsw80_t10_Lambda_eqOn :
    Set.EqOn (gapsw80_t10_Lambda K) (gapsw80_t9_completedDedekindZeta K)
      {(0 : ℂ), 1}ᶜ := by
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
  exact ite_eq_right (not_or.mpr hs)

/-- `gapsw80_t10_Lambda K` is complex differentiable on `{0, 1}ᶜ`. -/
theorem gapsw80_t10_Lambda_differentiableOn :
    DifferentiableOn ℂ (gapsw80_t10_Lambda K) {(0 : ℂ), 1}ᶜ :=
  (gapsw80_t9_differentiableOn_completedDedekindZeta K).congr
    (gapsw80_t10_Lambda_eqOn K)

/-- For `1 < s.re`, `gapsw80_t10_Lambda K s = gapsw80_t1_completedDedekindZeta K s`. -/
theorem gapsw80_t10_Lambda_eq_T1 {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t10_Lambda K s = gapsw80_t1_completedDedekindZeta K s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  rw [gapsw80_t10_Lambda, ite_eq_right (not_or.mpr ⟨hs0, hs1⟩)]
  exact gapsw80_t10_completedDedekindZeta_eq_T1 K hs

/-- For every `s`, `gapsw80_t10_Lambda K (1 - s) = gapsw80_t10_Lambda K s`. -/
theorem gapsw80_t10_Lambda_FE (s : ℂ) :
    gapsw80_t10_Lambda K (1 - s) = gapsw80_t10_Lambda K s := by
  unfold gapsw80_t10_Lambda
  by_cases h : s = 0 ∨ s = 1
  · have h' : (1 - s) = 0 ∨ (1 - s) = 1 := by
      rcases h with h0 | h1
      · exact Or.inr (by rw [h0]; ring)
      · exact Or.inl (by rw [h1]; ring)
    rw [ite_eq_left h', ite_eq_left h]
  · rw [not_or] at h
    have h' : ¬((1 - s) = 0 ∨ (1 - s) = 1) := by
      rw [not_or]
      exact ⟨fun hc => h.2 (sub_eq_zero.mp hc).symm, fun hc => h.1 (sub_eq_self.mp hc)⟩
    rw [ite_eq_right h', ite_eq_right (not_or.mpr h)]
    exact gapsw80_t9_completedDedekindZeta_FE K h.1 h.2

/-- For every number field `K` there is a function `Λ`, differentiable on `ℂ \ {0, 1}`, which
agrees with `gapsw80_t1_completedDedekindZeta K s` for `1 < s.re` and satisfies
`Λ (1 - s) = Λ s`. -/
theorem gapsw80_t10_A1_closed :
    FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition.gapsw80_t1_DedekindCompletedFE := by
  intro K
  exact ⟨gapsw80_t10_Lambda K,
    gapsw80_t10_Lambda_differentiableOn K,
    fun s hs => gapsw80_t10_Lambda_eq_T1 K hs,
    gapsw80_t10_Lambda_FE K⟩

end FLT.Gapsw80T10DedekindZetaBridgeA1Discharge

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT

namespace Gapsw80T11ExplicitFormulaA34Decomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module"

/-- The proposition that for every number field `K` there is an entire function `ξ` with
`ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s` for `s ≠ 0, 1`, and a constant `C` such
that `log ‖ξ s‖ ≤ C * ‖s‖ * log ‖s‖` whenever `2 ≤ ‖s‖`. -/
def gapsw80_t11_XiOrderOneHadamard : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ ξ : ℂ → ℂ,
      Differentiable ℂ ξ ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
        ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) ∧
      (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖)

end FLT.Gapsw80T11ExplicitFormulaA34Decomp

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT

namespace Gapsw80T32D1aBoundaryCaseDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T30D2d0cLocalEulerFactorProof
open FLT.Gapsw80T31D1HadamardSubDecomp

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

/-- The proposition that for every number field `K` and every entire function `ξ` with
`ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s` for `s ≠ 0, 1`, both `ξ 0 ≠ 0` and
`ξ 1 ≠ 0`. -/
def gapsw80_t32_XiEndpointNonvanishing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ ξ : ℂ → ℂ,
    Differentiable ℂ ξ →
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) →
    ξ 0 ≠ 0 ∧ ξ 1 ≠ 0

end FLT.Gapsw80T32D1aBoundaryCaseDecomp

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT

namespace Gapsw80T42D1b0a0XiNonzeroInfZerosProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
open FLT.Gapsw80T36D1appXiEndpointResidueProof
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
open FLT.Gapsw80T39D1b0HadamardQuotientDecomp
open FLT.Gapsw80T40D1b0bZeroFreeExpLinearProof
open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

/-- The proposition that for every number field `K` and real `C` there is `s` with `2 ≤ ‖s‖`,
`s ≠ 0`, `s ≠ 1` and `C * ‖s‖ < log ‖s * (s - 1) * gapsw80_t9_completedDedekindZeta K s‖`. -/
def gapsw80_t42_CompletedZetaRealSuperlinear : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ C : ℝ, ∃ s : ℂ,
    2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
    C * ‖s‖ < Real.log ‖s * (s - 1) * gapsw80_t9_completedDedekindZeta K s‖

end FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT

namespace KwDyf2XiEntireOrderDecomp

open FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T7ClosedFEWeakPair
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

/-- The weak functional-equation pair `gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)`
attached to the ideal class `C`. -/
noncomputable abbrev kwDyf2_P (C : ClassGroup (𝓞 K)) : WeakFEPair ℂ :=
  gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)

/-- The entire function
$r_C^s \left(s (s - 1) \Lambda_{0,C}(n s / 2) - 2 (s - 1) / n + 2 s \varepsilon_C / n\right)$
attached to the ideal class `C`, where `r_C = gapsw80_t9_covolRepr K C`,
`Λ_{0,C} = (kwDyf2_P K C).Λ₀` and `ε_C = (kwDyf2_P K C).ε`. -/
noncomputable def kwDyf2_xiSummand (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
    * (s * (s - 1) * (kwDyf2_P K C).Λ₀ ((nK K : ℂ) * s / 2)
        - 2 * (s - 1) / (nK K : ℂ)
        + 2 * s * (kwDyf2_P K C).ε / (nK K : ℂ))

/-- The function `s ↦ (gapsw80_t9_constK K)⁻¹ * ∑ C, kwDyf2_xiSummand K C s`, the sum running over
ideal classes. -/
noncomputable def kwDyf2_xi (s : ℂ) : ℂ :=
  (gapsw80_t9_constK K)⁻¹ * ∑ C : ClassGroup (𝓞 K), kwDyf2_xiSummand K C s

/-- The function `kwDyf2_xiSummand K C` is differentiable on `ℂ`. -/
theorem kwDyf2_differentiable_xiSummand (C : ClassGroup (𝓞 K)) :
    Differentiable ℂ (kwDyf2_xiSummand K C) := by
  unfold kwDyf2_xiSummand
  refine (differentiable_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr (gapsw80_t9_covolRepr_pos K C).ne'))).mul ?_
  refine (((differentiable_id.mul (differentiable_id.sub_const 1)).mul ?_).sub
    ((differentiable_const 2 |>.mul (differentiable_id.sub_const 1)).div_const _)).add
    (((differentiable_const 2).mul differentiable_id |>.mul (differentiable_const _)).div_const _)
  exact (kwDyf2_P K C).differentiable_Λ₀.comp
    (((differentiable_const _).mul differentiable_id).div_const _)

/-- The function `kwDyf2_xi K` is differentiable on `ℂ`. -/
theorem kwDyf2_differentiable_xi : Differentiable ℂ (kwDyf2_xi K) := by
  unfold kwDyf2_xi
  exact (differentiable_const _).mul
    (Differentiable.fun_sum (fun C _ => kwDyf2_differentiable_xiSummand K C))

/-- The weight `(kwDyf2_P K C).k` of the weak functional-equation pair attached to the ideal class
`C`, viewed as a complex number, equals `(nK K : ℂ) / 2`. -/
theorem kwDyf2_Pk_coe (C : ClassGroup (𝓞 K)) :
    ((kwDyf2_P K C).k : ℂ) = (nK K : ℂ) / 2 := by
  change (((nK K : ℝ) / 2 : ℝ) : ℂ) = (nK K : ℂ) / 2; push_cast; ring

/-- For `s ≠ 0` and `s ≠ 1`, `kwDyf2_xiSummand K C s` equals
`(covolRepr K C : ℂ) ^ s * (s * (s - 1) * (kwDyf2_P K C).Λ ((nK K : ℂ) * s / 2))`, where
`covolRepr K C` is `gapsw80_t9_covolRepr K C`. -/
theorem kwDyf2_xiSummand_eq (C : ClassGroup (𝓞 K)) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    kwDyf2_xiSummand K C s =
      ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
        * (s * (s - 1)
            * (kwDyf2_P K C).Λ ((nK K : ℂ) * s / 2)) := by
  unfold kwDyf2_xiSummand
  congr 1
  have hf0 : (kwDyf2_P K C).f₀ = 1 := rfl
  have hg0 : (kwDyf2_P K C).g₀ = 1 := rfl
  simp only [WeakFEPair.Λ, hf0, hg0, smul_eq_mul, mul_one]
  rw [kwDyf2_Pk_coe K C]
  have hn : (nK K : ℂ) ≠ 0 := gapsw80_t9_nK_ne_zero K
  have hσ : (nK K : ℂ) * s / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hn hs0) two_ne_zero
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hkσ : (nK K : ℂ) / 2 - (nK K : ℂ) * s / 2 ≠ 0 := by
    rw [div_sub_div_same, ← mul_one_sub]
    exact div_ne_zero (mul_ne_zero hn h1s) two_ne_zero
  field_simp
  ring

/-- For `s ≠ 0` and `s ≠ 1`, `kwDyf2_xi K s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s`.
-/
theorem kwDyf2_xi_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    kwDyf2_xi K s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s := by
  unfold kwDyf2_xi gapsw80_t9_completedDedekindZeta
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [kwDyf2_xiSummand_eq K C hs0 hs1]
  ring

/-- The proposition that for every number field `K` there is a real `C` with
`Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖` for all complex `s` with `2 ≤ ‖s‖`. -/
def kwDyf2_XiOrderBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

/-- If `kwDyf2_XiOrderBound` holds, then `gapsw80_t11_XiOrderOneHadamard` holds, i.e. for each
number field `K` there is an entire function equal to `s * (s - 1)` times the completed Dedekind
zeta function away from `0` and `1`, and of order at most one in the sense of the
`‖s‖ * Real.log ‖s‖` bound. -/
theorem kwDyf2_B1_of_C1 (hC1 : kwDyf2_XiOrderBound) :
    gapsw80_t11_XiOrderOneHadamard := by
  intro K _ _
  exact ⟨kwDyf2_xi K, kwDyf2_differentiable_xi K,
    fun s hs0 hs1 => kwDyf2_xi_eq K hs0 hs1, hC1 K⟩

/-- For `s ≠ 0` and `s ≠ 1`, `kwDyf2_xi K (1 - s) = kwDyf2_xi K s`. -/
theorem kwDyf2_sat_xi_FE {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    kwDyf2_xi K (1 - s) = kwDyf2_xi K s := by
  have h1s0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have h1s1 : (1 : ℂ) - s ≠ 1 := fun h => hs0 (sub_eq_self.mp h)
  rw [kwDyf2_xi_eq K h1s0 h1s1, kwDyf2_xi_eq K hs0 hs1,
    gapsw80_t9_completedDedekindZeta_FE K hs0 hs1]
  ring

end FLT.KwDyf2XiEntireOrderDecomp

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT

namespace Gapsw80T36D1appXiEndpointResidueProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T7ClosedFEWeakPair
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
open FLT.Gapsw80T35D1apa0ThreeFourOneIneqProof

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter"
p2m_open_scoped "nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K]

/-- The complex cast of the real number `(nK K : ℝ) / 2` equals `(nK K : ℂ) / 2`. -/
theorem gapsw80_t36_nK_cast_half : (((nK K : ℝ) / 2 : ℝ) : ℂ) = (nK K : ℂ) / 2 := by
  push_cast; ring

/-- For `a : ℂ`, the map `s ↦ (nK K : ℂ) * s / 2` sends the punctured neighbourhood `𝓝[≠] a` of `a`
into the punctured neighbourhood `𝓝[≠] ((nK K : ℂ) * a / 2)`, in the sense of `Tendsto`. -/
theorem gapsw80_t36_affine_tendsto (a : ℂ) :
    Tendsto (fun s : ℂ ↦ (nK K : ℂ) * s / 2) (𝓝[≠] a) (𝓝[≠] ((nK K : ℂ) * a / 2)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (((continuous_const.mul continuous_id').div_const 2).tendsto a).mono_left
      nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall (fun s hs ↦ ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
    exact fun h ↦ hs (mul_left_cancel₀ (gapsw80_t9_nK_ne_zero K)
      (by linear_combination 2 * h))

/-- For an ideal class `C`, as `s → 1` with `s ≠ 1`,
`(covolRepr K C : ℂ) ^ s * ((s - 1) * Λ ((nK K : ℂ) * s / 2))` tends to `2 / (nK K : ℂ)`, where `Λ`
is the completed Mellin transform of the Hecke weak functional-equation pair of the class
representative of `C` and `covolRepr K C` is `gapsw80_t9_covolRepr K C`. -/
theorem gapsw80_t36_perClass_residue_one (C : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
        * ((s - 1)
          * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 1) (𝓝 (2 / (nK K : ℂ))) := by
  set P := gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)
  have hn := gapsw80_t9_nK_ne_zero K
  have hk : (P.k : ℂ) = (nK K : ℂ) / 2 := gapsw80_t36_nK_cast_half K

  have hmap : Tendsto (fun s : ℂ ↦ (nK K : ℂ) * s / 2) (𝓝[≠] 1) (𝓝[≠] (P.k : ℂ)) := by
    have := gapsw80_t36_affine_tendsto K 1
    rwa [mul_one, ← hk] at this
  have hres : Tendsto (fun s : ℂ ↦ ((nK K : ℂ) * s / 2 - (P.k : ℂ))
        * P.Λ ((nK K : ℂ) * s / 2)) (𝓝[≠] 1) (𝓝 P.ε) := by
    have h := P.Λ_residue_k.comp hmap
    simpa only [Function.comp_def, smul_eq_mul,
      show (P.g₀ : ℂ) = 1 from rfl, mul_one] using h

  have hres' : Tendsto (fun s : ℂ ↦ (s - 1) * P.Λ ((nK K : ℂ) * s / 2))
      (𝓝[≠] 1) (𝓝 ((2 / (nK K : ℂ)) * P.ε)) := by
    refine (hres.const_mul (2 / (nK K : ℂ))).congr' (Eventually.of_forall fun s ↦ ?_)
    rw [hk, show (2 / (nK K : ℂ)) * (((nK K : ℂ) * s / 2 - (nK K : ℂ) / 2)
          * P.Λ ((nK K : ℂ) * s / 2))
        = ((2 / (nK K : ℂ)) * ((nK K : ℂ) / 2)) * ((s - 1) * P.Λ ((nK K : ℂ) * s / 2))
        from by ring,
      show (2 / (nK K : ℂ)) * ((nK K : ℂ) / 2) = 1 from by field_simp, one_mul]

  have hcvne : ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (gapsw80_t9_covolRepr_pos K C).ne'
  have hcov : Tendsto (fun s : ℂ ↦ ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s)
      (𝓝[≠] 1) (𝓝 ((gapsw80_t9_covolRepr K C : ℝ) : ℂ)) := by
    have := (continuousAt_const_cpow hcvne (b := 1)).tendsto
    simpa only [Complex.cpow_one] using this.mono_left nhdsWithin_le_nhds
  have hcε : ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) * P.ε = 1 := by
    show ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) * ((gapsw80_t9_covolRepr K C : ℝ) : ℂ)⁻¹ = 1
    exact mul_inv_cancel₀ hcvne
  have := hcov.mul hres'
  rwa [show ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) * ((2 / (nK K : ℂ)) * P.ε)
      = (2 / (nK K : ℂ)) * (((gapsw80_t9_covolRepr K C : ℝ) : ℂ) * P.ε) from by ring,
    hcε, mul_one] at this

/-- For an ideal class `C`, as `s → 0` with `s ≠ 0`,
`(covolRepr K C : ℂ) ^ s * (s * Λ ((nK K : ℂ) * s / 2))` tends to `-(2 / (nK K : ℂ))`, where `Λ` is
the completed Mellin transform of the Hecke weak functional-equation pair of the class
representative of `C` and `covolRepr K C` is `gapsw80_t9_covolRepr K C`. -/
theorem gapsw80_t36_perClass_residue_zero (C : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
        * (s * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
            ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 0) (𝓝 (-(2 / (nK K : ℂ)))) := by
  set P := gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)
  have hn := gapsw80_t9_nK_ne_zero K
  have hmap : Tendsto (fun s : ℂ ↦ (nK K : ℂ) * s / 2) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
    have := gapsw80_t36_affine_tendsto K 0
    simpa using this
  have hres : Tendsto (fun s : ℂ ↦ ((nK K : ℂ) * s / 2) * P.Λ ((nK K : ℂ) * s / 2))
      (𝓝[≠] 0) (𝓝 (-1 : ℂ)) := by
    have h := P.Λ_residue_zero.comp hmap
    simpa only [Function.comp_def, smul_eq_mul,
      show (P.f₀ : ℂ) = 1 from rfl] using h
  have hres' : Tendsto (fun s : ℂ ↦ s * P.Λ ((nK K : ℂ) * s / 2))
      (𝓝[≠] 0) (𝓝 (-(2 / (nK K : ℂ)))) := by
    have h := hres.const_mul (2 / (nK K : ℂ))
    rw [show (2 / (nK K : ℂ)) * (-1) = -(2 / (nK K : ℂ)) from by ring] at h
    refine h.congr' (Eventually.of_forall fun s ↦ ?_)
    rw [show (2 / (nK K : ℂ)) * ((nK K : ℂ) * s / 2 * P.Λ ((nK K : ℂ) * s / 2))
        = ((2 / (nK K : ℂ)) * ((nK K : ℂ) / 2)) * (s * P.Λ ((nK K : ℂ) * s / 2))
        from by ring,
      show (2 / (nK K : ℂ)) * ((nK K : ℂ) / 2) = 1 from by field_simp, one_mul]
  have hcvne : ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (gapsw80_t9_covolRepr_pos K C).ne'
  have hcov : Tendsto (fun s : ℂ ↦ ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s)
      (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
    have := (continuousAt_const_cpow hcvne (b := 0)).tendsto
    simpa only [Complex.cpow_zero] using this.mono_left nhdsWithin_le_nhds
  have := hcov.mul hres'
  rwa [one_mul] at this

/-- The complex number `(constK K)⁻¹ * (2 * h / n)`, where `constK K` is `gapsw80_t9_constK K`, `h`
is the class number of `K` and `n` is the degree of `K`. -/
noncomputable def gapsw80_t36_xiResidueVal : ℂ :=
  (gapsw80_t9_constK K)⁻¹
    * (2 * (Fintype.card (ClassGroup (𝓞 K)) : ℂ) / (nK K : ℂ))

/-- The complex number `gapsw80_t36_xiResidueVal K` is nonzero. -/
theorem gapsw80_t36_xiResidueVal_ne_zero : gapsw80_t36_xiResidueVal K ≠ 0 := by
  refine mul_ne_zero (inv_ne_zero (gapsw80_t9_constK_ne_zero K)) (div_ne_zero ?_ ?_)
  · exact mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  · exact gapsw80_t9_nK_ne_zero K

/-- As `s → 1` with `s ≠ 1`, `s * (s - 1) * gapsw80_t9_completedDedekindZeta K s` tends to
`gapsw80_t36_xiResidueVal K`. -/
theorem gapsw80_t36_tendsto_xi_rhs_one :
    Tendsto (fun s : ℂ ↦ s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
      (𝓝[≠] 1) (𝓝 (gapsw80_t36_xiResidueVal K)) := by
  have hsum : Tendsto (fun s : ℂ ↦
        ∑ C : ClassGroup (𝓞 K), ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
          * ((s - 1) * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
              ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 1) (𝓝 (∑ _C : ClassGroup (𝓞 K), (2 / (nK K : ℂ)))) :=
    tendsto_finsetSum _ (fun C _ ↦ gapsw80_t36_perClass_residue_one K C)
  have hs : Tendsto (fun s : ℂ ↦ s) (𝓝[≠] 1) (𝓝 (1:ℂ)) :=
    continuous_id.tendsto' 1 1 rfl |>.mono_left nhdsWithin_le_nhds
  have hG := (hsum.const_mul (gapsw80_t9_constK K)⁻¹).mul hs
  have hval : (gapsw80_t9_constK K)⁻¹
        * (∑ _C : ClassGroup (𝓞 K), (2 / (nK K : ℂ))) * 1
      = gapsw80_t36_xiResidueVal K := by
    rw [mul_one, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    unfold gapsw80_t36_xiResidueVal; ring
  rw [← hval]
  refine hG.congr' (Eventually.of_forall fun s ↦ ?_)
  unfold gapsw80_t9_completedDedekindZeta
  have hsum_eq : ∑ C : ClassGroup (𝓞 K),
        ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s * ((s - 1)
          * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
              ((nK K : ℂ) * s / 2))
      = (s - 1) * ∑ C : ClassGroup (𝓞 K),
          ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
            * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
                ((nK K : ℂ) * s / 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun C _ ↦ by ring)
  rw [hsum_eq]; ring

/-- As `s → 0` with `s ≠ 0`, `s * (s - 1) * gapsw80_t9_completedDedekindZeta K s` tends to
`gapsw80_t36_xiResidueVal K`. -/
theorem gapsw80_t36_tendsto_xi_rhs_zero :
    Tendsto (fun s : ℂ ↦ s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
      (𝓝[≠] 0) (𝓝 (gapsw80_t36_xiResidueVal K)) := by
  have hsum : Tendsto (fun s : ℂ ↦
        ∑ C : ClassGroup (𝓞 K), ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
          * (s * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
              ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 0) (𝓝 (∑ _C : ClassGroup (𝓞 K), (-(2 / (nK K : ℂ))))) :=
    tendsto_finsetSum _ (fun C _ ↦ gapsw80_t36_perClass_residue_zero K C)
  have hs1 : Tendsto (fun s : ℂ ↦ s - 1) (𝓝[≠] 0) (𝓝 (-1:ℂ)) := by
    have := (continuous_sub_right (1:ℂ)).tendsto (0:ℂ)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hG := (hsum.const_mul (gapsw80_t9_constK K)⁻¹).mul hs1
  have hval : (gapsw80_t9_constK K)⁻¹
        * (∑ _C : ClassGroup (𝓞 K), (-(2 / (nK K : ℂ)))) * (-1)
      = gapsw80_t36_xiResidueVal K := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    unfold gapsw80_t36_xiResidueVal; ring
  rw [← hval]
  refine hG.congr' (Eventually.of_forall fun s ↦ ?_)
  unfold gapsw80_t9_completedDedekindZeta
  have hsum_eq : ∑ C : ClassGroup (𝓞 K),
        ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s * (s
          * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
              ((nK K : ℂ) * s / 2))
      = s * ∑ C : ClassGroup (𝓞 K),
          ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
            * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
                ((nK K : ℂ) * s / 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun C _ ↦ by ring)
  rw [hsum_eq]; ring

/-- The proposition `gapsw80_t32_XiEndpointNonvanishing` holds: for every number field `K`, any
entire function equal to `s * (s - 1)` times the completed Dedekind zeta function away from `0` and
`1` is nonzero at `0` and at `1`. -/
theorem gapsw80_t36_D1app_closed : gapsw80_t32_XiEndpointNonvanishing := by
  intro K _ _ ξ hdiff hagr

  have heq1 : (fun s ↦ s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
      =ᶠ[𝓝[≠] (1:ℂ)] ξ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
        (isOpen_ne.mem_nhds (one_ne_zero (α := ℂ))),
      self_mem_nhdsWithin] with s hs0 hs1
    exact (hagr s hs0 hs1).symm
  have heq0 : (fun s ↦ s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
      =ᶠ[𝓝[≠] (0:ℂ)] ξ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (zero_ne_one (α := ℂ)))]
      with s hs0 hs1
    exact (hagr s hs0 hs1).symm
  have hξ1 : ξ 1 = gapsw80_t36_xiResidueVal K :=
    tendsto_nhds_unique
      ((hdiff.continuous.tendsto 1).mono_left nhdsWithin_le_nhds)
      ((gapsw80_t36_tendsto_xi_rhs_one K).congr' heq1)
  have hξ0 : ξ 0 = gapsw80_t36_xiResidueVal K :=
    tendsto_nhds_unique
      ((hdiff.continuous.tendsto 0).mono_left nhdsWithin_le_nhds)
      ((gapsw80_t36_tendsto_xi_rhs_zero K).congr' heq0)
  exact ⟨hξ0 ▸ gapsw80_t36_xiResidueVal_ne_zero K, hξ1 ▸ gapsw80_t36_xiResidueVal_ne_zero K⟩

end FLT.Gapsw80T36D1appXiEndpointResidueProof

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT

namespace KwDyf2XiOrderBoundDecomp

open FLT.KwDyf2XiEntireOrderDecomp
open FLT.Gapsw80T9ClassSumA1Closure

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical"

/-- If `0 < s.re`, then `‖Complex.Gamma s‖ ≤ Real.Gamma s.re`. -/
theorem kwDyf2_norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs,
    Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]

/-- If `s.re ≤ 1/2`, then `‖s‖ ≤ ‖1 - s‖`. -/
theorem kwDyf2_norm_le_norm_one_sub {s : ℂ} (hs : s.re ≤ 1/2) :
    ‖s‖ ≤ ‖1 - s‖ := by
  have h : ‖s‖^2 ≤ ‖1 - s‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, zero_sub, neg_mul_neg]
    nlinarith
  nlinarith [norm_nonneg s, norm_nonneg (1 - s)]

/-- If `2 ≤ ‖s‖`, then `0 ≤ ‖s‖ * Real.log ‖s‖`. -/
theorem kwDyf2_norm_mul_log_norm_nonneg {s : ℂ} (hs : 2 ≤ ‖s‖) :
    0 ≤ ‖s‖ * Real.log ‖s‖ :=
  mul_nonneg (by linarith) (Real.log_nonneg (by linarith))

/-- If `2 ≤ ‖s‖`, then `‖1 - s‖ ≤ (3/2) * ‖s‖`. -/
theorem kwDyf2_norm_one_sub_le {s : ℂ} (hs : 2 ≤ ‖s‖) :
    ‖1 - s‖ ≤ (3/2) * ‖s‖ :=
  calc ‖1 - s‖ ≤ ‖(1:ℂ)‖ + ‖s‖ := norm_sub_le 1 s
    _ = 1 + ‖s‖ := by rw [norm_one]
    _ ≤ (3/2) * ‖s‖ := by linarith

/-- If `2 ≤ ‖s‖` and `‖s‖ ≤ ‖1 - s‖`, then `‖1 - s‖ * Real.log ‖1 - s‖ ≤ 3 * ‖s‖ * Real.log ‖s‖`.
-/
theorem kwDyf2_refl_growth_bound {s : ℂ} (hs : 2 ≤ ‖s‖) (hle : ‖s‖ ≤ ‖1 - s‖) :
    ‖1 - s‖ * Real.log ‖1 - s‖ ≤ 3 * ‖s‖ * Real.log ‖s‖ := by
  have hlog2 : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log two_pos hs
  have h32 : ‖1 - s‖ ≤ (3/2) * ‖s‖ := kwDyf2_norm_one_sub_le hs
  have hlog : Real.log ‖1 - s‖ ≤ 2 * Real.log ‖s‖ :=
    calc Real.log ‖1 - s‖ ≤ Real.log ((3/2) * ‖s‖) :=
          Real.log_le_log (lt_of_lt_of_le two_pos (hs.trans hle)) h32
      _ = Real.log (3/2) + Real.log ‖s‖ :=
          Real.log_mul (by norm_num) (lt_of_lt_of_le two_pos hs).ne'
      _ ≤ 2 * Real.log ‖s‖ := by
          linarith [Real.log_le_log (by norm_num : (0:ℝ) < 3/2) (by norm_num : (3/2:ℝ) ≤ 2)]
  calc ‖1 - s‖ * Real.log ‖1 - s‖
      ≤ (3/2) * ‖s‖ * (2 * Real.log ‖s‖) := by
        refine mul_le_mul h32 hlog ?_ (by linarith)
        exact Real.log_nonneg (le_trans one_le_two (hs.trans hle))
    _ = 3 * ‖s‖ * Real.log ‖s‖ := by ring

/-- The proposition that for every number field `K` there is a real `C` with
`Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖` for all complex `s` with `1/2 ≤ s.re` and
`2 ≤ ‖s‖`. -/
def kwDyf2_XiHalfplaneBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 1/2 ≤ s.re → 2 ≤ ‖s‖ →
      Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

/-- If `kwDyf2_XiHalfplaneBound` holds, then `kwDyf2_XiOrderBound` holds. -/
theorem kwDyf2_C1_of_halfplane (hHalf : kwDyf2_XiHalfplaneBound) :
    kwDyf2_XiOrderBound := by
  intro K _ _
  obtain ⟨C, hC⟩ := hHalf K
  refine ⟨3 * max C 0, fun s hs => ?_⟩
  have hsln : 0 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_norm_mul_log_norm_nonneg hs
  rcases le_or_gt (1/2 : ℝ) s.re with hre | hre
  · calc Real.log ‖kwDyf2_xi K s‖
        ≤ C * ‖s‖ * Real.log ‖s‖ := hC s hre hs
      _ ≤ max C 0 * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]
          gcongr
          exact le_max_left C 0
      _ ≤ 3 * max C 0 * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc (3 * max C 0)]
          gcongr
          nlinarith [le_max_right C 0]
  · have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
    have hs1 : s ≠ 1 := fun h => by simp [h, Complex.one_re] at hre; linarith
    rw [← kwDyf2_sat_xi_FE K hs0 hs1]
    have h1re : 1/2 ≤ (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hle : ‖s‖ ≤ ‖1 - s‖ := kwDyf2_norm_le_norm_one_sub hre.le
    have h1norm : 2 ≤ ‖1 - s‖ := le_trans hs hle
    calc Real.log ‖kwDyf2_xi K (1 - s)‖
        ≤ C * ‖1 - s‖ * Real.log ‖1 - s‖ := hC (1 - s) h1re h1norm
      _ ≤ max C 0 * (‖1 - s‖ * Real.log ‖1 - s‖) := by
          rw [mul_assoc]
          gcongr
          · exact kwDyf2_norm_mul_log_norm_nonneg h1norm
          · exact le_max_left C 0
      _ ≤ max C 0 * (3 * ‖s‖ * Real.log ‖s‖) :=
          mul_le_mul_of_nonneg_left (kwDyf2_refl_growth_bound hs hle)
            (le_max_right C 0)
      _ = 3 * max C 0 * ‖s‖ * Real.log ‖s‖ := by ring

/-- The proposition that for every number field `K` there is a real `C` with
`Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖` for all complex `s` with `3/2 ≤ s.re` and
`2 ≤ ‖s‖`. -/
def kwDyf2_XiRightHalfBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 3/2 ≤ s.re → 2 ≤ ‖s‖ →
      Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

/-- The proposition that for every number field `K` there is a real `C` with
`Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖` for all complex `s` with `1/2 ≤ s.re ≤ 3/2` and
`2 ≤ ‖s‖`. -/
def kwDyf2_XiStripBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 → 2 ≤ ‖s‖ →
      Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

/-- If `kwDyf2_XiRightHalfBound` and `kwDyf2_XiStripBound` hold, then `kwDyf2_XiHalfplaneBound`
holds. -/
theorem kwDyf2_halfplane_of_C1a_C1b
    (hC1a : kwDyf2_XiRightHalfBound) (hC1b : kwDyf2_XiStripBound) :
    kwDyf2_XiHalfplaneBound := by
  intro K _ _
  obtain ⟨Ca, hCa⟩ := hC1a K
  obtain ⟨Cb, hCb⟩ := hC1b K
  refine ⟨max (max Ca 0) (max Cb 0), fun s hre hs => ?_⟩
  have hsln : 0 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_norm_mul_log_norm_nonneg hs
  rcases le_or_gt (3/2 : ℝ) s.re with hre2 | hre2
  · calc Real.log ‖kwDyf2_xi K s‖ ≤ Ca * ‖s‖ * Real.log ‖s‖ := hCa s hre2 hs
      _ ≤ max (max Ca 0) (max Cb 0) * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]; gcongr
          exact le_trans (le_max_left Ca 0) (le_max_left _ _)
  · calc Real.log ‖kwDyf2_xi K s‖ ≤ Cb * ‖s‖ * Real.log ‖s‖ := hCb s hre hre2.le hs
      _ ≤ max (max Ca 0) (max Cb 0) * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]; gcongr
          exact le_trans (le_max_left Cb 0) (le_max_right _ _)

/-- If `kwDyf2_XiRightHalfBound` and `kwDyf2_XiStripBound` hold, then `kwDyf2_XiOrderBound` holds.
-/
theorem kwDyf2_C1_of_C1a_C1b
    (hC1a : kwDyf2_XiRightHalfBound) (hC1b : kwDyf2_XiStripBound) :
    kwDyf2_XiOrderBound :=
  kwDyf2_C1_of_halfplane (kwDyf2_halfplane_of_C1a_C1b hC1a hC1b)

end FLT.KwDyf2XiOrderBoundDecomp

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT

namespace KwDyf2RealGammaLogBound

open FLT.KwDyf2XiOrderBoundDecomp

p2m_open "Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical Nat P2MW.S_NumberField_exists_completedDedekindZeta_package.Nat"

/-- The function `t ↦ t * Real.log t` is monotone on `Set.Ici 1`. -/
theorem kwDyf2_monotoneOn_mul_log : MonotoneOn (fun t => t * Real.log t) (Set.Ici 1) := by
  intro a ha b hb hab
  exact mul_le_mul hab (Real.log_le_log (lt_of_lt_of_le one_pos ha) hab)
    (Real.log_nonneg ha) (le_trans (le_of_lt one_pos) hb)

/-- For every natural number `n`, `Real.log (n ! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ)`. -/
theorem kwDyf2_log_factorial_le {n : ℕ} :
    Real.log (n ! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · simp [h0]
  · calc Real.log (n ! : ℝ)
        ≤ Real.log ((n : ℝ) ^ n) := by
          refine Real.log_le_log (by exact_mod_cast n.factorial_pos) ?_
          exact_mod_cast Nat.factorial_le_pow n
      _ = (n : ℝ) * Real.log (n : ℝ) := by
          rw [Real.log_pow]


/-- If `1 ≤ x`, then `Real.log (Real.Gamma x) ≤ x * Real.log x`. -/
theorem kwDyf2_log_Gamma_le_self_mul_log {x : ℝ} (hx : 1 ≤ x) :
    Real.log (Real.Gamma x) ≤ x * Real.log x := by
  set n := ⌊x⌋₊ with hn_def
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (le_trans zero_le_one hx)
  have hxn1 : x ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1

  have ha : 0 ≤ (n:ℝ) + 1 - x := by linarith
  have hb : 0 ≤ x - (n:ℝ) := by linarith
  have hab : ((n:ℝ) + 1 - x) + (x - (n:ℝ)) = 1 := by ring
  have hcomb : ((n:ℝ) + 1 - x) • (n : ℝ) + (x - (n:ℝ)) • ((n : ℝ) + 1) = x := by
    simp only [smul_eq_mul]; ring

  have hconv := Real.convexOn_log_Gamma.2 (Set.mem_Ioi.mpr hnpos)
    (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < (n:ℝ) + 1)) ha hb hab
  rw [hcomb, Function.comp_apply, Function.comp_apply, Function.comp_apply,
    smul_eq_mul, smul_eq_mul] at hconv

  have hGn : Real.Gamma (n : ℝ) = ((n - 1)! : ℝ) := by
    have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel hn1).symm
    rw [hcast]; exact_mod_cast Real.Gamma_nat_eq_factorial (n - 1)
  have hGn1 : Real.Gamma ((n : ℝ) + 1) = (n ! : ℝ) := by
    exact_mod_cast Real.Gamma_nat_eq_factorial n
  rw [hGn, hGn1] at hconv

  have hend1 : Real.log ((n - 1)! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    calc Real.log ((n - 1)! : ℝ)
        ≤ Real.log (n ! : ℝ) := by
          refine Real.log_le_log (by exact_mod_cast (n-1).factorial_pos) ?_
          exact_mod_cast Nat.factorial_le (Nat.sub_le n 1)
      _ ≤ (n : ℝ) * Real.log (n : ℝ) := kwDyf2_log_factorial_le
  have hend2 : Real.log (n ! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) :=
    kwDyf2_log_factorial_le

  have hstep : Real.log (Real.Gamma x) ≤ (n : ℝ) * Real.log (n : ℝ) :=
    calc Real.log (Real.Gamma x)
        ≤ ((n:ℝ)+1-x) * Real.log ((n - 1)! : ℝ)
            + (x-(n:ℝ)) * Real.log (n ! : ℝ) := hconv
      _ ≤ ((n:ℝ)+1-x) * ((n : ℝ) * Real.log (n : ℝ))
            + (x-(n:ℝ)) * ((n : ℝ) * Real.log (n : ℝ)) := by gcongr
      _ = (n : ℝ) * Real.log (n : ℝ) := by rw [← add_mul, hab, one_mul]

  exact hstep.trans (kwDyf2_monotoneOn_mul_log
    (Set.mem_Ici.mpr (by exact_mod_cast hn1)) (Set.mem_Ici.mpr hx) hnx)

/-- If `1 ≤ s.re`, then `Real.log ‖Complex.Gamma s‖ ≤ s.re * Real.log s.re`. -/
theorem kwDyf2_log_norm_Gamma_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    Real.log ‖Complex.Gamma s‖ ≤ s.re * Real.log s.re := by
  have hrepos : 0 < s.re := by linarith
  exact (Real.log_le_log (norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hrepos))
    (kwDyf2_norm_Gamma_le_Gamma_re hrepos)).trans (kwDyf2_log_Gamma_le_self_mul_log hs)

/-- If `1 ≤ s.re`, then `Real.log ‖Complex.Gamma s‖ ≤ ‖s‖ * Real.log ‖s‖`. -/
theorem kwDyf2_log_norm_Gamma_le_norm_mul_log_norm {s : ℂ}
    (hs : 1 ≤ s.re) :
    Real.log ‖Complex.Gamma s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
  have hre_norm : s.re ≤ ‖s‖ := Complex.re_le_norm s
  exact (kwDyf2_log_norm_Gamma_le_re hs).trans
    (kwDyf2_monotoneOn_mul_log (Set.mem_Ici.mpr hs)
      (Set.mem_Ici.mpr (le_trans hs hre_norm)) hre_norm)

end FLT.KwDyf2RealGammaLogBound

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT

namespace KwDyf2XiStripBoundAttack

open FLT.KwDyf2XiEntireOrderDecomp
open FLT.KwDyf2XiOrderBoundDecomp
open FLT.Gapsw80T15XiOrderOneB1Decomp
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T3IdealLatticeThetaTransformation

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical"

/-- If `0 < t` and `a ≤ σ ≤ b`, then `t ^ σ ≤ t ^ a + t ^ b`. -/
theorem kwDyf2_rpow_le_endpoints {t a b σ : ℝ} (ht : 0 < t)
    (ha : a ≤ σ) (hb : σ ≤ b) : t ^ σ ≤ t ^ a + t ^ b := by
  have hta : (0:ℝ) ≤ t ^ a := Real.rpow_nonneg ht.le a
  have htb : (0:ℝ) ≤ t ^ b := Real.rpow_nonneg ht.le b
  rcases le_total t 1 with h1 | h1
  · exact le_add_of_le_of_nonneg
      (Real.rpow_le_rpow_of_exponent_ge ht h1 ha) htb
  · exact le_add_of_nonneg_of_le hta
      (Real.rpow_le_rpow_of_exponent_le h1 hb)

section Λ₀Bound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- For a weak functional-equation pair `P` and a real `x`, the integral over `t ∈ (0, ∞)` of
`‖(t : ℂ) ^ ((x : ℂ) - 1) • P.f_modif t‖`, the norm of the Mellin integrand of the modified
function `P.f_modif` at real part `x`. -/
noncomputable def kwDyf2_MellinNormBound (P : WeakFEPair E) (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), ‖(t : ℂ) ^ ((x:ℂ) - 1) • P.f_modif t‖

omit [CompleteSpace E] in

/-- For a weak functional-equation pair `P` and real `x`, the function
`t ↦ ‖(t : ℂ) ^ ((x : ℂ) - 1) • P.f_modif t‖` is integrable on `Set.Ioi 0`. -/
theorem kwDyf2_MellinNormBound_integrable (P : WeakFEPair E) (x : ℝ) :
    IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((x:ℂ) - 1) • P.f_modif t‖)
      (Set.Ioi (0:ℝ)) :=
  (P.isStrongFEPair_toStrongFEPair.hasMellin (x:ℂ)).1.norm

omit [CompleteSpace E] in

/-- For a weak functional-equation pair `P` and real `x`, `0 ≤ kwDyf2_MellinNormBound P x`. -/
theorem kwDyf2_MellinNormBound_nonneg (P : WeakFEPair E) (x : ℝ) :
    0 ≤ kwDyf2_MellinNormBound P x :=
  integral_nonneg (fun _ => norm_nonneg _)

omit [CompleteSpace E] in

/-- For a weak functional-equation pair `P` and `s` with `a ≤ s.re ≤ b`,
`‖P.Λ₀ s‖ ≤ kwDyf2_MellinNormBound P a + kwDyf2_MellinNormBound P b`. -/
theorem kwDyf2_norm_Λ₀_le (P : WeakFEPair E) {s : ℂ} {a b : ℝ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖P.Λ₀ s‖ ≤ kwDyf2_MellinNormBound P a + kwDyf2_MellinNormBound P b := by

  show ‖mellin P.f_modif s‖ ≤ _
  unfold mellin

  refine (norm_integral_le_integral_norm _).trans ?_

  have hint_a := kwDyf2_MellinNormBound_integrable P a
  have hint_b := kwDyf2_MellinNormBound_integrable P b
  rw [show kwDyf2_MellinNormBound P a + kwDyf2_MellinNormBound P b
        = ∫ t in Set.Ioi (0:ℝ),
            (‖(t:ℂ)^((a:ℂ)-1) • P.f_modif t‖ + ‖(t:ℂ)^((b:ℂ)-1) • P.f_modif t‖)
      from (integral_add hint_a hint_b).symm]
  refine setIntegral_mono_on (P.isStrongFEPair_toStrongFEPair.hasMellin s).1.norm
    (hint_a.add hint_b) measurableSet_Ioi (fun t ht => ?_)

  have htpos : (0:ℝ) < t := ht
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos,
    Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right
    (kwDyf2_rpow_le_endpoints htpos (by linarith) (by linarith)) (norm_nonneg _)

end Λ₀Bound

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

variable (K : Type) [Field K] [NumberField K]

/-- The real constant attached to an ideal class `C`:
`(r^(1/2) + r^(3/2)) * ((3/2) * (M(n/4) + M(3n/4)) + 3/n + 3 * ‖ε‖ / n)`, where `r` is
`gapsw80_t9_covolRepr K C`, `n` is the degree of `K`, `M` is
`kwDyf2_MellinNormBound (kwDyf2_P K C)` and `ε` is `(kwDyf2_P K C).ε`. -/
noncomputable def kwDyf2_Bconst (C : ClassGroup (𝓞 K)) : ℝ :=
  (gapsw80_t9_covolRepr K C ^ (1/2 : ℝ) + gapsw80_t9_covolRepr K C ^ (3/2 : ℝ))
    * ((3/2) * (kwDyf2_MellinNormBound (kwDyf2_P K C) ((nK K : ℝ)/4)
                  + kwDyf2_MellinNormBound (kwDyf2_P K C) ((3 * nK K : ℝ)/4))
        + 3 / (nK K : ℝ) + 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ))


/-- If `1/2 ≤ s.re ≤ 3/2` and `2 ≤ ‖s‖`, then
`‖kwDyf2_xiSummand K C s‖ ≤ kwDyf2_Bconst K C * ‖s‖ ^ 2`. -/
theorem kwDyf2_norm_xiSummand_le (C : ClassGroup (𝓞 K)) {s : ℂ}
    (hre1 : 1/2 ≤ s.re) (hre2 : s.re ≤ 3/2) (hs : 2 ≤ ‖s‖) :
    ‖kwDyf2_xiSummand K C s‖ ≤ kwDyf2_Bconst K C * ‖s‖^2 := by
  have hnK : (0:ℝ) < (nK K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < nK K)
  have hcov := gapsw80_t9_covolRepr_pos K C
  have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hs
  have hs1 : ‖s - 1‖ ≤ (3/2) * ‖s‖ := by
    calc ‖s - 1‖ ≤ ‖s‖ + 1 := by
          have := norm_sub_le s 1; rwa [norm_one] at this
      _ ≤ (3/2) * ‖s‖ := by linarith
  have hsle : ‖s‖ ≤ ‖s‖^2 := by nlinarith

  have hcovpow : ‖((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s‖
      ≤ gapsw80_t9_covolRepr K C ^ (1/2:ℝ) + gapsw80_t9_covolRepr K C ^ (3/2:ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hcov]
    exact kwDyf2_rpow_le_endpoints hcov hre1 hre2

  have hre_ns : ((nK K : ℂ) * s / 2).re = (nK K : ℝ) * s.re / 2 := by
    simp [Complex.mul_re]
  have hL0 : ‖(kwDyf2_P K C).Λ₀ ((nK K : ℂ) * s / 2)‖
      ≤ kwDyf2_MellinNormBound (kwDyf2_P K C) ((nK K : ℝ)/4)
        + kwDyf2_MellinNormBound (kwDyf2_P K C) ((3 * nK K : ℝ)/4) := by
    refine kwDyf2_norm_Λ₀_le (kwDyf2_P K C) ?_ ?_
    · rw [hre_ns]; nlinarith
    · rw [hre_ns]; nlinarith
  set Msum := kwDyf2_MellinNormBound (kwDyf2_P K C) ((nK K : ℝ)/4)
              + kwDyf2_MellinNormBound (kwDyf2_P K C) ((3 * nK K : ℝ)/4)
  have hMsum_nn : 0 ≤ Msum :=
    add_nonneg (kwDyf2_MellinNormBound_nonneg _ _) (kwDyf2_MellinNormBound_nonneg _ _)

  have hbracket :
      ‖s * (s - 1) * (kwDyf2_P K C).Λ₀ ((nK K : ℂ) * s / 2)
        - 2 * (s - 1) / (nK K : ℂ) + 2 * s * (kwDyf2_P K C).ε / (nK K : ℂ)‖
      ≤ ((3/2) * Msum + 3 / (nK K : ℝ) + 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ)) * ‖s‖^2 := by
    have hnorm_nK : ‖(nK K : ℂ)‖ = (nK K : ℝ) := by
      rw [show ((nK K : ℕ) : ℂ) = ((nK K : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg hnK.le]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) (le_refl _)).trans ?_
    have h1 : ‖s * (s - 1) * (kwDyf2_P K C).Λ₀ ((nK K : ℂ) * s / 2)‖
        ≤ (3/2) * Msum * ‖s‖^2 := by
      rw [norm_mul, norm_mul]
      calc ‖s‖ * ‖s - 1‖ * ‖(kwDyf2_P K C).Λ₀ ((nK K : ℂ) * s / 2)‖
          ≤ ‖s‖ * ((3/2)*‖s‖) * Msum := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hs1 (norm_nonneg _)) hL0
              (norm_nonneg _) ?_
            positivity
        _ = (3/2) * Msum * ‖s‖^2 := by ring
    have h2 : ‖2 * (s - 1) / (nK K : ℂ)‖ ≤ 3 / (nK K : ℝ) * ‖s‖^2 := by
      rw [norm_div, norm_mul, hnorm_nK, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
      calc 2 * ‖s - 1‖ / (nK K : ℝ)
          ≤ 2 * ((3/2)*‖s‖) / (nK K : ℝ) := by gcongr
        _ = 3 * ‖s‖ / (nK K : ℝ) := by ring
        _ ≤ 3 * ‖s‖^2 / (nK K : ℝ) := by gcongr
        _ = 3 / (nK K : ℝ) * ‖s‖^2 := by ring
    have h3 : ‖2 * s * (kwDyf2_P K C).ε / (nK K : ℂ)‖
        ≤ 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ) * ‖s‖^2 := by
      rw [norm_div, norm_mul, norm_mul, hnorm_nK, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
      calc 2 * ‖s‖ * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ)
          ≤ 3 * ‖s‖^2 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ) := by
            gcongr; nlinarith [norm_nonneg s]
        _ = 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ) * ‖s‖^2 := by ring
    calc _ ≤ (3/2) * Msum * ‖s‖^2 + 3 / (nK K : ℝ) * ‖s‖^2
              + 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ) * ‖s‖^2 := by
          gcongr
      _ = ((3/2) * Msum + 3 / (nK K : ℝ) + 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ)) * ‖s‖^2 := by
          ring

  unfold kwDyf2_xiSummand kwDyf2_Bconst
  rw [norm_mul]
  calc ‖((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s‖ * ‖_‖
      ≤ (gapsw80_t9_covolRepr K C ^ (1/2:ℝ) + gapsw80_t9_covolRepr K C ^ (3/2:ℝ))
          * (((3/2) * Msum + 3 / (nK K : ℝ)
              + 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ)) * ‖s‖^2) :=
        mul_le_mul hcovpow hbracket (norm_nonneg _)
          (add_nonneg (Real.rpow_nonneg hcov.le _) (Real.rpow_nonneg hcov.le _))
    _ = _ := by ring

/-- The real constant `max 1 (‖(constK K)⁻¹‖ * ∑ C, kwDyf2_Bconst K C)`, where `constK K` is
`gapsw80_t9_constK K` and the sum runs over the class group of `𝓞 K`. -/
noncomputable def kwDyf2_Aconst : ℝ :=
  max 1 (‖(gapsw80_t9_constK K)⁻¹‖ * ∑ C : ClassGroup (𝓞 K), kwDyf2_Bconst K C)

/-- `1 ≤ kwDyf2_Aconst K`. -/
theorem kwDyf2_one_le_Aconst : 1 ≤ kwDyf2_Aconst K := le_max_left _ _


/-- If `1/2 ≤ s.re ≤ 3/2` and `2 ≤ ‖s‖`, then `‖kwDyf2_xi K s‖ ≤ kwDyf2_Aconst K * ‖s‖ ^ 2`. -/
theorem kwDyf2_norm_xi_le_Aconst_sq {s : ℂ}
    (hre1 : 1/2 ≤ s.re) (hre2 : s.re ≤ 3/2) (hs : 2 ≤ ‖s‖) :
    ‖kwDyf2_xi K s‖ ≤ kwDyf2_Aconst K * ‖s‖^2 := by
  unfold kwDyf2_xi
  rw [norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left
    ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun C _ =>
      kwDyf2_norm_xiSummand_le K C hre1 hre2 hs))) (norm_nonneg _)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- If `2 ≤ ‖s‖`, then `1 ≤ ‖s‖ * Real.log ‖s‖`. -/
theorem kwDyf2_one_le_norm_mul_log {s : ℂ} (hs : 2 ≤ ‖s‖) :
    1 ≤ ‖s‖ * Real.log ‖s‖ := by
  calc (1:ℝ) ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    _ ≤ ‖s‖ * Real.log ‖s‖ :=
        mul_le_mul hs (Real.log_le_log two_pos hs)
          (Real.log_nonneg one_le_two) (by linarith)


/-- The proposition `kwDyf2_XiStripBound` holds. -/
theorem kwDyf2_xiStripBound_proved : kwDyf2_XiStripBound := by
  intro K _ _
  refine ⟨Real.log (kwDyf2_Aconst K) + 2, fun s hre1 hre2 hs => ?_⟩
  have hAK1 : 1 ≤ kwDyf2_Aconst K := kwDyf2_one_le_Aconst K
  have hAKpos : 0 < kwDyf2_Aconst K := lt_of_lt_of_le one_pos hAK1
  have hlogA : 0 ≤ Real.log (kwDyf2_Aconst K) := Real.log_nonneg hAK1
  have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hs
  have hAs2 : 1 ≤ kwDyf2_Aconst K * ‖s‖^2 := by nlinarith
  have hstep1 : Real.log ‖kwDyf2_xi K s‖ ≤ Real.log (kwDyf2_Aconst K * ‖s‖^2) := by
    rcases eq_or_lt_of_le (norm_nonneg (kwDyf2_xi K s)) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg hAs2
    · exact Real.log_le_log h0 (kwDyf2_norm_xi_le_Aconst_sq K hre1 hre2 hs)
  have hsplit : Real.log (kwDyf2_Aconst K * ‖s‖^2)
      = Real.log (kwDyf2_Aconst K) + 2 * Real.log ‖s‖ := by
    rw [Real.log_mul hAKpos.ne' (by positivity), Real.log_pow]
    ring
  have hlogs : Real.log ‖s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
    nlinarith [Real.log_nonneg (le_trans one_le_two hs)]
  calc Real.log ‖kwDyf2_xi K s‖
      ≤ Real.log (kwDyf2_Aconst K) + 2 * Real.log ‖s‖ := hstep1.trans_eq hsplit
    _ ≤ Real.log (kwDyf2_Aconst K) * (‖s‖ * Real.log ‖s‖)
          + 2 * (‖s‖ * Real.log ‖s‖) := by
        gcongr
        exact le_mul_of_one_le_right hlogA (kwDyf2_one_le_norm_mul_log hs)
    _ = (Real.log (kwDyf2_Aconst K) + 2) * ‖s‖ * Real.log ‖s‖ := by ring

/-- If `kwDyf2_XiRightHalfBound` holds, then `gapsw80_t11_XiOrderOneHadamard` holds. -/
theorem kwDyf2_B1_of_C1a (hC1a : kwDyf2_XiRightHalfBound) :
    gapsw80_t11_XiOrderOneHadamard :=
  kwDyf2_B1_of_C1 (kwDyf2_C1_of_C1a_C1b hC1a kwDyf2_xiStripBound_proved)

end FLT.KwDyf2XiStripBoundAttack

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT

namespace Gapsw80T16XiRightHalfBoundProof

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real"

open FLT.Gapsw80T8MellinGammaPartialZeta FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
open FLT.Gapsw80T15XiOrderOneB1Decomp FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.KwDyf2XiEntireOrderDecomp FLT.KwDyf2XiOrderBoundDecomp
open FLT.KwDyf2XiStripBoundAttack FLT.KwDyf2RealGammaLogBound

p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

/-- For a number field `K`, `1 ≤ |(discr K : ℝ)|`, where `discr K` is the absolute discriminant. -/
theorem gapsw80_t16_one_le_abs_discr : (1:ℝ) ≤ |(discr K : ℝ)| := by
  have h : (1:ℤ) ≤ |discr K| := abs_pos.mpr (NumberField.discr_ne_zero K)
  exact_mod_cast h

/-- If `0 < s.re`, then `Complex.Gammaℂ s ≠ 0`. -/
theorem gapsw80_t16_Gammaℂ_ne_zero {s : ℂ} (hs : 0 < s.re) :
    Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_)
    (Complex.Gamma_ne_zero_of_re_pos hs)
  refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
  exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

/-- The `n`-th coefficient of the Dedekind zeta Dirichlet series of `K`: the number of ideals of
`𝓞 K` of absolute norm `n`, as a complex number. -/
noncomputable def gapsw80_t16_zetaCoeff (n : ℕ) : ℂ :=
  (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)

/-- The sum over `n` of the norms of the terms `LSeries.term (gapsw80_t16_zetaCoeff K) (3/2) n` of
the Dedekind zeta Dirichlet series evaluated at the real point `3/2`. -/
noncomputable def gapsw80_t16_Mzeta : ℝ :=
  ∑' n, ‖LSeries.term (gapsw80_t16_zetaCoeff K) ((3/2 : ℝ) : ℂ) n‖

/-- The series `n ↦ ‖LSeries.term (gapsw80_t16_zetaCoeff K) (3/2) n‖` is summable. -/
theorem gapsw80_t16_Mzeta_summable :
    Summable (fun n => ‖LSeries.term (gapsw80_t16_zetaCoeff K) ((3/2 : ℝ) : ℂ) n‖) :=
  (gapsw80_t10_LSeriesSummable_dedekindZeta K
    (s := ((3/2 : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; norm_num)).norm

/-- If `3/2 ≤ s.re`, then for every `n` the norm of `LSeries.term (gapsw80_t16_zetaCoeff K) s n` is
at most the norm of `LSeries.term (gapsw80_t16_zetaCoeff K) (3/2) n`. -/
theorem gapsw80_t16_term_norm_le {s : ℂ} (hs : 3/2 ≤ s.re) (n : ℕ) :
    ‖LSeries.term (gapsw80_t16_zetaCoeff K) s n‖
      ≤ ‖LSeries.term (gapsw80_t16_zetaCoeff K) ((3/2 : ℝ) : ℂ) n‖ := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [LSeries.term_zero]
  · have hn1 : 1 ≤ (n:ℝ) := Nat.one_le_cast.mpr hpos
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hpos.ne', ite_eq_right hpos.ne',
      Complex.ofReal_re]
    exact div_le_div_of_nonneg_left (norm_nonneg _)
      (Real.rpow_pos_of_pos (by exact_mod_cast hpos) _)
      (Real.rpow_le_rpow_of_exponent_le hn1 hs)

/-- If `3/2 ≤ s.re`, then the norm of the sum over ideal classes `C` of
`gapsw80_t8_partialDedekindZeta K C s` is at most `gapsw80_t16_Mzeta K`. -/
theorem gapsw80_t16_norm_sum_partialZeta_le {s : ℂ} (hs : 3/2 ≤ s.re) :
    ‖∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s‖
      ≤ gapsw80_t16_Mzeta K := by
  have h1 : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  rw [gapsw80_t10_sum_partialDedekindZeta_eq K h1]

  have hsum := (gapsw80_t16_Mzeta_summable K).of_nonneg_of_le
    (fun _ => norm_nonneg _) (gapsw80_t16_term_norm_le K hs)
  unfold NumberField.dedekindZeta
  calc ‖LSeries _ s‖
      ≤ ∑' n, ‖LSeries.term (gapsw80_t16_zetaCoeff K) s n‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ gapsw80_t16_Mzeta K :=
        hasSum_le (gapsw80_t16_term_norm_le K hs) hsum.hasSum
          (gapsw80_t16_Mzeta_summable K).hasSum

/-- If `3/2 ≤ s.re` and `2 ≤ ‖s‖`, then `Real.log ‖Complex.Gamma (s / 2)‖ ≤ ‖s‖ * Real.log ‖s‖`. -/
theorem gapsw80_t16_log_norm_Gamma_half_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖Complex.Gamma (s / 2)‖ ≤ ‖s‖ * Real.log ‖s‖ := by
  have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hns
  have h1nml : 1 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_one_le_norm_mul_log hns
  have hshalf_norm : ‖s / 2‖ = ‖s‖ / 2 := by
    rw [norm_div]; simp
  rcases le_or_gt 2 s.re with hge2 | hlt2
  · have hre : 1 ≤ (s / 2).re := by
      rw [Complex.div_ofNat_re]; linarith
    have hstep := kwDyf2_log_norm_Gamma_le_norm_mul_log_norm hre
    refine hstep.trans ?_
    rw [hshalf_norm]
    exact kwDyf2_monotoneOn_mul_log (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) (by linarith)
  · have hshalf_ne : s / 2 ≠ 0 := by
      intro h; rw [div_eq_zero_iff] at h
      rcases h with h | h
      · exact (gapsw80_t15_norm_ge_two_ne_zero_one hns).1 h
      · exact two_ne_zero h
    have hshift : Complex.Gamma (s / 2) = Complex.Gamma (s / 2 + 1) / (s / 2) := by
      rw [eq_div_iff hshalf_ne, mul_comm (Complex.Gamma (s/2)) (s/2),
          Complex.Gamma_add_one (s / 2) hshalf_ne]
    have hre1 : 1 ≤ (s / 2 + 1).re := by
      rw [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]; linarith
    have hnorm1 : ‖s / 2 + 1‖ ≤ ‖s‖ := by
      calc ‖s / 2 + 1‖ ≤ ‖s / 2‖ + 1 := by simpa using norm_add_le (s / 2) 1
        _ = ‖s‖ / 2 + 1 := by rw [hshalf_norm]
        _ ≤ ‖s‖ := by linarith
    have h1le1 : 1 ≤ ‖s / 2 + 1‖ :=
      le_trans (by exact_mod_cast hre1) (Complex.re_le_norm _)
    have hlogG1' : Real.log ‖Complex.Gamma (s / 2 + 1)‖ ≤ ‖s‖ * Real.log ‖s‖ :=
      (kwDyf2_log_norm_Gamma_le_norm_mul_log_norm hre1).trans
        (kwDyf2_monotoneOn_mul_log (Set.mem_Ici.mpr h1le1)
          (Set.mem_Ici.mpr (by linarith)) hnorm1)
    have h1shalf : (1:ℝ) ≤ ‖s / 2‖ := by rw [hshalf_norm]; linarith
    have hlogs2 : -Real.log ‖s / 2‖ ≤ 0 :=
      neg_nonpos_of_nonneg (Real.log_nonneg h1shalf)
    rw [hshift, norm_div, Real.log_div
      (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by linarith)))
      (by rw [hshalf_norm]; positivity)]
    linarith [hlogG1', hlogs2]

/-- If `3/2 ≤ s.re` and `2 ≤ ‖s‖`, then `Real.log ‖Complex.Gammaℝ s‖ ≤ ‖s‖ * Real.log ‖s‖`. -/
theorem gapsw80_t16_log_norm_Gammaℝ_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖Complex.Gammaℝ s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
  have hπ : ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi ^ (-s.re / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      Complex.div_ofNat_re, Complex.neg_re]
  have hπle : Real.log ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ ≤ 0 := by
    rw [hπ, Real.log_rpow Real.pi_pos]
    have hlogπ : 0 ≤ Real.log Real.pi :=
      Real.log_nonneg (one_le_two.trans Real.two_le_pi)
    nlinarith
  rw [Complex.Gammaℝ_def, norm_mul,
    Real.log_mul (by rw [hπ]; positivity)
      (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos
        (by rw [Complex.div_ofNat_re]; linarith)))]
  linarith [gapsw80_t16_log_norm_Gamma_half_le h32 hns, hπle]

/-- If `3/2 ≤ s.re` and `2 ≤ ‖s‖`, then `Real.log ‖Complex.Gammaℂ s‖ ≤ 2 * (‖s‖ * Real.log ‖s‖)`.
-/
theorem gapsw80_t16_log_norm_Gammaℂ_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖Complex.Gammaℂ s‖ ≤ 2 * (‖s‖ * Real.log ‖s‖) := by
  have h1nml : 1 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_one_le_norm_mul_log hns
  have hre1 : 1 ≤ s.re := by linarith
  have hΓ := kwDyf2_log_norm_Gamma_le_norm_mul_log_norm hre1
  have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
  have h2πpos : (0:ℝ) < 2 * Real.pi := by positivity
  have hpow : ‖(2 * (↑Real.pi : ℂ)) ^ (-s)‖ = (2 * Real.pi) ^ (-s.re) := by
    have : ((2 * (↑Real.pi : ℂ)) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos h2πpos, Complex.neg_re]
  have hpow_le : Real.log ‖(2 * (↑Real.pi : ℂ)) ^ (-s)‖ ≤ 0 := by
    rw [hpow, Real.log_rpow h2πpos]
    have hlog2π : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by linarith [Real.two_le_pi])
    nlinarith
  have hΓne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpow_ne : ‖(2 * (↑Real.pi : ℂ)) ^ (-s)‖ ≠ 0 := by
    rw [hpow]
    positivity
  rw [Complex.Gammaℂ_def, norm_mul, norm_mul,
    Real.log_mul (mul_ne_zero (by simp) hpow_ne) (norm_ne_zero_iff.mpr hΓne),
    Real.log_mul (by simp) hpow_ne]
  have hlog2' : Real.log ‖(2:ℂ)‖ = Real.log 2 := by simp
  linarith [hΓ, hpow_le, h1nml, hlog2]

/-- The real number `r₁ + 2 * r₂`, where `r₁` and `r₂` are the numbers of real and complex places
of `K`. -/
noncomputable def gapsw80_t16_CGamma : ℝ :=
  (nrRealPlaces K : ℝ) + 2 * (nrComplexPlaces K : ℝ)

/-- If `3/2 ≤ s.re` and `2 ≤ ‖s‖`, then
`Real.log ‖gapsw80_t9_gammaFactor K s‖ ≤ gapsw80_t16_CGamma K * (‖s‖ * Real.log ‖s‖)`. -/
theorem gapsw80_t16_log_norm_gammaFactor_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖gapsw80_t9_gammaFactor K s‖
      ≤ gapsw80_t16_CGamma K * (‖s‖ * Real.log ‖s‖) := by
  have hnml : 0 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_norm_mul_log_norm_nonneg hns
  have hRne : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hCne : Complex.Gammaℂ s ≠ 0 := gapsw80_t16_Gammaℂ_ne_zero (by linarith)
  unfold gapsw80_t9_gammaFactor gapsw80_t16_CGamma
  rw [norm_mul, norm_pow, norm_pow,
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hRne))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hCne)),
    Real.log_pow, Real.log_pow]
  have hRn : (nrRealPlaces K : ℝ) * Real.log ‖Complex.Gammaℝ s‖
      ≤ (nrRealPlaces K : ℝ) * (‖s‖ * Real.log ‖s‖) :=
    mul_le_mul_of_nonneg_left (gapsw80_t16_log_norm_Gammaℝ_le h32 hns) (Nat.cast_nonneg _)
  have hCn : (nrComplexPlaces K : ℝ) * Real.log ‖Complex.Gammaℂ s‖
      ≤ (nrComplexPlaces K : ℝ) * (2 * (‖s‖ * Real.log ‖s‖)) :=
    mul_le_mul_of_nonneg_left (gapsw80_t16_log_norm_Gammaℂ_le h32 hns) (Nat.cast_nonneg _)
  linarith

/-- The real number `Real.log |(discr K : ℝ)| / (2 * Real.log 2)`, where `discr K` is the absolute
discriminant of `K`. -/
noncomputable def gapsw80_t16_CDisc : ℝ :=
  Real.log |(discr K : ℝ)| / (2 * Real.log 2)

/-- If `2 ≤ ‖s‖`, then
`Real.log ‖(|(discr K : ℝ)| : ℂ) ^ (s / 2)‖ ≤ gapsw80_t16_CDisc K * (‖s‖ * Real.log ‖s‖)`. -/
theorem gapsw80_t16_log_norm_discrPow_le {s : ℂ} (hns : 2 ≤ ‖s‖) :
    Real.log ‖((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)‖
      ≤ gapsw80_t16_CDisc K * (‖s‖ * Real.log ‖s‖) := by
  have hD1 : (1:ℝ) ≤ |(discr K : ℝ)| := gapsw80_t16_one_le_abs_discr K
  have hDpos : (0:ℝ) < |(discr K : ℝ)| := lt_of_lt_of_le one_pos hD1
  have hlogD : 0 ≤ Real.log |(discr K : ℝ)| := Real.log_nonneg hD1
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlogn2 : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log two_pos hns
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hDpos),
    Real.log_rpow (by exact_mod_cast hDpos), Complex.div_ofNat_re]
  unfold gapsw80_t16_CDisc
  have hkey : s.re * Real.log 2 * Real.log |(discr K : ℝ)|
      ≤ Real.log |(discr K : ℝ)| * (‖s‖ * Real.log ‖s‖) := by
    nlinarith [mul_le_mul (Complex.re_le_norm s) hlogn2 hlog2.le (by linarith : (0:ℝ) ≤ ‖s‖)]
  calc s.re / 2 * Real.log |(discr K : ℝ)|
      = s.re * Real.log 2 * Real.log |(discr K : ℝ)| / (2 * Real.log 2) := by
        field_simp
    _ ≤ Real.log |(discr K : ℝ)| * (‖s‖ * Real.log ‖s‖) / (2 * Real.log 2) := by
        gcongr
    _ = Real.log |(discr K : ℝ)| / (2 * Real.log 2) * (‖s‖ * Real.log ‖s‖) := by ring

/-- If `0 < s.re`, then `0 < ‖gapsw80_t9_gammaFactor K s‖`. -/
theorem gapsw80_t16_norm_gammaFactor_pos {s : ℂ} (hs : 0 < s.re) :
    0 < ‖gapsw80_t9_gammaFactor K s‖ := by
  unfold gapsw80_t9_gammaFactor
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_pos (pow_pos (norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos hs)) _)
    (pow_pos (norm_pos_iff.mpr (gapsw80_t16_Gammaℂ_ne_zero hs)) _)

/-- The nonnegative real number `max (2 + CDisc + CGamma + max (Real.log Mzeta) 0) 0`, with
`CDisc`, `CGamma`, `Mzeta` the constants `gapsw80_t16_CDisc K`, `gapsw80_t16_CGamma K`,
`gapsw80_t16_Mzeta K`. -/
noncomputable def gapsw80_t16_Cassem : ℝ :=
  max (2 + gapsw80_t16_CDisc K + gapsw80_t16_CGamma K
    + max (Real.log (gapsw80_t16_Mzeta K)) 0) 0

/-- `0 ≤ gapsw80_t16_Cassem K`. -/
theorem gapsw80_t16_Cassem_nonneg : 0 ≤ gapsw80_t16_Cassem K := le_max_right _ _

/-- The proposition `kwDyf2_XiRightHalfBound` holds. -/
theorem gapsw80_t16_xiRightHalfBound_proved : kwDyf2_XiRightHalfBound := by
  intro K _ _
  refine ⟨gapsw80_t16_Cassem K, fun s h32 hns => ?_⟩
  have hnml : 0 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_norm_mul_log_norm_nonneg hns
  have h1nml : 1 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_one_le_norm_mul_log hns
  by_cases hξ0 : kwDyf2_xi K s = 0
  · rw [hξ0, norm_zero, Real.log_zero]
    exact mul_nonneg (mul_nonneg (gapsw80_t16_Cassem_nonneg K) (by linarith))
      (Real.log_nonneg (by linarith))
  have h1 : 1 < s.re := lt_of_lt_of_le (by norm_num) h32
  obtain ⟨hs0, hs1⟩ := gapsw80_t15_norm_ge_two_ne_zero_one hns
  rw [kwDyf2_xi_eq K hs0 hs1, gapsw80_t9_completedDedekindZeta_eq_sum K h1]
  have hsum_pos : (0:ℝ) < ‖∑ C, gapsw80_t8_partialDedekindZeta K C s‖ := by
    refine norm_pos_iff.mpr fun habs => hξ0 ?_
    rw [kwDyf2_xi_eq K hs0 hs1, gapsw80_t9_completedDedekindZeta_eq_sum K h1, habs]
    ring
  have hpoly_pos : (0:ℝ) < ‖s * (s - 1)‖ := by
    rw [norm_mul]
    exact mul_pos (norm_pos_iff.mpr hs0) (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))
  have hD1 : (1:ℝ) ≤ |(discr K : ℝ)| := gapsw80_t16_one_le_abs_discr K
  have hDpow_pos : (0:ℝ) < ‖((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast lt_of_lt_of_le one_pos hD1)]
    positivity
  have hGamma_pos := gapsw80_t16_norm_gammaFactor_pos K (s := s) (by linarith)
  rw [show s * (s - 1) * (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
        * gapsw80_t9_gammaFactor K s
        * ∑ C, gapsw80_t8_partialDedekindZeta K C s)
      = (s * (s - 1)) * (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2))
        * (gapsw80_t9_gammaFactor K s)
        * (∑ C, gapsw80_t8_partialDedekindZeta K C s) from by ring,
    norm_mul, norm_mul, norm_mul,
    Real.log_mul (by positivity) hsum_pos.ne',
    Real.log_mul (by positivity) hGamma_pos.ne',
    Real.log_mul hpoly_pos.ne' hDpow_pos.ne']
  have bZeta : Real.log ‖∑ C, gapsw80_t8_partialDedekindZeta K C s‖
      ≤ max (Real.log (gapsw80_t16_Mzeta K)) 0 * (‖s‖ * Real.log ‖s‖) :=
      ((Real.log_le_log hsum_pos (gapsw80_t16_norm_sum_partialZeta_le K h32)).trans
        (le_max_left _ _)).trans (le_mul_of_one_le_right (le_max_right _ _) h1nml)
  calc Real.log ‖s * (s - 1)‖ + Real.log ‖((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)‖
        + Real.log ‖gapsw80_t9_gammaFactor K s‖
        + Real.log ‖∑ C, gapsw80_t8_partialDedekindZeta K C s‖
      ≤ 2 * ‖s‖ * Real.log ‖s‖
        + gapsw80_t16_CDisc K * (‖s‖ * Real.log ‖s‖)
        + gapsw80_t16_CGamma K * (‖s‖ * Real.log ‖s‖)
        + max (Real.log (gapsw80_t16_Mzeta K)) 0 * (‖s‖ * Real.log ‖s‖) := by
        linarith [gapsw80_t15_sat_polynomialFactor_orderBound s hns,
          gapsw80_t16_log_norm_discrPow_le K hns, gapsw80_t16_log_norm_gammaFactor_le K h32 hns]
    _ = (2 + gapsw80_t16_CDisc K + gapsw80_t16_CGamma K
          + max (Real.log (gapsw80_t16_Mzeta K)) 0) * (‖s‖ * Real.log ‖s‖) := by ring
    _ ≤ gapsw80_t16_Cassem K * (‖s‖ * Real.log ‖s‖) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hnml
    _ = gapsw80_t16_Cassem K * ‖s‖ * Real.log ‖s‖ := by ring

/-- The proposition `gapsw80_t11_XiOrderOneHadamard` holds: for every number field `K` there is an
entire function equal to `s * (s - 1)` times the completed Dedekind zeta function away from `0` and
`1`, with `Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖` for `2 ≤ ‖s‖`. -/
theorem gapsw80_t16_B1_closed : gapsw80_t11_XiOrderOneHadamard :=
  kwDyf2_B1_of_C1a gapsw80_t16_xiRightHalfBound_proved

end FLT.Gapsw80T16XiRightHalfBoundProof

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT

namespace Gapsw80T43CompletedZetaRealSuperlinearProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T16XiRightHalfBoundProof
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T30D2d0cLocalEulerFactorProof
open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
open FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real Nat P2MW.S_NumberField_exists_completedDedekindZeta_package.Nat Filter.Nat Set.Nat"

/-- The real constant `1 + 2 * Real.log (2 * Real.pi)`. -/
noncomputable def gapsw80_t43_L₀ : ℝ := 1 + 2 * Real.log (2 * Real.pi)

/-- For a number field `K` and real `σ ≥ 0`, `1 ≤ ‖(|discr K| : ℂ) ^ ((σ : ℂ) / 2)‖`. -/
theorem gapsw80_t43_one_le_norm_discrPow (K : Type) [Field K] [NumberField K]
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (1:ℝ) ≤ ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ := by
  rw [gapsw80_t10_discrCoercion,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_of_lt_of_le one_pos (gapsw80_t16_one_le_abs_discr K))]
  have hre : ((σ:ℂ) / 2).re = σ / 2 := by
    simp [Complex.ofReal_re]
  rw [hre]
  exact Real.one_le_rpow (gapsw80_t16_one_le_abs_discr K) (by linarith)

/-- For a natural number `n`, `‖Complex.Gamma ((n + 1 : ℕ) : ℂ)‖ = (n ! : ℝ)`. -/
theorem gapsw80_t43_norm_Gamma_nat_succ (n : ℕ) :
    ‖Complex.Gamma ((n + 1 : ℕ) : ℂ)‖ = (n ! : ℝ) := by
  rw [show (((n + 1 : ℕ) : ℂ)) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
    show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]
  exact abs_of_pos (by exact_mod_cast n.factorial_pos)

/-- For a number field `K` and real `σ > 1`, `1 ≤ ‖dedekindZeta K (σ : ℂ)‖`. -/
theorem gapsw80_t43_one_le_norm_dedekindZeta_ofReal (K : Type) [Field K]
    [NumberField K] {σ : ℝ} (hσ : 1 < σ) :
    (1:ℝ) ≤ ‖dedekindZeta K (σ:ℂ)‖ := by
  have hre : 1 < (σ:ℂ).re := by rwa [Complex.ofReal_re]
  have hsum : LSeriesSummable
      (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (σ:ℂ) :=
    gapsw80_t10_LSeriesSummable_dedekindZeta K hre

  have hterm_re_nonneg : ∀ n,
      0 ≤ (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) n).re := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      have hcpow : (n:ℂ)^(σ:ℂ) = (((n:ℝ)^σ : ℝ):ℂ) := by
        rw [show ((n:ℕ):ℂ) = (((n:ℕ):ℝ):ℂ) from (Complex.ofReal_natCast n).symm,
          ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      rw [hcpow, show ((Nat.card _ : ℕ):ℂ) = (((Nat.card _ : ℕ):ℝ):ℂ) from
          (Complex.ofReal_natCast _).symm, ← Complex.ofReal_div, Complex.ofReal_re]
      positivity

  have hterm1_re :
      (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) 1).re = 1 := by
    rw [LSeries.term_of_ne_zero one_ne_zero]
    simp only [Nat.cast_one, Complex.one_cpow, div_one]
    have : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} = 1 := by
      simp [Ideal.absNorm_eq_one_iff]
    rw [this]; simp

  have hHS_re : HasSum
      (fun n => (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) n).re)
      (dedekindZeta K (σ:ℂ)).re :=
    Complex.hasSum_re hsum.hasSum
  calc (1:ℝ)
      = (LSeries.term _ (σ:ℂ) 1).re := hterm1_re.symm
    _ ≤ (dedekindZeta K (σ:ℂ)).re :=
        le_hasSum hHS_re 1 (fun n _ => hterm_re_nonneg n)
    _ ≤ ‖dedekindZeta K (σ:ℂ)‖ := Complex.re_le_norm _

/-- `Real.log Real.pi ≤ 2 * Real.log (2 * Real.pi)`. -/
theorem gapsw80_t43_log_pi_le : Real.log Real.pi ≤ 2 * Real.log (2 * Real.pi) := by
  have h1 : Real.log Real.pi ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log Real.pi_pos (by linarith [Real.pi_pos])
  have h2 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

/-- For a natural number `m ≥ 1`, `m * Real.log m - m ≤ Real.log (m ! : ℝ)`. -/
theorem gapsw80_t43_stirling_core {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) := by
  have hlog_m : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have h2π : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have key := Stirling.le_log_factorial_stirling (Nat.one_le_iff_ne_zero.mp hm)
  linarith

/-- For a natural number `m ≥ 1`,
`m * Real.log m - gapsw80_t43_L₀ * (m + 1) ≤ Real.log ‖Complex.Gammaℝ (2 * (m + 1))‖`. -/
theorem gapsw80_t43_log_norm_Gammaℝ_ge {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - gapsw80_t43_L₀ * ((m:ℝ) + 1)
      ≤ Real.log ‖Complex.Gammaℝ ((2 * ((m:ℝ) + 1) : ℝ):ℂ)‖ := by
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσ
  have hσ2 : σ / 2 = (m:ℝ) + 1 := by rw [hσ]; ring
  have hm1pos : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have harg : ((σ:ℂ)/2) = ((m + 1 : ℕ) : ℂ) := by
    rw [hσ]; push_cast; ring

  have heq : ‖Complex.Gammaℝ (σ:ℂ)‖
      = Real.pi ^ (-((m:ℝ)+1)) * (m ! : ℝ) := by
    rw [Complex.Gammaℝ_def, norm_mul,
      show (-(σ:ℂ)/2) = -((σ:ℂ)/2) from by ring, harg,
      gapsw80_t43_norm_Gamma_nat_succ m,
      show (-((m+1:ℕ):ℂ)) = ((-((m:ℝ)+1) : ℝ):ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.ofReal_re]
  rw [heq, Real.log_mul (by positivity) (by exact_mod_cast m.factorial_pos.ne'),
    Real.log_rpow Real.pi_pos]
  have hstir : (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) :=
    gapsw80_t43_stirling_core hm
  have hπ : Real.log Real.pi ≤ 2 * Real.log (2 * Real.pi) := gapsw80_t43_log_pi_le
  unfold gapsw80_t43_L₀
  nlinarith [hm1pos]

/-- For a natural number `m ≥ 1`,
`m * Real.log m - gapsw80_t43_L₀ * (m + 1) ≤ Real.log ‖Complex.Gammaℂ (2 * (m + 1))‖`. -/
theorem gapsw80_t43_log_norm_Gammaℂ_ge {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - gapsw80_t43_L₀ * ((m:ℝ) + 1)
      ≤ Real.log ‖Complex.Gammaℂ ((2 * ((m:ℝ) + 1) : ℝ):ℂ)‖ := by
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσ
  have hσnat : σ = ((2*m+1 : ℕ):ℝ) + 1 := by push_cast; rw [hσ]; ring
  have h2πpos : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have harg : ((σ:ℝ):ℂ) = (((2*m+1) + 1 : ℕ) : ℂ) := by
    rw [hσ]; push_cast; ring

  have heq : ‖Complex.Gammaℂ (σ:ℂ)‖
      = 2 * (2*Real.pi) ^ (-σ) * ((2*m+1)! : ℝ) := by
    rw [Complex.Gammaℂ_def, norm_mul, norm_mul, harg,
      gapsw80_t43_norm_Gamma_nat_succ (2*m+1),
      show (-(((2*m+1)+1:ℕ):ℂ)) = (((-σ):ℝ):ℂ) from by rw [hσ]; push_cast; ring,
      show ((2:ℂ)*(Real.pi:ℂ)) = (((2*Real.pi:ℝ)):ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos h2πpos, Complex.ofReal_re]
    norm_num
  rw [heq, Real.log_mul (by positivity) (by exact_mod_cast (2*m+1).factorial_pos.ne'),
    Real.log_mul (by norm_num) (by positivity), Real.log_rpow h2πpos]

  have hfac_le : (m ! : ℝ) ≤ ((2*m+1)! : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hlogfac : Real.log (m ! : ℝ) ≤ Real.log ((2*m+1)! : ℝ) :=
    Real.log_le_log (by exact_mod_cast m.factorial_pos) hfac_le
  have hstir : (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) :=
    gapsw80_t43_stirling_core hm
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  unfold gapsw80_t43_L₀
  nlinarith

/-- For a number field `K`, `1 ≤ nrRealPlaces K + nrComplexPlaces K`. -/
theorem gapsw80_t43_one_le_nrPlaces_sum (K : Type) [Field K] [NumberField K] :
    1 ≤ nrRealPlaces K + nrComplexPlaces K := by
  have hk : 1 ≤ nrRealPlaces K + 2 * nrComplexPlaces K := by
    rw [card_add_two_mul_card_eq_rank]; exact Module.finrank_pos
  omega

/-- For every real `D` there is a natural number `m ≥ 2` with `D * (m + 1) < m * Real.log m`. -/
theorem gapsw80_t43_exists_m_superlinear (D : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ D * ((m:ℝ) + 1) < (m:ℝ) * Real.log m := by
  set D' := max D 0
  have hD'0 : 0 ≤ D' := le_max_right _ _
  have hlog : ∀ᶠ m : ℕ in atTop, 2 * D' < Real.log (m:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (2*D')
  obtain ⟨m, hmD, hm2⟩ := (hlog.and (eventually_ge_atTop 2)).exists
  refine ⟨m, hm2, ?_⟩
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  calc D * ((m:ℝ) + 1)
      ≤ D' * ((m:ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ D' * (2 * (m:ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hD'0
        have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
        linarith
    _ = (2 * D') * (m:ℝ) := by ring
    _ < Real.log (m:ℝ) * (m:ℝ) := mul_lt_mul_of_pos_right hmD hm0
    _ = (m:ℝ) * Real.log m := by ring


/-- The proposition `gapsw80_t42_CompletedZetaRealSuperlinear` holds: for every number field `K`
and real `C` there is `s ∉ {0, 1}` with `2 ≤ ‖s‖` and
`C * ‖s‖ < Real.log ‖s * (s - 1) * gapsw80_t9_completedDedekindZeta K s‖`. -/
theorem gapsw80_t43_SL_closed : gapsw80_t42_CompletedZetaRealSuperlinear := by
  intro K _ _ C
  obtain ⟨m, hm2, hmD⟩ := gapsw80_t43_exists_m_superlinear (2 * |C| + gapsw80_t43_L₀)
  have hm1 : 1 ≤ m := by omega
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσdef
  have hσ4 : (4:ℝ) ≤ σ := by
    have : (2:ℝ) ≤ (m:ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm1
    rw [hσdef]; linarith
  have hσ1 : (1:ℝ) < σ := by linarith
  have hσ0 : (0:ℝ) < σ := by linarith
  have hnorm_s : ‖(σ:ℂ)‖ = σ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos hσ0

  refine ⟨(σ:ℂ), ?_, ?_, ?_, ?_⟩
  · rw [hnorm_s]; linarith
  · exact_mod_cast hσ0.ne'
  · intro h; rw [Complex.ofReal_eq_one] at h; linarith

  have hre : (1:ℝ) < (σ:ℂ).re := by rwa [Complex.ofReal_re]

  set L : ℝ := (m:ℝ) * Real.log m - gapsw80_t43_L₀ * ((m:ℝ) + 1) with hLdef
  have hL_pos : 0 ≤ L := by
    have h2C : 0 ≤ 2 * |C| * ((m:ℝ)+1) := by positivity
    rw [hLdef]; linarith [hmD]
  have hCL : C * σ < L := by
    rw [hσdef, hLdef]
    have habs : C * (2 * ((m:ℝ)+1)) ≤ |C| * (2 * ((m:ℝ)+1)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    linarith [hmD]

  rw [hnorm_s, gapsw80_t10_completedDedekindZeta_eq_T1 K hre,
    gapsw80_t1_completedDedekindZeta]
  refine lt_of_lt_of_le hCL ?_

  have hDge1 : (1:ℝ) ≤ ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ :=
    gapsw80_t43_one_le_norm_discrPow K hσ0.le
  have hZge1 : (1:ℝ) ≤ ‖dedekindZeta K (σ:ℂ)‖ :=
    gapsw80_t43_one_le_norm_dedekindZeta_ofReal K hσ1
  have hGRne : Complex.Gammaℝ (σ:ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; exact hσ0)
  have hGCne : Complex.Gammaℂ (σ:ℂ) ≠ 0 :=
    gapsw80_t16_Gammaℂ_ne_zero (by rw [Complex.ofReal_re]; exact hσ0)
  have hGRpos : (0:ℝ) < ‖Complex.Gammaℝ (σ:ℂ)‖ := norm_pos_iff.mpr hGRne
  have hGCpos : (0:ℝ) < ‖Complex.Gammaℂ (σ:ℂ)‖ := norm_pos_iff.mpr hGCne
  have hGRL : L ≤ Real.log ‖Complex.Gammaℝ (σ:ℂ)‖ := by
    rw [hLdef]; exact gapsw80_t43_log_norm_Gammaℝ_ge hm1
  have hGCL : L ≤ Real.log ‖Complex.Gammaℂ (σ:ℂ)‖ := by
    rw [hLdef]; exact gapsw80_t43_log_norm_Gammaℂ_ge hm1
  have hs1 : ‖(σ:ℂ) - 1‖ = σ - 1 := by
    rw [show ((σ:ℂ) - 1) = (((σ - 1 : ℝ)):ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by linarith)

  simp only [norm_mul, norm_pow, hnorm_s, hs1]

  have hall_pos :
      (0:ℝ) < σ * (σ - 1) *
        (‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖) := by
    have : (0:ℝ) < σ - 1 := by linarith
    positivity

  rw [show σ * (σ - 1) *
        (‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖)
      = (σ * (σ - 1)) * ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖ by ring,
    Real.log_mul (by positivity) (by linarith [hZge1]),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by linarith [hDge1]),
    Real.log_pow, Real.log_pow]

  have hlog_ss1 : 0 ≤ Real.log (σ * (σ - 1)) :=
    Real.log_nonneg (by nlinarith)
  have hlogD : 0 ≤ Real.log ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ :=
    Real.log_nonneg hDge1
  have hlogZ : 0 ≤ Real.log ‖dedekindZeta K (σ:ℂ)‖ := Real.log_nonneg hZge1

  have hr1 : (nrRealPlaces K : ℝ) * L
      ≤ (nrRealPlaces K : ℝ) * Real.log ‖Complex.Gammaℝ (σ:ℂ)‖ :=
    mul_le_mul_of_nonneg_left hGRL (Nat.cast_nonneg _)
  have hr2 : (nrComplexPlaces K : ℝ) * L
      ≤ (nrComplexPlaces K : ℝ) * Real.log ‖Complex.Gammaℂ (σ:ℂ)‖ :=
    mul_le_mul_of_nonneg_left hGCL (Nat.cast_nonneg _)
  have hrsum : (1:ℝ) ≤ (nrRealPlaces K : ℝ) + (nrComplexPlaces K : ℝ) := by
    exact_mod_cast gapsw80_t43_one_le_nrPlaces_sum K
  nlinarith [mul_nonneg (Nat.cast_nonneg (nrRealPlaces K)) hL_pos,
    mul_nonneg (Nat.cast_nonneg (nrComplexPlaces K)) hL_pos]

end FLT.Gapsw80T43CompletedZetaRealSuperlinearProof

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition FLT.Gapsw80T9ClassSumA1Closure FLT.Gapsw80T10DedekindZetaBridgeA1Discharge FLT.Gapsw80T16XiRightHalfBoundProof FLT.Gapsw80T36D1appXiEndpointResidueProof FLT.Gapsw80T43CompletedZetaRealSuperlinearProof FLT.Gapsw80T11ExplicitFormulaA34Decomp FLT.Gapsw80T32D1aBoundaryCaseDecomp FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof in

/-- For a number field `K` there is a function `Λ : ℂ → ℂ`, differentiable off `{0, 1}`, satisfying
`Λ (1 - s) = Λ s` for `s ≠ 0, 1`, and equal for `1 < s.re` to
`|discr K| ^ (s / 2) * Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂ * dedekindZeta K s`, such that
`s * (s - 1) * Λ s` extends to an entire function `ξ` of order at most one
(`Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖` for `2 ≤ ‖s‖`), every such entire extension is nonzero
at `0` and `1`, and for every real `C` there is `s ∉ {0, 1}` with `2 ≤ ‖s‖` and
`C * ‖s‖ < Real.log ‖s * (s - 1) * Λ s‖`. -/
theorem solution (K : Type) [Field K] [NumberField K] :
    ∃ Λ : ℂ → ℂ,
      DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s) ∧
      (∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) ∧
      (∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) ∧
        ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) ∧
      (∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) → ξ 0 ≠ 0 ∧ ξ 1 ≠ 0) ∧
      (∀ C : ℝ, ∃ s : ℂ, 2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
        C * ‖s‖ < Real.log ‖s * (s - 1) * Λ s‖) := by
  refine ⟨gapsw80_t9_completedDedekindZeta K, ?_, ?_, ?_, gapsw80_t16_B1_closed K,
    gapsw80_t36_D1app_closed K, gapsw80_t43_SL_closed K⟩
  · exact gapsw80_t9_differentiableOn_completedDedekindZeta K
  · exact fun s hs0 hs1 => gapsw80_t9_completedDedekindZeta_FE K hs0 hs1
  · intro s hs
    rw [gapsw80_t10_completedDedekindZeta_eq_T1 K hs]
    rfl
