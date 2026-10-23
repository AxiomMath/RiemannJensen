module

public import RiemannJensen.Dedekind.CompletedZetaIdealTheta

/-!
# The Hecke theta kernel

The ideal-lattice theta function averaged over a fundamental domain of the unit group, its
transformation law, the bridge from the trace-dual ideal to the dual lattice, and the closed
weak functional equation of the Hecke kernel.

## Main definitions

* `gapsw80_t5_heckeKernel`: the theta function averaged over a fundamental domain of the unit
  group.
* `gapsw80_t6_traceDualIdeal`: the trace-dual ideal of an ideal.
-/

@[expose] public section

namespace P2MW.S_NumberField_exists_completedDedekindZeta_package

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation"

section

noncomputable section

namespace FLT

namespace Gapsw80T5HeckeThetaKernel

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "NumberField.mixedEmbedding.fundamentalCone P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding.fundamentalCone"
p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"

open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T4MultiVarIdealThetaTransformation

p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

/-- For a unit `η` of `𝓞 K`, the function on infinite places sending `w` to `(w η)^2`. -/
def gapsw80_t5_unitSqScale (η : (𝓞 K)ˣ) : realSpace K := fun w => (w (η : K)) ^ 2

omit [NumberField K] in
/-- For a unit `η` of `𝓞 K`, `x` in the mixed space and an infinite place `w`,
`normAtPlace w (η • x) = w η * normAtPlace w x`. -/
theorem normAtPlace_unitSMul (η : (𝓞 K)ˣ) (x : mixedSpace K) (w : InfinitePlace K) :
    normAtPlace w (η • x) = w (η : K) * normAtPlace w x := by
  rw [unitSMul_smul, map_mul, normAtPlace_apply]

omit [NumberField K] in
/-- If `x` lies in the ideal lattice of `I` and `η` is a unit of `𝓞 K`, then `η • x` also lies in
the ideal lattice of `I`. -/
theorem unitSMul_mem_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (η : (𝓞 K)ˣ)
    {x : mixedSpace K} (hx : x ∈ mixedEmbedding.idealLattice K I) :
    η • x ∈ mixedEmbedding.idealLattice K I := by
  obtain ⟨a, ha, rfl⟩ := (mem_idealLattice K I).mp hx
  refine (mem_idealLattice K I).mpr ⟨(η : 𝓞 K) • a, Submodule.smul_mem _ _ ha, ?_⟩
  rw [unitSMul_smul, Algebra.smul_def, map_mul]

/-- The bijection of the ideal lattice of `I` with itself given by multiplication by the unit `η`,
with inverse multiplication by `η⁻¹`. -/
def gapsw80_t5_unitSMulLatticeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (η : (𝓞 K)ˣ) :
    mixedEmbedding.idealLattice K I ≃ mixedEmbedding.idealLattice K I where
  toFun x := ⟨η • (x : mixedSpace K), unitSMul_mem_idealLattice K I η x.2⟩
  invFun x := ⟨η⁻¹ • (x : mixedSpace K), unitSMul_mem_idealLattice K I η⁻¹ x.2⟩
  left_inv x := by
    simp only [inv_smul_smul]
  right_inv x := by
    simp only [smul_inv_smul]

/-- For a unit `η` of `𝓞 K`, `gapsw80_t4_multiIdealTheta K I` takes the same value at
`gapsw80_t5_unitSqScale K η * y` as at `y`. -/
theorem gapsw80_t5_multiIdealTheta_unitSq_smul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (η : (𝓞 K)ˣ) (y : InfinitePlace K → ℝ) :
    gapsw80_t4_multiIdealTheta K I (gapsw80_t5_unitSqScale K η * y)
      = gapsw80_t4_multiIdealTheta K I y := by
  rw [gapsw80_t4_multiIdealTheta_eq_latticeSum, gapsw80_t4_multiIdealTheta_eq_latticeSum]
  conv_rhs => rw [← (gapsw80_t5_unitSMulLatticeEquiv K I η).tsum_eq]
  refine tsum_congr fun x => ?_
  have hsum : ∑ w : InfinitePlace K,
        (gapsw80_t5_unitSqScale K η * y) w * normAtPlace w (x : mixedSpace K) ^ 2
      = ∑ w : InfinitePlace K,
        y w * normAtPlace w ((gapsw80_t5_unitSMulLatticeEquiv K I η x : mixedSpace K)) ^ 2 := by
    refine Finset.sum_congr rfl fun w _ => ?_
    show gapsw80_t5_unitSqScale K η w * y w * normAtPlace w (x : mixedSpace K) ^ 2
      = y w * normAtPlace w (η • (x : mixedSpace K)) ^ 2
    rw [normAtPlace_unitSMul, mul_pow, gapsw80_t5_unitSqScale]
    ring
  rw [hsum]

/-- For `c : realSpace K`, the function on infinite places sending `w` to `(expMapBasis c w)^2`. -/
def gapsw80_t5_yParam (c : realSpace K) : realSpace K := fun w => (expMapBasis c w) ^ 2

/-- For every `c : realSpace K` and infinite place `w`, `gapsw80_t5_yParam K c w` is positive. -/
theorem yParam_pos (c : realSpace K) (w : InfinitePlace K) :
    0 < gapsw80_t5_yParam K c w := pow_pos (expMapBasis_pos c w) 2

/-- For `c : realSpace K`, $\prod_w (\text{yParam}(c)(w))^{\text{mult}(w)} = e^{2\,n_K\,c(w_0)}$,
where `n_K` is the degree of `K`. -/
theorem gapsw80_t5_prod_yParam_mult (c : realSpace K) :
    ∏ w : InfinitePlace K, (gapsw80_t5_yParam K c w) ^ mult w
      = Real.exp (c w₀) ^ (2 * nK K) := by
  unfold gapsw80_t5_yParam
  simp_rw [← pow_mul, mul_comm 2, pow_mul]
  rw [Finset.prod_pow, prod_expMapBasis_pow, ← pow_mul, mul_comm]

/-- For `c : realSpace K` and an infinite place `w`, `expMapBasis (-c) w = (expMapBasis c w)⁻¹`. -/
theorem expMapBasis_neg (c : realSpace K) (w : InfinitePlace K) :
    expMapBasis (-c) w = (expMapBasis c w)⁻¹ := by
  rw [expMapBasis_apply, expMapBasis_apply, _root_.map_neg, expMap_apply, expMap_apply,
    Pi.neg_apply, mul_neg, Real.exp_neg]

/-- For `c : realSpace K` and an infinite place `w`,
`gapsw80_t5_yParam K (-c) w = (gapsw80_t5_yParam K c w)⁻¹`. -/
theorem gapsw80_t5_yParam_neg (c : realSpace K) (w : InfinitePlace K) :
    gapsw80_t5_yParam K (-c) w = (gapsw80_t5_yParam K c w)⁻¹ := by
  unfold gapsw80_t5_yParam
  rw [expMapBasis_neg, inv_pow]

/-- For an infinite place `i ≠ w₀` and `c : realSpace K`, `expMapBasis (c + Pi.single i 1) w`
equals `expMapBasis c w` times the absolute value at `w` of the corresponding fundamental unit. -/
theorem expMapBasis_add_single {i : InfinitePlace K} (hi : i ≠ w₀) (c : realSpace K)
    (w : InfinitePlace K) :
    expMapBasis (c + Pi.single i 1) w
      = expMapBasis c w * w (fundSystem K (equivFinRank.symm ⟨i, hi⟩) : K) := by

  rw [expMapBasis_apply, expMapBasis_apply, map_add, expMap_add, Pi.mul_apply,
    show ((completeBasis K).equivFun.symm) (Pi.single i 1) = completeBasis K i by
      simp [Basis.equivFun_symm_apply, Pi.single_apply],
    completeBasis_apply_of_ne K ⟨i, hi⟩,
    show expMap (expMap.symm
        (normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm ⟨i, hi⟩))))) w
      = normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) w from
      congrFun (expMap.right_inv (by simp [expMap_target, pos_at_place])) w,
    normAtAllPlaces_apply, normAtPlace_apply]

/-- For an infinite place `i ≠ w₀` and `c : realSpace K`, `gapsw80_t5_yParam K (c + Pi.single i 1)`
equals `gapsw80_t5_unitSqScale` of the corresponding fundamental unit times
`gapsw80_t5_yParam K c`. -/
theorem gapsw80_t5_yParam_add_single {i : InfinitePlace K} (hi : i ≠ w₀) (c : realSpace K) :
    gapsw80_t5_yParam K (c + Pi.single i 1)
      = gapsw80_t5_unitSqScale K (fundSystem K (equivFinRank.symm ⟨i, hi⟩))
          * gapsw80_t5_yParam K c := by
  ext w
  unfold gapsw80_t5_yParam gapsw80_t5_unitSqScale
  rw [expMapBasis_add_single K hi, mul_pow, Pi.mul_apply, mul_comm]

/-- For `r : ℝ` and `u : logSpace K`, the element of `realSpace K` taking the value `r` at `w₀` and
`u ⟨w, h⟩` at each other place `w`. -/
def gapsw80_t5_mkParam (r : ℝ) (u : logSpace K) : realSpace K :=
  fun w => if h : w = w₀ then r else u ⟨w, h⟩

/-- For `r : ℝ` and `u : logSpace K`, `gapsw80_t5_mkParam K r u w₀ = r`. -/
@[scoped simp] theorem mkParam_w₀ (r : ℝ) (u : logSpace K) : gapsw80_t5_mkParam K r u w₀ = r := by
  unfold gapsw80_t5_mkParam; rw [dite_eq_left rfl]

/-- For `w ≠ w₀`, the `w`-coordinate of `gapsw80_t5_mkParam K r u` is `u ⟨w, hw⟩`. -/
@[scoped simp] theorem mkParam_ne {w : InfinitePlace K} (hw : w ≠ w₀) (r : ℝ) (u : logSpace K) :
    gapsw80_t5_mkParam K r u w = u ⟨w, hw⟩ := by
  unfold gapsw80_t5_mkParam; rw [dite_eq_right hw]

/-- `gapsw80_t5_mkParam K` is odd. -/
theorem mkParam_neg (r : ℝ) (u : logSpace K) :
    gapsw80_t5_mkParam K (-r) (-u) = -(gapsw80_t5_mkParam K r u) := by
  ext w
  by_cases hw : w = w₀
  · simp [hw, mkParam_w₀]
  · simp [mkParam_ne K hw]

/-- The product over infinite places `w` of
`gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u) w ^ mult w` equals `Real.exp r ^ (2 * nK K)`. -/
theorem gapsw80_t5_prod_yParam_mkParam (r : ℝ) (u : logSpace K) :
    ∏ w : InfinitePlace K, (gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u) w) ^ mult w
      = Real.exp r ^ (2 * nK K) := by
  rw [gapsw80_t5_prod_yParam_mult, mkParam_w₀]

/-- For `0 < t`, `Real.exp (Real.log t / 2) ^ (2 * nK K) = t ^ nK K`. -/
theorem exp_half_log_pow_two_n {t : ℝ} (ht : 0 < t) :
    Real.exp (Real.log t / 2) ^ (2 * nK K) = t ^ (nK K) := by
  rw [pow_mul, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero,
    Real.exp_log ht]

/-- The Hecke kernel `gapsw80_t5_heckeKernel K I t` of an ideal `I` at `t` is the integral over
`u ∈ [0,1)^{r}`, indexed by the infinite places other than `w₀`, of
`gapsw80_t4_multiIdealTheta K I` evaluated at
`gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)`. -/
def gapsw80_t5_heckeKernel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
    gapsw80_t4_multiIdealTheta K I
      (gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) ∂volume

/-- For `0 < t`, `gapsw80_t5_heckeKernel K I t` equals `(t ^ nK K * covol(I)^2) ^ (-1/2)` times the
integral over `u ∈ [0,1)^r` of the lattice sum `∑_{v ∈ ℤ^n} exp(-π vᵀ G⁻¹ v)`. Here `G` is
`gapsw80_t4_scaledGram K I` at `gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)`, and
`covol(I)` is the covolume of `mixedEmbedding.idealLattice K I`. -/
theorem gapsw80_t5_heckeKernel_transformation_raw (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t5_heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
          (∑' v : Fin (nK K) → ℤ,
            cexp ((-(π *
              (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I
                  (gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)))⁻¹
                *ᵥ zcastR v)) : ℝ) : ℂ)) ∂volume := by
  unfold gapsw80_t5_heckeKernel
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  rw [gapsw80_t4_multiIdealTheta_transformation K I (fun w => yParam_pos K _ w),
    gapsw80_t5_prod_yParam_mkParam, exp_half_log_pow_two_n K ht]

/-- For `c : realSpace K`, the inverse of `gapsw80_t4_scaledGram K I (gapsw80_t5_yParam K c)` is
$C^{-1} D C^{-T}$, where `C = coordMatrix K I` and
`D = gapsw80_t4_Dscale K (gapsw80_t5_yParam K (-c))`. -/
theorem gapsw80_t5_scaledGram_yParam_inv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) :
    (gapsw80_t4_scaledGram K I (gapsw80_t5_yParam K c))⁻¹
      = (coordMatrix K I)⁻¹ * gapsw80_t4_Dscale K (gapsw80_t5_yParam K (-c))
          * ((coordMatrix K I)ᵀ)⁻¹ := by
  rw [gapsw80_t4_scaledGram_inv_eq K I (fun w => yParam_pos K c w),
    show (fun w => (gapsw80_t5_yParam K c w)⁻¹) = gapsw80_t5_yParam K (-c) from
      funext fun w => (gapsw80_t5_yParam_neg K c w).symm]

/-- For `0 < t`, `gapsw80_t5_heckeKernel K I t` equals $(t^{n} \operatorname{covol}(I)^2)^{-1/2}$
times the integral over `u ∈ [0,1)^r` of
$\sum_{v \in \mathbb Z^n} \exp(-\pi v^T C^{-1} D_u C^{-T} v)$, where `C = coordMatrix K I` and
`D_u` is `gapsw80_t4_Dscale K` at
`gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t⁻¹ / 2) (-u))`. -/
theorem gapsw80_t5_heckeKernel_transformation_raw' (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t5_heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
          (∑' v : Fin (nK K) → ℤ,
            cexp ((-(π *
              (zcastR v ⬝ᵥ ((coordMatrix K I)⁻¹
                  * gapsw80_t4_Dscale K
                      (gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t⁻¹ / 2) (-u)))
                  * ((coordMatrix K I)ᵀ)⁻¹)
                *ᵥ zcastR v)) : ℝ) : ℂ)) ∂volume := by
  rw [gapsw80_t5_heckeKernel_transformation_raw K I ht]
  congr 1
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  congr 1
  ext v
  rw [gapsw80_t5_scaledGram_yParam_inv,
    show gapsw80_t5_mkParam K (Real.log t⁻¹ / 2) (-u)
        = -(gapsw80_t5_mkParam K (Real.log t / 2) u) by
      rw [Real.log_inv, neg_div, ← mkParam_neg]]

end FLT.Gapsw80T5HeckeThetaKernel

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel"

section

noncomputable section

namespace FLT

namespace Gapsw80T6TraceDualBridge

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"

open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T4MultiVarIdealThetaTransformation FLT.Gapsw80T5HeckeThetaKernel

p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

/-- The sign-weight function on the index set `index K`: it is `1` at real-place indices, `2` at
the first component of each complex place and `-2` at the second. -/
def gapsw80_t6_multSign : index K → ℝ :=
  Sum.elim (fun _ => 1) (fun p => if p.2 = 0 then 2 else -2)

omit [NumberField K] in
/-- `gapsw80_t6_multSign K` takes the value `1` at the index of a real place. -/
@[scoped simp] theorem multSign_inl (w : {w : InfinitePlace K // IsReal w}) :
    gapsw80_t6_multSign K (Sum.inl w) = 1 := rfl

omit [NumberField K] in
/-- `gapsw80_t6_multSign K` takes the value `2` at the first component `(w, 0)` of a complex place
`w`. -/
@[scoped simp] theorem multSign_inr_fst (w : {w : InfinitePlace K // IsComplex w}) :
    gapsw80_t6_multSign K (Sum.inr (w, 0)) = 2 := rfl

omit [NumberField K] in
/-- `gapsw80_t6_multSign K` takes the value `-2` at the second component `(w, 1)` of a complex
place `w`. -/
@[scoped simp] theorem multSign_inr_snd (w : {w : InfinitePlace K // IsComplex w}) :
    gapsw80_t6_multSign K (Sum.inr (w, 1)) = -2 := rfl

omit [NumberField K] in
/-- For every index `c`, `(gapsw80_t6_multSign K c) ^ 2` equals the square of the multiplicity of
the place `gapsw80_t4_placeOf K c`. -/
theorem multSign_sq (c : index K) :
    (gapsw80_t6_multSign K c) ^ 2 = ((mult (gapsw80_t4_placeOf K c)) ^ 2 : ℝ) := by
  rcases c with ⟨w, hw⟩ | ⟨⟨w, hw⟩, j⟩
  · simp [mult, hw]
  · rw [placeOf_inr, mult, ite_eq_right (not_isReal_iff_isComplex.mpr hw)]
    fin_cases j <;> simp [gapsw80_t6_multSign]

/-- The diagonal real `nK K × nK K` matrix `gapsw80_t6_Phi K`, whose `i`-th diagonal entry is
`gapsw80_t6_multSign K ((eIdx K).symm i)`. -/
def gapsw80_t6_Phi : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.diagonal fun i => gapsw80_t6_multSign K ((eIdx K).symm i)

/-- For `y : InfinitePlace K → ℝ`, $\Phi^T D_y \Phi = D_{y'}$, where `Φ = gapsw80_t6_Phi K`,
`D_y = gapsw80_t4_Dscale K y` and `y' w = (mult w : ℝ) ^ 2 * y w`. -/
theorem gapsw80_t6_Phi_Dscale_Phi (y : InfinitePlace K → ℝ) :
    (gapsw80_t6_Phi K)ᵀ * gapsw80_t4_Dscale K y * gapsw80_t6_Phi K
      = gapsw80_t4_Dscale K (fun w => (mult w : ℝ)^2 * y w) := by
  rw [gapsw80_t6_Phi, Matrix.diagonal_transpose, gapsw80_t4_Dscale, gapsw80_t4_Dscale,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  refine Matrix.diagonal_eq_diagonal_iff.mpr fun i => ?_
  rw [show gapsw80_t6_multSign K ((eIdx K).symm i) * y (gapsw80_t4_placeOf K ((eIdx K).symm i))
        * gapsw80_t6_multSign K ((eIdx K).symm i)
      = gapsw80_t6_multSign K ((eIdx K).symm i) ^ 2
        * y (gapsw80_t4_placeOf K ((eIdx K).symm i)) from by ring,
    multSign_sq]

omit [NumberField K] in
/-- For every index `c`, `|gapsw80_t6_multSign K c|` equals the multiplicity of the place
`gapsw80_t4_placeOf K c`, as a real number. -/
theorem abs_multSign (c : index K) :
    |gapsw80_t6_multSign K c| = (mult (gapsw80_t4_placeOf K c) : ℝ) := by
  rcases c with ⟨w, hw⟩ | ⟨⟨w, hw⟩, j⟩
  · simp [mult, hw]
  · have hmult : mult (w : InfinitePlace K) = 2 := by
      rw [mult]; exact ite_eq_right (not_isReal_iff_isComplex.mpr hw)
    fin_cases j <;> simp [gapsw80_t6_multSign, placeOf_inr, hmult]

/-- The absolute value of the determinant of `gapsw80_t6_Phi K` is `4 ^ nrComplexPlaces K`. -/
theorem gapsw80_t6_abs_det_Phi :
    |(gapsw80_t6_Phi K).det| = (4 : ℝ) ^ nrComplexPlaces K := by
  rw [gapsw80_t6_Phi, Matrix.det_diagonal, Finset.abs_prod]
  calc ∏ i, |gapsw80_t6_multSign K ((eIdx K).symm i)|
      = ∏ c : index K, (mult (gapsw80_t4_placeOf K c) : ℝ) := by
        rw [Fintype.prod_equiv (eIdx K).symm _ (fun c => |gapsw80_t6_multSign K c|)
          (fun i => rfl)]
        exact Finset.prod_congr rfl fun c _ => abs_multSign K c
    _ = ∏ w : InfinitePlace K, (mult w : ℝ) ^ mult w := by
        rw [← Finset.prod_fiberwise Finset.univ (gapsw80_t4_placeOf K)
            (fun c => (mult (gapsw80_t4_placeOf K c) : ℝ))]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [Finset.prod_eq_pow_card fun c hc => by
              rw [Finset.mem_filter] at hc; rw [hc.2]]
        congr 1
        rcases isReal_or_isComplex w with hw | hw
        · rw [mult, ite_eq_left hw, fiber_placeOf_isReal K hw, Finset.card_singleton]
        · rw [mult, ite_eq_right (not_isReal_iff_isComplex.mpr hw), fiber_placeOf_isComplex K hw,
            Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    _ = (4 : ℝ) ^ nrComplexPlaces K := by
        rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K => IsReal w)]
        simp only [mult_isReal, Nat.cast_one, pow_one, Finset.prod_const_one, one_mul]
        have hmn : ∀ w : {w : InfinitePlace K // ¬IsReal w},
            mult (w : InfinitePlace K) = 2 :=
          fun w => by rw [mult, ite_eq_right w.2]
        simp only [hmn, Nat.cast_ofNat]
        rw [show ((2 : ℝ) ^ 2 : ℝ) = 4 from by norm_num, Finset.prod_const,
          Finset.card_univ]
        congr 1
        exact Fintype.card_congr
          (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex)

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The `i`-th element of `K` of the `ℤ`-basis of the fractional ideal `I` given by
`basisOfFractionalIdeal`, reindexed through `(eI K I).symm`. -/
def gapsw80_t6_idealBasisK (i : Fin (nK K)) : K :=
  basisOfFractionalIdeal K I ((eI K I).symm i)

/-- The mixed embedding of `gapsw80_t6_idealBasisK K I i` equals the `i`-th element
`idealZBasis K I i` of the `ℤ`-basis of the ideal lattice, viewed in `mixedSpace K`. -/
theorem mixedEmbedding_idealBasisK (i : Fin (nK K)) :
    mixedEmbedding K (gapsw80_t6_idealBasisK K I i)
      = (idealZBasis K I i : mixedSpace K) := by
  rw [gapsw80_t6_idealBasisK, idealZBasis_apply, fractionalIdealLatticeBasis_apply]

/-- Each `gapsw80_t6_idealBasisK K I i` lies in the fractional ideal `I`. -/
theorem idealBasisK_mem (i : Fin (nK K)) :
    gapsw80_t6_idealBasisK K I i ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  have h : gapsw80_t6_idealBasisK K I i ∈ ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
    rw [← mem_span_basisOfFractionalIdeal]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact h

/-- For `a b : K` and an index `c`, the real number `gapsw80_t6_biTerm K a b c` is the `c`-th
standard-basis coordinate of the mixed embedding of `a`, times `gapsw80_t6_multSign K c`, times the
`c`-th coordinate of the mixed embedding of `b`. -/
def gapsw80_t6_biTerm (a b : K) (c : index K) : ℝ :=
  (mixedEmbedding.stdBasis K).repr (mixedEmbedding K a) c
    * gapsw80_t6_multSign K c
    * (mixedEmbedding.stdBasis K).repr (mixedEmbedding K b) c

/-- At the index of a real place `w`, `gapsw80_t6_biTerm K a b` equals the real embedding of
`a * b` at `w`. -/
theorem biTerm_isReal (a b : K) (w : {w : InfinitePlace K // IsReal w}) :
    gapsw80_t6_biTerm K a b (Sum.inl w)
      = embedding_of_isReal w.2 (a * b) := by
  unfold gapsw80_t6_biTerm
  rw [multSign_inl, mul_one, stdBasis_apply_isReal, stdBasis_apply_isReal,
    mixedEmbedding_apply_isReal, mixedEmbedding_apply_isReal, ← map_mul]

/-- For a complex place `w`, the sum of `gapsw80_t6_biTerm K a b` at the indices `(w, 0)` and
`(w, 1)` equals `2 * (w.1.embedding (a * b)).re`. -/
theorem biTerm_isComplex_sum (a b : K) (w : {w : InfinitePlace K // IsComplex w}) :
    gapsw80_t6_biTerm K a b (Sum.inr (w, 0)) + gapsw80_t6_biTerm K a b (Sum.inr (w, 1))
      = 2 * (w.1.embedding (a * b)).re := by
  unfold gapsw80_t6_biTerm
  simp only [multSign_inr_fst, multSign_inr_snd, stdBasis_apply_isComplex_fst,
    stdBasis_apply_isComplex_snd, mixedEmbedding_apply_isComplex, map_mul, Complex.mul_re]
  ring

/-- For `a b : K`, the sum over all indices `c` of `gapsw80_t6_biTerm K a b c`, cast to `ℂ`, equals
the sum of `φ (a * b)` over all ring homomorphisms `φ : K →+* ℂ`. -/
theorem sum_biTerm_eq_sum_embeddings (a b : K) :
    ((∑ c : index K, gapsw80_t6_biTerm K a b c : ℝ) : ℂ)
      = ∑ φ : K →+* ℂ, φ (a * b) := by

  have hRHS : (∑ φ : K →+* ℂ, φ (a * b))
      = ∑ c : index K, (indexEquiv K c) (a * b) :=
    ((indexEquiv K).sum_comp (fun φ => φ (a * b))).symm
  rw [hRHS, Fintype.sum_sum_type, Fintype.sum_sum_type, Complex.ofReal_add,
    Complex.ofReal_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun w _ => ?_) ?_
  · rw [biTerm_isReal, indexEquiv_apply_isReal, ← embedding_of_isReal_apply w.2]
  · rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Complex.ofReal_add, ← Complex.ofReal_add,
      biTerm_isComplex_sum, indexEquiv_apply_isComplex_fst, indexEquiv_apply_isComplex_snd,
      ComplexEmbedding.conjugate_coe_eq, Complex.add_conj, Complex.ofReal_mul,
      Complex.ofReal_ofNat]

/-- For `a b : K`, the sum over `i : Fin (nK K)` of the `i`-th coordinate of the mixed embedding of
`a`, times `gapsw80_t6_multSign K ((eIdx K).symm i)`, times the `i`-th coordinate of that of `b`,
equals the trace `Algebra.trace ℚ K (a * b)`, cast to `ℝ`. -/
theorem gapsw80_t6_stdBasis_Phi_bilinear_eq_trace (a b : K) :
    ∑ i : Fin (nK K),
      (stdBasisFin K).repr (mixedEmbedding K a) i
        * gapsw80_t6_multSign K ((eIdx K).symm i)
        * (stdBasisFin K).repr (mixedEmbedding K b) i
      = ((Algebra.trace ℚ K (a * b) : ℚ) : ℝ) := by

  have hLHS : ∑ i : Fin (nK K),
        (stdBasisFin K).repr (mixedEmbedding K a) i
          * gapsw80_t6_multSign K ((eIdx K).symm i)
          * (stdBasisFin K).repr (mixedEmbedding K b) i
      = ∑ c : index K, gapsw80_t6_biTerm K a b c := by
    rw [Fintype.sum_equiv (eIdx K).symm _ (gapsw80_t6_biTerm K a b) fun i => ?_]
    unfold gapsw80_t6_biTerm
    simp only [stdBasisFin, Basis.repr_reindex_apply]
  rw [hLHS]
  have hRHS : ((Algebra.trace ℚ K (a * b) : ℚ) : ℂ)
      = ∑ φ : K →+* ℂ, φ (a * b) := by
    rw [show ((Algebra.trace ℚ K (a * b) : ℚ) : ℂ)
          = algebraMap ℚ ℂ (Algebra.trace ℚ K (a * b)) from rfl,
      trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ),
      ← (RingHom.equivRatAlgHom (R := K) (S := ℂ)).sum_comp (fun σ => σ (a * b))]
    rfl
  have h := sum_biTerm_eq_sum_embeddings K a b
  rw [← hRHS] at h
  exact_mod_cast h

/-- The trace-dual of the fractional ideal `I`, namely `FractionalIdeal.dual ℤ ℚ I`, as a unit of
the group of fractional ideals. -/
def gapsw80_t6_traceDualIdeal : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

/-- The underlying fractional ideal of `gapsw80_t6_traceDualIdeal K I` is
`FractionalIdeal.dual ℤ ℚ I`. -/
@[scoped simp] theorem coe_traceDualIdeal :
    (gapsw80_t6_traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

/-- The real matrix
`(coordMatrix K I)ᵀ * gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)`. -/
def gapsw80_t6_bridgeMatrix : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  (coordMatrix K I)ᵀ * gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)

/-- The `(i, j)` entry of `coordMatrix K I` is the `i`-th standard-basis coordinate of the mixed
embedding of `gapsw80_t6_idealBasisK K I j`. -/
theorem coordMatrix_apply (i j : Fin (nK K)) :
    coordMatrix K I i j
      = (stdBasisFin K).repr (mixedEmbedding K (gapsw80_t6_idealBasisK K I j)) i := by
  rw [coordMatrix_eq_toMatrix, Basis.toMatrix_apply, mixedEmbedding_idealBasisK]

/-- The `(j, k)` entry of `gapsw80_t6_bridgeMatrix K I` equals the trace `Algebra.trace ℚ K` of the
product of `gapsw80_t6_idealBasisK K I j` and
`gapsw80_t6_idealBasisK K (gapsw80_t6_traceDualIdeal K I) k`, cast to `ℝ`. -/
theorem gapsw80_t6_bridgeMatrix_entry_eq_trace (j k : Fin (nK K)) :
    gapsw80_t6_bridgeMatrix K I j k
      = ((Algebra.trace ℚ K
          (gapsw80_t6_idealBasisK K I j
            * gapsw80_t6_idealBasisK K (gapsw80_t6_traceDualIdeal K I) k) : ℚ) : ℝ) := by
  rw [← gapsw80_t6_stdBasis_Phi_bilinear_eq_trace, gapsw80_t6_bridgeMatrix,
    Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.transpose_apply, coordMatrix_apply,
    show (gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)) i k
      = gapsw80_t6_multSign K ((eIdx K).symm i)
          * coordMatrix K (gapsw80_t6_traceDualIdeal K I) i k from by
      rw [gapsw80_t6_Phi, Matrix.diagonal_mul],
    coordMatrix_apply]
  ring

/-- Every entry of `gapsw80_t6_bridgeMatrix K I` is the real cast of an integer. -/
theorem gapsw80_t6_bridgeMatrix_entry_isInt (j k : Fin (nK K)) :
    ∃ m : ℤ, gapsw80_t6_bridgeMatrix K I j k = (m : ℝ) := by
  rw [gapsw80_t6_bridgeMatrix_entry_eq_trace]
  have hck : gapsw80_t6_idealBasisK K (gapsw80_t6_traceDualIdeal K I) k
      ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
    have h := idealBasisK_mem K (gapsw80_t6_traceDualIdeal K I) k
    rwa [coe_traceDualIdeal] at h
  have hint : Algebra.traceForm ℚ K
        (gapsw80_t6_idealBasisK K (gapsw80_t6_traceDualIdeal K I) k)
        (gapsw80_t6_idealBasisK K I j)
      ∈ (algebraMap ℤ ℚ).range :=
    (FractionalIdeal.mem_dual I.ne_zero).mp hck _ (idealBasisK_mem K I j)
  obtain ⟨m, hm⟩ := hint
  refine ⟨m, ?_⟩
  rw [Algebra.traceForm_apply, mul_comm] at hm
  rw [← hm]
  simp only [eq_intCast, Rat.cast_intCast]

/-- The integer matrix whose `(j, k)` entry is an integer `m` with
`gapsw80_t6_bridgeMatrix K I j k = (m : ℝ)`, chosen using `gapsw80_t6_bridgeMatrix_entry_isInt`. -/
def gapsw80_t6_bridgeMatZ : Matrix (Fin (nK K)) (Fin (nK K)) ℤ :=
  fun j k => (gapsw80_t6_bridgeMatrix_entry_isInt K I j k).choose

/-- Casting the entries of `gapsw80_t6_bridgeMatZ K I` to `ℝ` gives `gapsw80_t6_bridgeMatrix K I`.
-/
theorem bridgeMatZ_cast_eq :
    (gapsw80_t6_bridgeMatZ K I).map (Int.cast : ℤ → ℝ) = gapsw80_t6_bridgeMatrix K I := by
  ext j k
  exact (gapsw80_t6_bridgeMatrix_entry_isInt K I j k).choose_spec.symm

/-- The absolute norm of the trace-dual ideal of `I` equals the inverse of the product of the
absolute norm of `I` and `|discr K|`. -/
theorem absNorm_traceDualIdeal :
    FractionalIdeal.absNorm
        (gapsw80_t6_traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K)
      = (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K)
          * ((discr K).natAbs : ℚ))⁻¹ := by
  have hd1 : FractionalIdeal.absNorm
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))
        = ((discr K).natAbs : ℚ)⁻¹ := by
    have hcoe : (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))⁻¹
        = (↑(differentIdeal ℤ (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
      (coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)).symm
    rw [← inv_inv (FractionalIdeal.absNorm _), ← map_inv₀, hcoe,
      FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal (K := K)]
  rw [coe_traceDualIdeal, FractionalIdeal.dual_eq_mul_inv, map_mul, map_inv₀, hd1,
    mul_comm, ← mul_inv]

/-- The determinant of `gapsw80_t6_bridgeMatrix K I` has absolute value `1`. -/
theorem gapsw80_t6_abs_det_bridgeMatrix :
    |(gapsw80_t6_bridgeMatrix K I).det| = 1 := by
  have hdet : |(gapsw80_t6_bridgeMatrix K I).det|
      = ZLattice.covolume (mixedEmbedding.idealLattice K I)
          * (4 : ℝ) ^ nrComplexPlaces K
          * ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t6_traceDualIdeal K I)) := by
    rw [gapsw80_t6_bridgeMatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      abs_mul, abs_mul, abs_det_coordMatrix, abs_det_coordMatrix, gapsw80_t6_abs_det_Phi]
  rw [hdet, mixedEmbedding.covolume_idealLattice, mixedEmbedding.covolume_idealLattice,
    absNorm_traceDualIdeal]
  have hD : (0 : ℝ) < |(discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hNI : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ≠ 0 := by
    have hne := (FractionalIdeal.absNorm_eq_zero_iff (K := K)).not.mpr I.ne_zero
    exact_mod_cast hne
  have hsqD : (Real.sqrt |(discr K : ℝ)|) ^ 2 = |(discr K : ℝ)| :=
    Real.sq_sqrt (abs_nonneg _)
  have hnatAbs : ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h4 : (4 : ℝ) ^ nrComplexPlaces K * ((2 : ℝ)⁻¹ ^ nrComplexPlaces K) ^ 2 = 1 := by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_mul,
      mul_comm 2 (nrComplexPlaces K), ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]

  push_cast
  rw [hnatAbs, mul_inv]
  have hgoal : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
        * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|
        * (4 : ℝ) ^ nrComplexPlaces K
        * ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)⁻¹
            * |(discr K : ℝ)|⁻¹ * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|)
      = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
            * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)⁻¹)
          * ((Real.sqrt |(discr K : ℝ)|) ^ 2 * |(discr K : ℝ)|⁻¹)
          * ((4 : ℝ) ^ nrComplexPlaces K * ((2 : ℝ)⁻¹ ^ nrComplexPlaces K) ^ 2) := by
    ring
  rw [hgoal, mul_inv_cancel₀ hNI, hsqD, mul_inv_cancel₀ hD.ne', h4, one_mul, one_mul]

/-- The determinant of `gapsw80_t6_bridgeMatZ K I`, cast to `ℝ`, equals the determinant of
`gapsw80_t6_bridgeMatrix K I`. -/
theorem cast_det_bridgeMatZ :
    ((gapsw80_t6_bridgeMatZ K I).det : ℝ) = (gapsw80_t6_bridgeMatrix K I).det := by
  have h : ((gapsw80_t6_bridgeMatZ K I).map (Int.cast : ℤ → ℝ)).det
      = (gapsw80_t6_bridgeMatrix K I).det := by rw [bridgeMatZ_cast_eq]
  rw [← h]
  exact RingHom.map_det (Int.castRingHom ℝ) (gapsw80_t6_bridgeMatZ K I)

/-- The integer matrix `gapsw80_t6_bridgeMatZ K I` is a unit in the matrix ring over `ℤ`. -/
theorem bridgeMatZ_isUnit : IsUnit (gapsw80_t6_bridgeMatZ K I) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h1 : |((gapsw80_t6_bridgeMatZ K I).det : ℝ)| = 1 := by
    rw [cast_det_bridgeMatZ, gapsw80_t6_abs_det_bridgeMatrix]
  have hn : (gapsw80_t6_bridgeMatZ K I).det.natAbs = 1 := by
    have h2 : ((gapsw80_t6_bridgeMatZ K I).det.natAbs : ℝ) = 1 := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact h1
    exact_mod_cast h2
  exact Int.isUnit_iff_natAbs_eq.mpr hn

/-- The matrix `gapsw80_t6_bridgeMatZ K I` as an element of the unit group of
`Matrix (Fin (nK K)) (Fin (nK K)) ℤ`. -/
def gapsw80_t6_bridgeMatZUnit : (Matrix (Fin (nK K)) (Fin (nK K)) ℤ)ˣ :=
  (bridgeMatZ_isUnit K I).unit

/-- The underlying matrix of the unit `gapsw80_t6_bridgeMatZUnit K I` is
`gapsw80_t6_bridgeMatZ K I`. -/
@[scoped simp] theorem coe_bridgeMatZUnit :
    ((gapsw80_t6_bridgeMatZUnit K I : Matrix (Fin (nK K)) (Fin (nK K)) ℤ))
      = gapsw80_t6_bridgeMatZ K I := rfl

/-- The bijection of `Fin (nK K) → ℤ` given by multiplying a vector on the left by the inverse of
the unit `gapsw80_t6_bridgeMatZUnit K I`. -/
def gapsw80_t6_bridgeEquiv : (Fin (nK K) → ℤ) ≃ (Fin (nK K) → ℤ) where
  toFun v := ((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val *ᵥ v
  invFun v := (gapsw80_t6_bridgeMatZUnit K I).val *ᵥ v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

/-- For `v : Fin (nK K) → ℤ`, `zcastR (gapsw80_t6_bridgeEquiv K I v)` equals the real-cast inverse
of `gapsw80_t6_bridgeMatZUnit K I` applied to `zcastR v`. -/
theorem zcastR_bridgeEquiv_apply (v : Fin (nK K) → ℤ) :
    zcastR (gapsw80_t6_bridgeEquiv K I v)
      = (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
          *ᵥ zcastR v := by
  ext i
  change ((((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val *ᵥ v) i : ℝ) = _
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, zcastR]
  push_cast
  rfl

/-- The product of `gapsw80_t6_bridgeMatrix K I` and the real-cast inverse of
`gapsw80_t6_bridgeMatZUnit K I` is the identity matrix. -/
theorem bridgeMatrix_mul_cast_inv :
    gapsw80_t6_bridgeMatrix K I
        * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
      = 1 := by
  have h : (gapsw80_t6_bridgeMatZ K I) * ((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val
      = 1 := by
    conv_lhs => rw [← coe_bridgeMatZUnit, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmap : ((gapsw80_t6_bridgeMatZ K I) * ((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val).map
        (Int.cast : ℤ → ℝ)
      = gapsw80_t6_bridgeMatrix K I
          * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ)) := by
    have := map_mul (Int.castRingHom ℝ).mapMatrix (gapsw80_t6_bridgeMatZ K I)
      ((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val
    simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at this
    rw [this, bridgeMatZ_cast_eq]
  rw [← hmap, h]
  ext i j
  simp [Matrix.map_apply, Matrix.one_apply, apply_ite (Int.cast : ℤ → ℝ)]

/-- `gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)` times the real-cast inverse
of `gapsw80_t6_bridgeMatZUnit K I` equals `((coordMatrix K I)ᵀ)⁻¹`. -/
theorem Phi_mul_coordMatrix_mul_cast_inv :
    gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)
        * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
      = ((coordMatrix K I)ᵀ)⁻¹ := by
  have hunit : IsUnit ((coordMatrix K I)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (det_coordMatrix_ne_zero K I)
  calc gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)
        * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
      = (((coordMatrix K I)ᵀ)⁻¹ * (coordMatrix K I)ᵀ)
          * (gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)
              * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))) := by
        rw [Matrix.nonsing_inv_mul _ hunit, one_mul]
    _ = ((coordMatrix K I)ᵀ)⁻¹
          * (gapsw80_t6_bridgeMatrix K I
              * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))) := by
        rw [gapsw80_t6_bridgeMatrix, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_assoc]
    _ = ((coordMatrix K I)ᵀ)⁻¹ := by
        rw [bridgeMatrix_mul_cast_inv, mul_one]

/-- For `y' : InfinitePlace K → ℝ` and `v : Fin (nK K) → ℤ`, the quadratic form of
`(coordMatrix K I)⁻¹ * gapsw80_t4_Dscale K y' * ((coordMatrix K I)ᵀ)⁻¹` at `zcastR v` equals the
quadratic form of
`gapsw80_t4_scaledGram K (gapsw80_t6_traceDualIdeal K I) (fun w => (mult w : ℝ)^2 * y' w)` at
`zcastR (gapsw80_t6_bridgeEquiv K I v)`. -/
theorem gapsw80_t6_dualQuadForm_eq (y' : InfinitePlace K → ℝ) (v : Fin (nK K) → ℤ) :
    zcastR v ⬝ᵥ ((coordMatrix K I)⁻¹
        * gapsw80_t4_Dscale K y' * ((coordMatrix K I)ᵀ)⁻¹) *ᵥ zcastR v
      = zcastR (gapsw80_t6_bridgeEquiv K I v) ⬝ᵥ
          gapsw80_t4_scaledGram K (gapsw80_t6_traceDualIdeal K I)
            (fun w => (mult w : ℝ)^2 * y' w)
          *ᵥ zcastR (gapsw80_t6_bridgeEquiv K I v) := by

  have hMv : ((coordMatrix K I)ᵀ)⁻¹ *ᵥ zcastR v
      = (gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I))
          *ᵥ zcastR (gapsw80_t6_bridgeEquiv K I v) := by
    rw [zcastR_bridgeEquiv_apply, Matrix.mulVec_mulVec, Phi_mul_coordMatrix_mul_cast_inv]

  have hLHS : zcastR v ⬝ᵥ ((coordMatrix K I)⁻¹ * gapsw80_t4_Dscale K y'
        * ((coordMatrix K I)ᵀ)⁻¹) *ᵥ zcastR v
      = (((coordMatrix K I)ᵀ)⁻¹ *ᵥ zcastR v) ⬝ᵥ
          (gapsw80_t4_Dscale K y') *ᵥ (((coordMatrix K I)ᵀ)⁻¹ *ᵥ zcastR v) := by
    rw [show (coordMatrix K I)⁻¹ = (((coordMatrix K I)ᵀ)⁻¹)ᵀ from by
          rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose],
      Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (zcastR v) (((coordMatrix K I)ᵀ)⁻¹)ᵀ, Matrix.vecMul_transpose]

  have hRHS : zcastR (gapsw80_t6_bridgeEquiv K I v) ⬝ᵥ
        (gapsw80_t4_scaledGram K (gapsw80_t6_traceDualIdeal K I)
          (fun w => (mult w : ℝ)^2 * y' w))
        *ᵥ zcastR (gapsw80_t6_bridgeEquiv K I v)
      = ((gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I))
            *ᵥ zcastR (gapsw80_t6_bridgeEquiv K I v))
          ⬝ᵥ (gapsw80_t4_Dscale K y')
          *ᵥ ((gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I))
            *ᵥ zcastR (gapsw80_t6_bridgeEquiv K I v)) := by
    have hG : gapsw80_t4_scaledGram K (gapsw80_t6_traceDualIdeal K I)
          (fun w => (mult w : ℝ)^2 * y' w)
        = (gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I))ᵀ
            * gapsw80_t4_Dscale K y'
            * (gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)) := by
      rw [gapsw80_t4_scaledGram, ← gapsw80_t6_Phi_Dscale_Phi, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [hG, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec _
        ((gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I))ᵀ),
      Matrix.vecMul_transpose]
  rw [hLHS, hRHS, hMv]

/-- For `y' : InfinitePlace K → ℝ`, the sum over `v ∈ ℤ^n` of `exp(-π vᵀ M v)`, with
`M = (coordMatrix K I)⁻¹ * gapsw80_t4_Dscale K y' * ((coordMatrix K I)ᵀ)⁻¹`, equals
`gapsw80_t4_multiIdealTheta K (gapsw80_t6_traceDualIdeal K I)` at `fun w => (mult w : ℝ)^2 * y' w`.
-/
theorem gapsw80_t6_dualGramSum_eq_multiIdealTheta_codiff (y' : InfinitePlace K → ℝ) :
    (∑' v : Fin (nK K) → ℤ,
      cexp ((-(π * (zcastR v ⬝ᵥ ((coordMatrix K I)⁻¹
          * gapsw80_t4_Dscale K y' * ((coordMatrix K I)ᵀ)⁻¹)
        *ᵥ zcastR v)) : ℝ) : ℂ))
      = gapsw80_t4_multiIdealTheta K (gapsw80_t6_traceDualIdeal K I)
          (fun w => (mult w : ℝ)^2 * y' w) := by
  conv_rhs => rw [gapsw80_t4_multiIdealTheta, ← (gapsw80_t6_bridgeEquiv K I).tsum_eq]
  exact tsum_congr fun v => by rw [gapsw80_t6_dualQuadForm_eq]

/-- For `0 < t`, `gapsw80_t5_heckeKernel K I t` equals $(t^{n} \operatorname{covol}(I)^2)^{-1/2}$
times the integral over `u ∈ [0,1)^r` of
`gapsw80_t4_multiIdealTheta K (gapsw80_t6_traceDualIdeal K I)` at the point
`w ↦ (mult w : ℝ) ^ 2 * y_u w`, where
`y_u = gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t⁻¹ / 2) (-u))`. -/
theorem gapsw80_t6_heckeKernel_transformation_bridged
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t5_heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
          gapsw80_t4_multiIdealTheta K (gapsw80_t6_traceDualIdeal K I)
            (fun w => (mult w : ℝ)^2 * gapsw80_t5_yParam K
              (gapsw80_t5_mkParam K (Real.log t⁻¹ / 2) (-u)) w) ∂MeasureTheory.volume := by
  rw [gapsw80_t5_heckeKernel_transformation_raw' K I ht]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  rw [← gapsw80_t6_dualGramSum_eq_multiIdealTheta_codiff]

end FLT.Gapsw80T6TraceDualBridge

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"

section

noncomputable section

namespace FLT

namespace Gapsw80T7ClosedFEWeakPair

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "NumberField.mixedEmbedding.fundamentalCone P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding.fundamentalCone"
p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"

open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T4MultiVarIdealThetaTransformation FLT.Gapsw80T5HeckeThetaKernel
open FLT.Gapsw80T6TraceDualBridge

p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Asymptotics P2MW.S_NumberField_exists_completedDedekindZeta_package.Asymptotics Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Asymptotics.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K]

/-- The vector `gapsw80_t7_multSq K : realSpace K` with `w`-coordinate `(mult w : ℝ) ^ 2`. -/
def gapsw80_t7_multSq : realSpace K := fun w => ((mult w : ℝ)) ^ 2

omit [NumberField K] in
/-- Every coordinate of `gapsw80_t7_multSq K` is strictly positive. -/
theorem multSq_pos (w : InfinitePlace K) : 0 < gapsw80_t7_multSq K w :=
  pow_pos (Nat.cast_pos.mpr mult_pos) 2

omit [NumberField K] in
/-- For a unit `η` of `𝓞 K` and `y : realSpace K`, multiplication by `gapsw80_t7_multSq K` commutes
with multiplication by `gapsw80_t5_unitSqScale K η`. -/
theorem multSq_unitSqScale_comm (η : (𝓞 K)ˣ) (y : realSpace K) :
    gapsw80_t7_multSq K * (gapsw80_t5_unitSqScale K η * y)
      = gapsw80_t5_unitSqScale K η * (gapsw80_t7_multSq K * y) := by
  ext w; simp only [Pi.mul_apply]; ring

/-- For `i ≠ w₀`, the function
`c ↦ gapsw80_t4_multiIdealTheta K J (gapsw80_t7_multSq K * gapsw80_t5_yParam K c)` is invariant
under `c ↦ c + Pi.single i 1`. -/
theorem gapsw80_t7_multiIdealTheta_multSq_yParam_periodic
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {i : InfinitePlace K} (hi : i ≠ w₀)
    (c : realSpace K) :
    gapsw80_t4_multiIdealTheta K J
        (gapsw80_t7_multSq K * gapsw80_t5_yParam K (c + Pi.single i 1))
      = gapsw80_t4_multiIdealTheta K J
          (gapsw80_t7_multSq K * gapsw80_t5_yParam K c) := by
  rw [gapsw80_t5_yParam_add_single K hi, multSq_unitSqScale_comm,
    gapsw80_t5_multiIdealTheta_unitSq_smul]

/-- `gapsw80_t5_mkParam K r (u + Pi.single i 1)` equals
`gapsw80_t5_mkParam K r u + Pi.single (i : InfinitePlace K) 1`, for `i` indexing a place other than
`w₀`. -/
theorem mkParam_add_single (r : ℝ) (u : logSpace K)
    (i : {w : InfinitePlace K // w ≠ w₀}) :
    gapsw80_t5_mkParam K r (u + Pi.single i 1)
      = gapsw80_t5_mkParam K r u + Pi.single (i : InfinitePlace K) 1 := by
  ext w
  by_cases hw : w = w₀
  · subst hw
    simp only [mkParam_w₀, Pi.add_apply, Pi.single_eq_of_ne' i.2, add_zero]
  · simp only [mkParam_ne K hw, Pi.add_apply]
    by_cases hwi : w = (i : InfinitePlace K)
    · subst hwi
      simp [Pi.single_eq_same, show (⟨(i:InfinitePlace K), hw⟩ : {w // w ≠ w₀}) = i from
        Subtype.ext rfl]
    · rw [Pi.single_eq_of_ne (fun h => hwi (Subtype.ext_iff.mp h)),
        Pi.single_eq_of_ne hwi, add_zero]

/-- The complex-valued function of `u : logSpace K` given by `gapsw80_t4_multiIdealTheta K J`
evaluated at `gapsw80_t7_multSq K * gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u)`. -/
abbrev gapsw80_t7_integrand (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ)
    (u : logSpace K) : ℂ :=
  gapsw80_t4_multiIdealTheta K J
    (gapsw80_t7_multSq K * gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u))

/-- `gapsw80_t7_integrand K J r` is invariant under translating `u` by `k • Pi.single i 1` for any
integer `k` and index `i`. -/
theorem gapsw80_t7_integrand_single_zperiodic (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (r : ℝ) (i : {w : InfinitePlace K // w ≠ w₀}) (k : ℤ) (u : logSpace K) :
    gapsw80_t7_integrand K J r (u + k • Pi.single i 1) = gapsw80_t7_integrand K J r u := by
  have hstep : ∀ v : logSpace K,
      gapsw80_t7_integrand K J r (v + Pi.single i 1) = gapsw80_t7_integrand K J r v := fun v => by
    unfold gapsw80_t7_integrand
    rw [mkParam_add_single, gapsw80_t7_multiIdealTheta_multSq_yParam_periodic K J i.2]
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [add_smul, one_smul, ← add_assoc, hstep]; exact ih
  | pred n ih =>
    have h' := (hstep (u + (-(n : ℤ) - 1) • Pi.single i 1)).symm
    rw [add_assoc, show (-(n:ℤ)-1) • Pi.single i (1:ℝ) + (Pi.single i 1 : logSpace K)
        = (-(n:ℤ)) • Pi.single i 1 from by rw [sub_smul, one_smul, sub_add_cancel]] at h'
    exact h'.trans ih

/-- `gapsw80_t7_integrand K J r` is invariant under translation by any element `g` of the `ℤ`-span
of the standard basis of `logSpace K`. -/
theorem gapsw80_t7_integrand_zlattice_invariant (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (r : ℝ) (g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (u : logSpace K) :
    gapsw80_t7_integrand K J r ((g : logSpace K) + u) = gapsw80_t7_integrand K J r u := by
  have hmem := g.2
  rw [Basis.mem_span_iff_repr_mem] at hmem
  simp only [Pi.basisFun_repr] at hmem
  choose k hk using hmem
  have hg : (g : logSpace K) = ∑ i, (k i) • Pi.single i (1:ℝ) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero, ← hk,
      eq_intCast]
    simp [zsmul_eq_mul]
  rw [hg]

  induction (Finset.univ : Finset {w : InfinitePlace K // w ≠ w₀}) using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj,
      show (k j • Pi.single j (1:ℝ) + ∑ i ∈ s, k i • Pi.single i 1) + u
          = (∑ i ∈ s, k i • Pi.single i 1 + u) + k j • Pi.single j 1 from by abel,
      gapsw80_t7_integrand_single_zperiodic]
    exact ih

/-- The unit box `[0,1)^r` in `logSpace K`, the product over the infinite places other than `w₀` of
`Set.Ico 0 1`. -/
abbrev gapsw80_t7_unitBox : Set (logSpace K) :=
  Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1

/-- The unit box `gapsw80_t7_unitBox K` equals the fundamental domain `ZSpan.fundamentalDomain` of
the standard basis `Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}`. -/
theorem unitBox_eq_fundamentalDomain :
    gapsw80_t7_unitBox K
      = ZSpan.fundamentalDomain (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}) :=
  (ZSpan.fundamentalDomain_pi_basisFun).symm

/-- The unit box `gapsw80_t7_unitBox K` is an additive fundamental domain with respect to Lebesgue
measure for the `ℤ`-span of the standard basis of `logSpace K`. -/
theorem gapsw80_t7_unitBox_isAddFundamentalDomain :
    IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      (gapsw80_t7_unitBox K) volume := by
  rw [unitBox_eq_fundamentalDomain]
  exact ZSpan.isAddFundamentalDomain _ volume

/-- Lebesgue measure on `logSpace K` is invariant under translation by the `ℤ`-span of the
standard basis. -/
local instance : VAddInvariantMeasure
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (logSpace K) volume :=
  ⟨fun _ _ _ => measure_preimage_add _ _ _⟩

/-- The `ℤ`-span of the standard basis of `logSpace K` is countable. -/
local instance : Countable
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}))) := by
  refine Countable.of_equiv ({w : InfinitePlace K // w ≠ w₀} → ℤ)
    (Equiv.ofBijective
      (fun k : {w : InfinitePlace K // w ≠ w₀} → ℤ =>
        (⟨fun i => (k i : ℝ), ?_⟩ :
          Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}))))
      ⟨?_, ?_⟩)
  · rw [Basis.mem_span_iff_repr_mem]; intro i; exact ⟨k i, by simp⟩
  · intro k₁ k₂ h
    exact funext fun i => Int.cast_injective (congr_fun (Subtype.ext_iff.mp h) i)
  · intro ⟨v, hv⟩
    rw [Basis.mem_span_iff_repr_mem] at hv
    simp only [Pi.basisFun_repr] at hv
    choose k hk using hv
    exact ⟨k, Subtype.ext (funext fun i => by simp [← hk i, eq_intCast])⟩

/-- The image of the unit box under negation is an additive fundamental domain with respect to
Lebesgue measure for the `ℤ`-span of the standard basis of `logSpace K`. -/
theorem gapsw80_t7_neg_unitBox_isAddFundamentalDomain :
    IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      ((Neg.neg : logSpace K → logSpace K) '' gapsw80_t7_unitBox K) volume := by
  refine (gapsw80_t7_unitBox_isAddFundamentalDomain K).image_of_equiv
    (Equiv.neg (logSpace K))
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving
    (Equiv.neg _) ?_
  intro g x
  show -((-g : logSpace K) + x) = (g : logSpace K) + -x
  simp only [neg_add, neg_neg]

/-- The integral over the unit box of `gapsw80_t7_integrand K J r (-u)` equals the integral over
the unit box of `gapsw80_t7_integrand K J r u`. -/
theorem gapsw80_t7_setIntegral_neg_box_eq (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    ∫ u in gapsw80_t7_unitBox K, gapsw80_t7_integrand K J r (-u) ∂volume
      = ∫ u in gapsw80_t7_unitBox K, gapsw80_t7_integrand K J r u ∂volume := by

  calc ∫ u in gapsw80_t7_unitBox K, gapsw80_t7_integrand K J r (-u) ∂volume
      = ∫ v in (Neg.neg : logSpace K → logSpace K) '' gapsw80_t7_unitBox K,
          gapsw80_t7_integrand K J r v ∂volume :=
        ((Measure.measurePreserving_neg (volume : Measure (logSpace K))).setIntegral_image_emb
          (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.neg (logSpace K)))
          (gapsw80_t7_integrand K J r) (gapsw80_t7_unitBox K)).symm
    _ = ∫ u in gapsw80_t7_unitBox K, gapsw80_t7_integrand K J r u ∂volume :=
        (gapsw80_t7_neg_unitBox_isAddFundamentalDomain K).setIntegral_eq
          (gapsw80_t7_unitBox_isAddFundamentalDomain K)
          (fun g u => gapsw80_t7_integrand_zlattice_invariant K J r g u)

/-- The kernel `gapsw80_t7_multHeckeKernel K J t` is the integral over the unit box of
`gapsw80_t7_integrand K J (Real.log t / 2) u`. -/
def gapsw80_t7_multHeckeKernel (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  ∫ u in gapsw80_t7_unitBox K, gapsw80_t7_integrand K J (Real.log t / 2) u ∂volume

/-- For `0 < t`, `gapsw80_t5_heckeKernel K I t` equals `(t ^ nK K * covol(I)^2) ^ (-1/2)` times
`gapsw80_t7_multHeckeKernel K (gapsw80_t6_traceDualIdeal K I) t⁻¹`. -/
theorem gapsw80_t7_heckeKernel_closed_FE (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t5_heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ)
        * gapsw80_t7_multHeckeKernel K (gapsw80_t6_traceDualIdeal K I) t⁻¹ := by
  rw [gapsw80_t6_heckeKernel_transformation_bridged K I ht, gapsw80_t7_multHeckeKernel]
  congr 1

  rw [← gapsw80_t7_setIntegral_neg_box_eq K (gapsw80_t6_traceDualIdeal K I) (Real.log t⁻¹ / 2)]
  rfl

/-- The covolume of `mixedEmbedding.idealLattice K I` is strictly positive. -/
theorem gapsw80_t7_covol_pos (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < ZLattice.covolume (mixedEmbedding.idealLattice K I) :=
  ZLattice.covolume_pos _ volume

/-- For `0 < x`, `0 < c` and `n : ℕ`, `(x⁻¹ ^ n * c ^ 2) ^ (-1/2 : ℝ) = x ^ (n / 2 : ℝ) * c⁻¹`. -/
theorem rpow_factor_h_feq {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (n : ℕ) :
    (x⁻¹ ^ n * c ^ 2) ^ (-(1/2) : ℝ) = x ^ ((n : ℝ)/2) * c⁻¹ := by
  have h1 : (x⁻¹ ^ n : ℝ) ^ (-(1/2) : ℝ) = x ^ ((n : ℝ)/2) := by
    rw [← Real.rpow_natCast x⁻¹, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le,
      ← Real.rpow_mul hx.le]
    ring_nf
  have h2 : (c ^ 2 : ℝ) ^ (-(1/2) : ℝ) = c⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hc.le]
    norm_num
    exact Real.rpow_neg_one c
  rw [Real.mul_rpow (by positivity) (by positivity), h1, h2]

/-- For all `x > 0`, `gapsw80_t5_heckeKernel K I (1 / x)` equals `covol(I)⁻¹ * x ^ (nK K / 2)`
times `gapsw80_t7_multHeckeKernel K (gapsw80_t6_traceDualIdeal K I) x`, where `covol(I)` is the
covolume of `mixedEmbedding.idealLattice K I`. -/
theorem gapsw80_t7_h_feq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      gapsw80_t5_heckeKernel K I (1 / x)
        = (((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℂ))⁻¹
            * ((x ^ ((nK K : ℝ)/2) : ℝ) : ℂ))
          • gapsw80_t7_multHeckeKernel K (gapsw80_t6_traceDualIdeal K I) x := by
  intro x hx
  have hx' : (0:ℝ) < x := hx
  have h1x : (0:ℝ) < 1/x := by positivity
  rw [gapsw80_t7_heckeKernel_closed_FE K I h1x, one_div, inv_inv, smul_eq_mul]
  congr 1
  rw [rpow_factor_h_feq hx' (gapsw80_t7_covol_pos K I)]
  push_cast
  ring

/-- For `u : logSpace K`, the vector in `realSpace K` whose `w`-coordinate is the square of the
product over `i` of `w (fundSystem K (equivFinRank.symm i)) ^ (u i)`. -/
def gapsw80_t7_unitPart (u : logSpace K) : realSpace K := fun w =>
  (∏ i : {w : InfinitePlace K // w ≠ w₀},
    (w (fundSystem K (equivFinRank.symm i) : K)) ^ (u i)) ^ 2

/-- Every coordinate of `gapsw80_t7_unitPart K u` is strictly positive. -/
theorem unitPart_pos (u : logSpace K) (w : InfinitePlace K) :
    0 < gapsw80_t7_unitPart K u w := by
  refine pow_pos (Finset.prod_pos fun i _ => ?_) 2
  exact Real.rpow_pos_of_pos (pos_iff.mpr (by simp)) _

/-- For `0 < t`, the value of `gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)` at
`w` is `t * gapsw80_t7_unitPart K u w`. -/
theorem gapsw80_t7_yParam_mkParam_factor {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (w : InfinitePlace K) :
    gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u) w
      = t * gapsw80_t7_unitPart K u w := by
  unfold gapsw80_t5_yParam gapsw80_t7_unitPart
  rw [expMapBasis_apply']
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, mkParam_w₀,
    ← Real.exp_nat_mul, show (2:ℕ) * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht]
  congr 2
  exact Finset.prod_congr rfl fun i _ => by rw [mkParam_ne K i.2]

/-- For each infinite place `w`, the map `u ↦ gapsw80_t7_unitPart K u w` is continuous on
`logSpace K`. -/
theorem continuous_unitPart (w : InfinitePlace K) :
    Continuous fun u : logSpace K => gapsw80_t7_unitPart K u w := by
  unfold gapsw80_t7_unitPart
  refine (continuous_finsetProd _ fun i _ => ?_).pow 2
  exact (Real.continuous_const_rpow
    (pos_iff.mpr (by simp [fundSystem])).ne').comp (continuous_apply i)

/-- There is `c > 0` such that `c ≤ gapsw80_t7_unitPart K u w` for all `u ∈ [0,1]^r` and all
infinite places `w`. -/
theorem gapsw80_t7_unitPart_lower_bound :
    ∃ c > 0, ∀ u ∈ (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1),
      ∀ w, c ≤ gapsw80_t7_unitPart K u w := by
  have hcpct : IsCompact (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hne : (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1).Nonempty :=
    ⟨0, fun i _ => by simp⟩

  have hw : ∀ w : InfinitePlace K, ∃ c > 0,
      ∀ u ∈ (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1),
        c ≤ gapsw80_t7_unitPart K u w := fun w => by
    obtain ⟨u₀, hu₀, hmin⟩ := hcpct.exists_isMinOn hne (continuous_unitPart K w).continuousOn
    exact ⟨gapsw80_t7_unitPart K u₀ w, unitPart_pos K u₀ w, fun u hu => hmin hu⟩
  choose c hcpos hc using hw
  refine ⟨Finset.univ.inf' ⟨w₀, Finset.mem_univ _⟩ c, ?_, fun u hu w => ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr fun w _ => hcpos w
  · exact (Finset.inf'_le c (Finset.mem_univ w)).trans (hc w u hu)

/-- The set `{w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1}` is compact. -/
theorem isCompact_sum_sq_eq_one :
    IsCompact {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} := by
  have hclosed : IsClosed {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hbdd : {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} ⊆ Metric.closedBall 0 1 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)).trans_eq hw
  exact (Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hclosed, Metric.isBounded_closedBall.subset hbdd⟩)

/-- There is `lam > 0` such that `lam * ∑ i, (v i)^2 ≤ vᵀ G v` for all `v : Fin (nK K) → ℤ`, where
`G = gapsw80_t3_idealGram K I`. -/
theorem gapsw80_t7_idealGram_lower_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ lam > 0, ∀ v : Fin (nK K) → ℤ,
      lam * ∑ i, (v i : ℝ)^2 ≤ zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v := by
  set F : (Fin (nK K) → ℝ) → ℝ := fun w => w ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ w with hF
  have hFcont : Continuous F := by unfold F; fun_prop
  have hFscale : ∀ (c : ℝ) (w : Fin (nK K) → ℝ), F (c • w) = c^2 * F w := fun c w => by
    simp only [hF, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, sq, mul_assoc]
  have hSne : {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1}.Nonempty := by
    refine ⟨Pi.single (⟨0, Module.finrank_pos⟩ : Fin (nK K)) 1, ?_⟩
    simp only [Set.mem_ofPred_eq, Pi.single_apply, ite_pow, one_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  obtain ⟨ww, hww, hmin⟩ := (isCompact_sum_sq_eq_one K).exists_isMinOn hSne hFcont.continuousOn
  have hne : ww ≠ 0 := by
    rintro rfl
    simp at hww
  have hlam : 0 < F ww := by
    simpa [hF] using (gapsw80_t3_idealGram_posDef K I).dotProduct_mulVec_pos hne
  refine ⟨F ww, hlam, fun v => ?_⟩
  by_cases hv : zcastR v = 0
  · have hsum0 : ∑ i, (v i : ℝ)^2 = 0 := Finset.sum_eq_zero fun i _ => by
      simp [show (v i : ℝ) = 0 from congr_fun hv i]
    simp only [hsum0, mul_zero, hv, hF, Matrix.mulVec_zero, dotProduct_zero, le_refl]
  · set s : ℝ := Real.sqrt (∑ i, (v i : ℝ)^2) with hs_def
    have hsumpos : 0 < ∑ i, (v i : ℝ)^2 := by
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ?_
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      exact ⟨i, Finset.mem_univ i, by
        simp only [zcastR, Pi.zero_apply] at hi; positivity⟩
    have hspos : 0 < s := Real.sqrt_pos.mpr hsumpos
    have hs_sq : s^2 = ∑ i, (v i : ℝ)^2 := Real.sq_sqrt hsumpos.le
    have hmem : s⁻¹ • zcastR v ∈ {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} := by
      simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
        ← hs_sq, inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero 2 hspos.ne')
    calc F ww * ∑ i, (v i : ℝ)^2
        = s^2 * F ww := by rw [hs_sq, mul_comm]
      _ ≤ s^2 * F (s⁻¹ • zcastR v) :=
          mul_le_mul_of_nonneg_left (hmin hmem) (sq_nonneg s)
      _ = F (s • (s⁻¹ • zcastR v)) := (hFscale s _).symm
      _ = zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v := by
          rw [smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]

/-- The summand `exp(-π vᵀ G v)` at `v = 0`, with `G = gapsw80_t4_scaledGram K I y`, equals `1`. -/
theorem multiIdealTheta_zero_term (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : InfinitePlace K → ℝ) :
    cexp ((-(π * (zcastR (0 : Fin (nK K) → ℤ) ⬝ᵥ (gapsw80_t4_scaledGram K I y)
      *ᵥ zcastR 0)) : ℝ) : ℂ) = 1 := by
  simp [zcastR, dotProduct]

/-- If `c ≤ y w` for all `w`, then for all `v : Fin (nK K) → ℤ`, `c` times the quadratic form of
`gapsw80_t3_idealGram K I` at `zcastR v` is at most the quadratic form of
`gapsw80_t4_scaledGram K I y` at `zcastR v`. -/
theorem scaledGram_lower_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : ℝ}
    {y : InfinitePlace K → ℝ} (hy : ∀ w, c ≤ y w) (v : Fin (nK K) → ℤ) :
    c * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)
      ≤ zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v := by
  have hGram1 : gapsw80_t3_idealGram K I = gapsw80_t4_scaledGram K I (fun _ => (1:ℝ)) := by
    rw [gapsw80_t4_scaledGram_const_eq, one_smul]
  rw [hGram1, gapsw80_t4_quadForm_scaledGram, gapsw80_t4_quadForm_scaledGram, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => by
    rw [one_mul]
    exact mul_le_mul_of_nonneg_right (hy w) (sq_nonneg _)

/-- If `v : Fin (nK K) → ℤ` is nonzero, then `1 ≤ ∑ i, (v i : ℝ)^2`. -/
theorem one_le_sum_sq_of_ne_zero {v : Fin (nK K) → ℤ} (hv : v ≠ 0) :
    (1 : ℝ) ≤ ∑ i, (v i : ℝ)^2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have h1 : (1:ℝ) ≤ (v i : ℝ)^2 :=
    (one_le_sq_iff_one_le_abs _).mpr (by exact_mod_cast Int.one_le_abs (by simpa using hi))
  exact h1.trans
    (Finset.single_le_sum (f := fun j => (v j : ℝ)^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- For `0 < lam`, the function `v ↦ rexp (-(π * lam * ∑ i, (v i : ℝ)^2))` is summable over
`v : Fin (nK K) → ℤ`. -/
theorem gapsw80_t7_summable_dom_gaussian {lam : ℝ} (hlam : 0 < lam) :
    Summable fun v : Fin (nK K) → ℤ => rexp (-(π * lam * ∑ i, (v i : ℝ)^2)) :=
  (gapsw80_t2_summable_gaussian_Zn (n := nK K) (c := π * lam) (by positivity)).congr
    fun v => by ring_nf

/-- There exist `C` and `p > 0` such that for every `c ≥ 1` and every `y : InfinitePlace K → ℝ`
with `c ≤ y w` for all `w`, `‖gapsw80_t4_multiIdealTheta K I y - 1‖ ≤ C * Real.exp (-(p * c))`. -/
theorem gapsw80_t7_theta_sub_one_exp_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ C p, 0 < p ∧ ∀ {c : ℝ}, 1 ≤ c →
      ∀ {y : InfinitePlace K → ℝ}, (∀ w, c ≤ y w) →
        ‖gapsw80_t4_multiIdealTheta K I y - 1‖ ≤ C * Real.exp (-(p * c)) := by
  obtain ⟨lam, hlam, hGram⟩ := gapsw80_t7_idealGram_lower_bound K I
  set p := π * lam with hp_def
  have hp : 0 < p := by positivity
  have hsum : Summable fun v : Fin (nK K) → ℤ => rexp (-(p * ∑ i, (v i:ℝ)^2)) :=
    gapsw80_t7_summable_dom_gaussian K hlam
  set C := rexp p * ∑' v : Fin (nK K) → ℤ, rexp (-(p * ∑ i, (v i:ℝ)^2)) with hC_def
  refine ⟨C, p, hp, fun {c} hc {y} hy => ?_⟩

  let f : (Fin (nK K) → ℤ) → ℂ := fun v =>
    cexp ((-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ)
  have hzero : f 0 = 1 := multiIdealTheta_zero_term K I y

  have hterm : ∀ v, ‖f v‖ ≤ rexp (-(p * c * ∑ i, (v i:ℝ)^2)) := fun v => by
    show ‖cexp _‖ ≤ _
    rw [Complex.norm_exp, Complex.ofReal_re]
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    calc p * c * ∑ i, (v i:ℝ)^2
        = π * (c * (lam * ∑ i, (v i:ℝ)^2)) := by ring
      _ ≤ π * (c * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hGram v) (by linarith)) Real.pi_nonneg
      _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v) :=
          mul_le_mul_of_nonneg_left (scaledGram_lower_bound K I hy v) Real.pi_nonneg

  have hdom : ∀ v : Fin (nK K) → ℤ,
      rexp (-(p * c * ∑ i, (v i:ℝ)^2)) ≤ rexp (-(p * ∑ i, (v i:ℝ)^2)) := fun v => by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have hs : (0:ℝ) ≤ ∑ i, (v i : ℝ)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hc)) hs]
  have hsplit : ∀ {v : Fin (nK K) → ℤ}, v ≠ 0 →
      rexp (-(p * c * ∑ i, (v i:ℝ)^2)) ≤ rexp (-(p*(c-1))) * rexp (-(p * ∑ i, (v i:ℝ)^2)) := by
    intro v hv
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 := one_le_sum_sq_of_ne_zero K hv
    nlinarith [mul_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hc)) (sub_nonneg.mpr h1)]

  have hfullnorm : Summable fun v => ‖f v‖ :=
    hsum.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => (hterm v).trans (hdom v))
  have hfullsum : Summable f := hfullnorm.of_norm
  have htail_summable : Summable fun v : Fin (nK K) → ℤ =>
      if v = 0 then (0:ℝ) else rexp (-(p * c * ∑ i, (v i:ℝ)^2)) := by
    refine hsum.of_nonneg_of_le (fun v => ?_) (fun v => ?_)
    · split_ifs <;> positivity
    · split_ifs with h
      · positivity
      · exact hdom v
  have hite_norm_summable : Summable fun v : Fin (nK K) → ℤ =>
      ‖if v = (0 : Fin (nK K) → ℤ) then (0:ℂ) else f v‖ := by
    refine hfullnorm.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_)
    split_ifs <;> simp

  have hTheta : gapsw80_t4_multiIdealTheta K I y - 1
      = ∑' v, if v = 0 then 0 else f v := by
    have heq : gapsw80_t4_multiIdealTheta K I y = ∑' v, f v := rfl
    rw [heq, hfullsum.tsum_eq_add_tsum_ite 0, hzero, add_sub_cancel_left]
  rw [hTheta]
  calc ‖∑' v, if v = 0 then 0 else f v‖
      ≤ ∑' v, ‖if v = (0 : Fin (nK K) → ℤ) then (0:ℂ) else f v‖ :=
        norm_tsum_le_tsum_norm hite_norm_summable
    _ ≤ ∑' v, if v = (0 : Fin (nK K) → ℤ) then (0:ℝ) else rexp (-(p*c*∑ i, (v i:ℝ)^2)) := by
        refine hite_norm_summable.tsum_le_tsum (fun v => ?_) htail_summable
        split_ifs with h
        · simp
        · exact hterm v
    _ ≤ ∑' v : Fin (nK K) → ℤ, rexp (-(p*(c-1))) * rexp (-(p * ∑ i, (v i:ℝ)^2)) := by
        refine htail_summable.tsum_le_tsum (fun v => ?_) (hsum.mul_left _)
        split_ifs with h
        · positivity
        · exact hsplit h
    _ = C * rexp (-(p * c)) := by
        rw [tsum_mul_left, hC_def,
          show -(p*(c-1)) = p + (-(p*c)) from by ring, Real.exp_add]
        ring

/-- For each `v : Fin (nK K) → ℤ`, the map sending `y : InfinitePlace K → ℝ` to the theta term
`cexp (-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)))` is continuous. -/
theorem continuous_theta_term (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (v : Fin (nK K) → ℤ) :
    Continuous fun y : InfinitePlace K → ℝ =>
      cexp ((-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ) := by
  refine Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (Continuous.neg ?_))
  refine continuous_const.mul ?_
  simp only [gapsw80_t4_quadForm_scaledGram]
  exact continuous_finsetSum _ fun w _ => (continuous_apply w).mul continuous_const

/-- If `0 < c`, then `gapsw80_t4_multiIdealTheta K I` is continuous on the set of `y` with
`c ≤ y w` for all places `w`. -/
theorem gapsw80_t7_continuousOn_multiIdealTheta_ge (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {c : ℝ} (hc : 0 < c) :
    ContinuousOn (gapsw80_t4_multiIdealTheta K I) {y | ∀ w, c ≤ y w} := by
  obtain ⟨lam, hlam, hGram⟩ := gapsw80_t7_idealGram_lower_bound K I
  refine continuousOn_tsum (fun v => (continuous_theta_term K I v).continuousOn)
    (gapsw80_t7_summable_dom_gaussian K (mul_pos hc hlam)) (fun v y hy => ?_)
  rw [Complex.norm_exp, Complex.ofReal_re]
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  calc π * (c * lam) * ∑ i, (v i:ℝ)^2
      = π * (c * (lam * ∑ i, (v i:ℝ)^2)) := by ring
    _ ≤ π * (c * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGram v) hc.le) Real.pi_nonneg
    _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v) :=
        mul_le_mul_of_nonneg_left (scaledGram_lower_bound K I hy v) Real.pi_nonneg

/-- `gapsw80_t4_multiIdealTheta K I` is continuous on the set of `y` with `0 < y w` for all places
`w`. -/
theorem gapsw80_t7_continuousOn_multiIdealTheta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (gapsw80_t4_multiIdealTheta K I) {y | ∀ w, 0 < y w} := by
  intro y hy
  set c := Finset.univ.inf' ⟨w₀, Finset.mem_univ _⟩ (fun w => y w / 2) with hc_def
  have hc : 0 < c := (Finset.lt_inf'_iff _).mpr fun w _ => half_pos (hy w)
  have hy' : y ∈ {z | ∀ w, c ≤ z w} := fun w =>
    (Finset.inf'_le _ (Finset.mem_univ w)).trans (half_le_self (hy w).le)
  have hopen : IsOpen {z : InfinitePlace K → ℝ | ∀ w, c < z w} := by
    have : {z : InfinitePlace K → ℝ | ∀ w, c < z w} = ⋂ w, {z | c < z w} := by
      ext z; simp [Set.mem_iInter]
    rw [this]; exact isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have hy'' : y ∈ {z | ∀ w, c < z w} := fun w =>
    (Finset.inf'_le _ (Finset.mem_univ w)).trans_lt (by linarith [half_lt_self (hy w)])

  refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_
    (mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hy''))
  exact ((gapsw80_t7_continuousOn_multiIdealTheta_ge K I hc) y hy').mono
    (fun z hz w => (hz w).le)

/-- For each `r : ℝ`, the map `u ↦ gapsw80_t5_mkParam K r u` from `logSpace K` to `realSpace K` is
continuous. -/
theorem continuous_mkParam (r : ℝ) :
    Continuous fun u : logSpace K => gapsw80_t5_mkParam K r u := by
  refine continuous_pi fun w => ?_
  unfold gapsw80_t5_mkParam
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

/-- For `scale` with `0 < scale w` at every place `w` and any `r : ℝ`, the map sending
`u : logSpace K` to `gapsw80_t4_multiIdealTheta K I` at
`scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u)` is continuous. -/
theorem continuous_genericKernel_integrand (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ)
    (scale : realSpace K) (hscale : ∀ w, 0 < scale w) :
    Continuous fun u : logSpace K =>
      gapsw80_t4_multiIdealTheta K I
        (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u)) := by
  have hyP : Continuous fun u : logSpace K =>
      scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u) := by
    refine continuous_pi fun w => ?_
    exact continuous_const.mul
      (((continuous_apply w).comp ((continuous_expMapBasis K).comp (continuous_mkParam K r))).pow 2)
  refine ContinuousOn.comp_continuous (gapsw80_t7_continuousOn_multiIdealTheta K I) hyP ?_
  exact fun u w => mul_pos (hscale w) (yParam_pos K _ w)

/-- The unit box `gapsw80_t7_unitBox K` in `logSpace K` has volume `1`. -/
theorem volume_unitBox_eq_one : volume (gapsw80_t7_unitBox K) = 1 := by
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

/-- The unit box `gapsw80_t7_unitBox K` has finite volume. -/
theorem volume_unitBox_lt_top : volume (gapsw80_t7_unitBox K) < ⊤ := by
  rw [volume_unitBox_eq_one]; exact ENNReal.one_lt_top

/-- If `1 ≤ scale w` at every place `w`, then the integral over `u ∈ gapsw80_t7_unitBox K` of
`gapsw80_t4_multiIdealTheta K I` at
`scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)` is continuous in `t` on
`Set.Ioi 0`. -/
theorem gapsw80_t7_continuousOn_genericKernel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (scale : realSpace K) (hscale : ∀ w, 1 ≤ scale w) :
    ContinuousOn (fun t : ℝ => ∫ u in gapsw80_t7_unitBox K,
      gapsw80_t4_multiIdealTheta K I
        (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) ∂volume)
      (Set.Ioi 0) := by
  have hscale' : ∀ w, 0 < scale w := fun w => lt_of_lt_of_le one_pos (hscale w)
  obtain ⟨cK, hcK, hLB⟩ := gapsw80_t7_unitPart_lower_bound K
  obtain ⟨C, p, hp, hbound⟩ := gapsw80_t7_theta_sub_one_exp_bound K I
  have hfin : IsFiniteMeasure (volume.restrict (gapsw80_t7_unitBox K)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using volume_unitBox_lt_top K⟩

  intro t₀ ht₀
  have ht₀' : (0:ℝ) < t₀ := ht₀
  set s := Set.Icc (t₀/2) (t₀+1) with hs_def
  have hsnhds : s ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hssub : s ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le (by linarith) ht.1
  set c₀ : ℝ := cK * (t₀/2)
  have hc₀ : 0 < c₀ := mul_pos hcK (by linarith)
  obtain ⟨lam, hlam, hGram⟩ := gapsw80_t7_idealGram_lower_bound K I
  set M : ℝ := ∑' v : Fin (nK K) → ℤ, rexp (-(π * (c₀ * lam) * ∑ i, (v i:ℝ)^2)) with hM_def
  have hMsum := gapsw80_t7_summable_dom_gaussian K (mul_pos hc₀ hlam)

  have hy_lb : ∀ t ∈ s, ∀ u ∈ gapsw80_t7_unitBox K, ∀ w,
      c₀ ≤ (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) w := by
    intro t ht u hu w
    have ht' : (0:ℝ) < t := hssub ht
    rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht']
    have huP : 0 < gapsw80_t7_unitPart K u w := unitPart_pos K u w
    calc c₀ = cK * (t₀/2) := rfl
      _ ≤ gapsw80_t7_unitPart K u w * t :=
          mul_le_mul (hLB u (fun i hi => Ico_subset_Icc_self (hu i hi)) w) ht.1 (by linarith) huP.le
      _ = 1 * (t * gapsw80_t7_unitPart K u w) := by ring
      _ ≤ scale w * (t * gapsw80_t7_unitPart K u w) :=
          mul_le_mul_of_nonneg_right (hscale w) (by positivity)

  have hTheta_bound : ∀ t ∈ s, ∀ u ∈ gapsw80_t7_unitBox K,
      ‖gapsw80_t4_multiIdealTheta K I
        (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u))‖ ≤ M := by
    intro t ht u hu
    unfold gapsw80_t4_multiIdealTheta
    have hle : ∀ v : Fin (nK K) → ℤ,
        ‖cexp ((-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I
          (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)))
            *ᵥ zcastR v)) : ℝ) : ℂ)‖ ≤ rexp (-(π * (c₀ * lam) * ∑ i, (v i:ℝ)^2)) := fun v => by
      rw [Complex.norm_exp, Complex.ofReal_re]
      exact Real.exp_le_exp.mpr (neg_le_neg (by
        calc π * (c₀ * lam) * ∑ i, (v i:ℝ)^2
            = π * (c₀ * (lam * ∑ i, (v i:ℝ)^2)) := by ring
          _ ≤ π * (c₀ * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hGram v) hc₀.le) Real.pi_nonneg
          _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I _) *ᵥ zcastR v) :=
              mul_le_mul_of_nonneg_left
                (scaledGram_lower_bound K I (hy_lb t ht u hu) v) Real.pi_nonneg))
    have hsum := hMsum.of_nonneg_of_le (fun _ => norm_nonneg _) hle
    exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hle hMsum)

  have hcontOn_s : ContinuousOn
      (fun t => ∫ u in gapsw80_t7_unitBox K,
        gapsw80_t4_multiIdealTheta K I
          (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) ∂volume) s := by
    refine continuousOn_of_dominated (bound := fun _ => M)
      (μ := volume.restrict (gapsw80_t7_unitBox K)) ?_ ?_ ?_ ?_
    · intro t _
      exact (continuous_genericKernel_integrand K I _ scale hscale').aestronglyMeasurable.restrict
    · intro t ht
      exact ae_restrict_of_forall_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
        (fun u hu => hTheta_bound t ht u hu)
    · exact integrable_const M
    · refine ae_of_all _ fun u => ?_

      have hmk : ContinuousOn (fun t : ℝ => gapsw80_t5_mkParam K (Real.log t / 2) u) s := by
        refine continuousOn_pi.mpr fun w' => ?_
        unfold gapsw80_t5_mkParam
        split_ifs
        · exact (Real.continuousOn_log.mono (hssub.trans fun x hx => ne_of_gt hx)).div_const 2
        · exact continuousOn_const
      have hyP : ContinuousOn
          (fun t : ℝ => scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) s := by
        refine ContinuousOn.mul continuousOn_const ?_
        refine continuousOn_pi.mpr fun w => ?_
        unfold gapsw80_t5_yParam
        exact (((continuous_apply w).comp (continuous_expMapBasis K)).continuousOn.comp hmk
          (Set.mapsTo_univ _ _)).pow 2
      exact (gapsw80_t7_continuousOn_multiIdealTheta K I).comp hyP
        (fun t ht w => mul_pos (hscale' w) (yParam_pos K _ w))
  exact (hcontOn_s t₀ ⟨by linarith, by linarith⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds hsnhds)

/-- The Hecke kernel `gapsw80_t5_heckeKernel K I` is continuous on `Set.Ioi 0`. -/
theorem gapsw80_t7_continuousOn_heckeKernel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (gapsw80_t5_heckeKernel K I) (Set.Ioi 0) := by
  have h := gapsw80_t7_continuousOn_genericKernel K I 1 (fun _ => le_refl 1)
  simp only [one_mul] at h
  exact h

/-- The kernel `gapsw80_t7_multHeckeKernel K J` is continuous on `Set.Ioi 0`. -/
theorem gapsw80_t7_continuousOn_multHeckeKernel (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (gapsw80_t7_multHeckeKernel K J) (Set.Ioi 0) :=
  gapsw80_t7_continuousOn_genericKernel K J (gapsw80_t7_multSq K)
    (fun _ => one_le_pow₀ (Nat.one_le_cast.mpr mult_pos))

/-- If `1 ≤ scale w` at every place `w`, there is `p > 0` such that the integral over the unit box
of `gapsw80_t4_multiIdealTheta K I` at
`scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)`, minus `1`, is
`O(Real.exp (-p * t))` as `t → ∞`. -/
theorem gapsw80_t7_genericKernel_sub_one_isBigO_exp (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (scale : realSpace K) (hscale : ∀ w, 1 ≤ scale w) :
    ∃ p > 0, (fun t => (∫ u in gapsw80_t7_unitBox K,
        gapsw80_t4_multiIdealTheta K I
          (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) ∂volume) - 1)
      =O[atTop] fun t => Real.exp (-p * t) := by
  obtain ⟨cK, hcK, hLB⟩ := gapsw80_t7_unitPart_lower_bound K
  obtain ⟨C, p, hp, hbound⟩ := gapsw80_t7_theta_sub_one_exp_bound K I
  have hscale' : ∀ w, 0 < scale w := fun w => lt_of_lt_of_le one_pos (hscale w)
  refine ⟨p * cK, by positivity, IsBigO.of_bound (max C 0) ?_⟩
  filter_upwards [eventually_ge_atTop cK⁻¹] with t ht
  have ht0 : 0 < t := lt_of_lt_of_le (inv_pos.mpr hcK) ht
  have hcKt : 1 ≤ cK * t := by
    rw [mul_comm]
    exact (inv_le_iff_one_le_mul₀ hcK).mp ht
  set G : logSpace K → ℂ := fun u => gapsw80_t4_multiIdealTheta K I
      (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) with hG_def

  have hptw : ∀ u ∈ gapsw80_t7_unitBox K, ‖G u - 1‖ ≤ C * Real.exp (-(p * (cK * t))) := by
    intro u hu
    refine hbound hcKt (fun w => ?_)
    rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht0]
    have huP : 0 < gapsw80_t7_unitPart K u w := unitPart_pos K u w
    calc cK * t ≤ gapsw80_t7_unitPart K u w * t :=
          mul_le_mul_of_nonneg_right (hLB u (fun i hi => Ico_subset_Icc_self (hu i hi)) w)
            ht0.le
      _ = 1 * (t * gapsw80_t7_unitPart K u w) := by ring
      _ ≤ scale w * (t * gapsw80_t7_unitPart K u w) :=
          mul_le_mul_of_nonneg_right (hscale w) (by positivity)

  have hGcont : Continuous G := continuous_genericKernel_integrand K I _ scale hscale'
  have hfin : IsFiniteMeasure (volume.restrict (gapsw80_t7_unitBox K)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using volume_unitBox_lt_top K⟩
  have hintconst : IntegrableOn (fun _ : logSpace K => (1:ℂ)) (gapsw80_t7_unitBox K) volume := by
    simpa only [IntegrableOn, integrable_const_iff] using Or.inr hfin
  have hint : IntegrableOn (fun u => G u - 1) (gapsw80_t7_unitBox K) volume := by
    refine ⟨(hGcont.sub continuous_const).aestronglyMeasurable.restrict, ?_⟩
    refine HasFiniteIntegral.mono' ?_
      (ae_restrict_of_forall_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
        (fun u hu => hptw u hu))
    exact (integrable_const (C * Real.exp (-(p * (cK * t))))).hasFiniteIntegral

  have heq : (∫ u in gapsw80_t7_unitBox K, G u ∂volume) - 1
      = ∫ u in gapsw80_t7_unitBox K, (G u - 1) ∂volume := by
    have hintG : IntegrableOn G (gapsw80_t7_unitBox K) volume :=
      (hint.add hintconst).congr_fun
        (fun u _ => by simp only [Pi.add_apply]; ring)
        (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    rw [integral_sub hintG hintconst, setIntegral_const]
    simp [measureReal_def, volume_unitBox_eq_one]

  rw [Real.norm_of_nonneg (Real.exp_pos _).le,
    show -(p * cK) * t = -(p * (cK * t)) from by ring]
  calc ‖(∫ u in gapsw80_t7_unitBox K, G u ∂volume) - 1‖
      = ‖∫ u in gapsw80_t7_unitBox K, (G u - 1) ∂volume‖ := by rw [heq]
    _ ≤ (C * Real.exp (-(p * (cK * t)))) * (volume (gapsw80_t7_unitBox K)).toReal :=
        norm_setIntegral_le_of_norm_le_const (volume_unitBox_lt_top K) hptw
    _ = C * Real.exp (-(p * (cK * t))) := by
        rw [volume_unitBox_eq_one, ENNReal.toReal_one, mul_one]
    _ ≤ max C 0 * Real.exp (-(p * (cK * t))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- There is `p > 0` such that `gapsw80_t5_heckeKernel K I t - 1` is `O(Real.exp (-p * t))` as
`t → ∞`. -/
theorem gapsw80_t7_heckeKernel_sub_one_isBigO_exp (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ p > 0, (fun t => gapsw80_t5_heckeKernel K I t - 1)
      =O[atTop] fun t => Real.exp (-p * t) := by
  obtain ⟨p, hp, hO⟩ := gapsw80_t7_genericKernel_sub_one_isBigO_exp K I 1 (fun _ => le_refl 1)
  refine ⟨p, hp, hO.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl⟩
  simp only [one_mul, gapsw80_t5_heckeKernel]

/-- For every real `r`, `gapsw80_t5_heckeKernel K I t - 1` is `O(t ^ r)` as `t → ∞`. -/
theorem gapsw80_t7_hf_top (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    (fun t => gapsw80_t5_heckeKernel K I t - 1) =O[atTop] fun t => t ^ r := by
  obtain ⟨p, hp, hO⟩ := gapsw80_t7_heckeKernel_sub_one_isBigO_exp K I
  exact hO.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO

/-- There is `p > 0` such that `gapsw80_t7_multHeckeKernel K J t - 1` is `O(Real.exp (-p * t))` as
`t → ∞`. -/
theorem gapsw80_t7_multHeckeKernel_sub_one_isBigO_exp (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ p > 0, (fun t => gapsw80_t7_multHeckeKernel K J t - 1)
      =O[atTop] fun t => Real.exp (-p * t) :=
  gapsw80_t7_genericKernel_sub_one_isBigO_exp K J (gapsw80_t7_multSq K)
    (fun _ => one_le_pow₀ (Nat.one_le_cast.mpr mult_pos))

/-- For every real `r`, `gapsw80_t7_multHeckeKernel K J t - 1` is `O(t ^ r)` as `t → ∞`. -/
theorem gapsw80_t7_hg_top (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    (fun t => gapsw80_t7_multHeckeKernel K J t - 1) =O[atTop] fun t => t ^ r := by
  obtain ⟨p, hp, hO⟩ := gapsw80_t7_multHeckeKernel_sub_one_isBigO_exp K J
  exact hO.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO


/-- The weak functional-equation pair over `ℂ` with `f` the Hecke kernel of `I`, `g` the
multiplicative Hecke kernel of the trace dual ideal of `I`, weight `k = nK K / 2`, root number `ε`
the inverse of the covolume of the ideal lattice of `I`, and `f₀ = g₀ = 1`. -/
def gapsw80_t7_heckeWeakFEPair (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : WeakFEPair ℂ where
  f := gapsw80_t5_heckeKernel K I
  g := gapsw80_t7_multHeckeKernel K (gapsw80_t6_traceDualIdeal K I)
  k := (nK K : ℝ) / 2
  ε := ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℂ))⁻¹
  f₀ := 1
  g₀ := 1
  hk := div_pos (by exact_mod_cast (Module.finrank_pos : 0 < finrank ℚ K)) two_pos
  hε := by
    refine inv_ne_zero (Complex.ofReal_ne_zero.mpr ?_)
    exact (gapsw80_t7_covol_pos K I).ne'
  hf_int := (gapsw80_t7_continuousOn_heckeKernel K I).locallyIntegrableOn measurableSet_Ioi
  hg_int := (gapsw80_t7_continuousOn_multHeckeKernel K _).locallyIntegrableOn measurableSet_Ioi
  h_feq := by
    intro x hx
    have h := gapsw80_t7_h_feq K I x hx
    simp only [smul_eq_mul] at h ⊢
    convert h using 2
  hf_top := gapsw80_t7_hf_top K I
  hg_top := gapsw80_t7_hg_top K _

end FLT.Gapsw80T7ClosedFEWeakPair

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"

