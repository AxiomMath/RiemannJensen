module

public import RiemannJensen.Xi
public import RiemannJensen.Theta
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.MellinTransform
public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

/-!
# The theta–xi bridge

This module records exact identities which connect the theta kernel used in
Riemann's integral formula to Mathlib's construction of the completed zeta
function.  In particular, no integral representation is postulated: the
completed zeta function is unfolded to the regularized Mellin transform from
which Mathlib constructs it, and the summands of `thetaPhi` are identified
with the differential operator occurring in the classical integration-by-
parts argument.
-/

@[expose] public section

namespace RiemannJensen

open Complex MeasureTheory

/-- The positive-frequency Gaussian seed whose image under
`d²/dt² - 1/4` is the corresponding summand of `thetaPhi`. -/
noncomputable def thetaSeedTerm (m : ℕ) (t : ℝ) : ℝ :=
  let n : ℝ := (m + 1 : ℕ)
  Real.exp (t / 2 - Real.pi * n ^ 2 * Real.exp (2 * t))

/-- Exact first derivative of a positive-frequency Gaussian theta seed. -/
theorem hasDerivAt_thetaSeedTerm (m : ℕ) (t : ℝ) :
    HasDerivAt (thetaSeedTerm m)
      (thetaSeedTerm m t *
        (1 / 2 - 2 * Real.pi * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * t))) t := by
  have h := (((hasDerivAt_id' t).div_const 2).sub
    (((hasDerivAt_id' t).const_mul 2).exp.const_mul (Real.pi * ((m + 1 : ℕ) : ℝ) ^ 2))).exp
  refine h.congr_deriv ?_
  simp only [thetaSeedTerm, Pi.sub_apply]
  ring

/-- Derivative of the explicit first derivative of a Gaussian theta seed, i.e. its second
derivative. -/
theorem hasDerivAt_thetaSeedTerm_first (m : ℕ) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        thetaSeedTerm m x *
          (1 / 2 - 2 * Real.pi * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * x)))
      (thetaSeedTerm m t *
        ((1 / 2 - 2 * Real.pi * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * t)) ^ 2 -
          4 * Real.pi * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * t))) t := by
  have h := (hasDerivAt_const t (1 / 2 : ℝ)).sub
    (((hasDerivAt_id' t).const_mul 2).exp.const_mul (2 * Real.pi * ((m + 1 : ℕ) : ℝ) ^ 2))
  refine ((hasDerivAt_thetaSeedTerm m t).mul h).congr_deriv ?_
  simp only [Pi.sub_apply]
  ring

/-- The paper's theta summand is exactly `(d²/dt² - 1/4)` applied to
its Gaussian seed.  This is the algebraic heart of the two integrations by
parts that produce the xi kernel. -/
theorem thetaTerm_eq_deriv_deriv_sub (m : ℕ) (t : ℝ) :
    thetaTerm m t = deriv (deriv (thetaSeedTerm m)) t - (1 / 4) * thetaSeedTerm m t := by
  rw [show deriv (thetaSeedTerm m) = _ from funext fun x => (hasDerivAt_thetaSeedTerm m x).deriv,
    (hasDerivAt_thetaSeedTerm_first m t).deriv]
  simp only [thetaTerm, thetaSeedTerm]
  rw [show 9 * t / 2 = t / 2 + 2 * t + 2 * t by ring, show 5 * t / 2 = t / 2 + 2 * t by ring]
  simp only [sub_eq_add_neg, Real.exp_add, neg_mul]
  ring

/-- The Gaussian seeds sum to the positive-frequency half of the Jacobi
theta kernel. -/
theorem hasSum_thetaSeedTerm (t : ℝ) :
    HasSum (fun m : ℕ => thetaSeedTerm m t)
      (Real.exp (t / 2) *
        ((HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1) / 2)) := by
  have h := HurwitzZeta.hasSum_nat_cosKernel₀ 0 (Real.exp_pos (2 * t))
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one, QuotientAddGroup.mk_zero] at h
  have h' := (h.div_const 2).mul_left (Real.exp (t / 2))
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at h'
  convert h' using 2 with m
  simp only [thetaSeedTerm]
  rw [mul_div_cancel_left₀ _ two_ne_zero, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Summability of the positive-frequency Gaussian seed series. -/
theorem summable_thetaSeedTerm (t : ℝ) : Summable (fun m : ℕ => thetaSeedTerm m t) :=
  (hasSum_thetaSeedTerm t).summable

/-- Closed form of the positive-frequency theta seed sum. -/
theorem tsum_thetaSeedTerm (t : ℝ) :
    (∑' m : ℕ, thetaSeedTerm m t) =
      Real.exp (t / 2) * ((HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1) / 2) :=
  (hasSum_thetaSeedTerm t).tsum_eq

/-- The full kernel is the sum of the images of its Gaussian seeds under `d²/dt² - 1/4`. -/
theorem thetaPhi_eq_tsum_deriv_deriv_sub (t : ℝ) :
    thetaPhi t = ∑' m : ℕ, (deriv (deriv (thetaSeedTerm m)) t - (1 / 4) * thetaSeedTerm m t) :=
  tsum_congr fun m => thetaTerm_eq_deriv_deriv_sub m t

/-- Mathlib's entire completed zeta is, definitionally, one half of the
regularized Mellin transform of the even Hurwitz kernel at zero. -/
theorem completedRiemannZeta₀_eq_regularizedMellin (s : ℂ) :
    completedRiemannZeta₀ s =
      mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (s / 2) / 2 :=
  rfl

/-- Consequently the xi normalization used in this project has an exact
regularized-Mellin expression. -/
theorem riemannXi_eq_regularizedMellin (s : ℂ) :
    riemannXi s =
      (s * (s - 1) *
          (mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (s / 2) / 2) + 1) / 2 := by
  rw [riemannXi, completedRiemannZeta₀_eq_regularizedMellin]

/-- The centered xi function in the same regularized-Mellin normalization. -/
theorem centeredXi_eq_regularizedMellin (w : ℂ) :
    centeredXi w =
      (((1 / 2 : ℂ) + w) * ((1 / 2 : ℂ) + w - 1) *
          (mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
            (((1 / 2 : ℂ) + w) / 2) / 2) + 1) / 2 := by
  rw [centeredXi, riemannXi_eq_regularizedMellin]

/-- Above one, Mathlib's regularized even theta kernel is simply the usual
kernel with its constant term removed. -/
theorem regularizedEvenKernel_of_one_lt {x : ℝ} (hx : 1 < x) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x =
      (HurwitzZeta.evenKernel 0 x - 1 : ℝ) := by
  simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
    Set.indicator_of_mem (Set.mem_Ioi.mpr hx),
    Set.indicator_of_notMem (Set.notMem_Ioo_of_ge hx.le)]

/-- Below one, the regularizing term is the exact `x⁻¹ᐟ²` contribution
forced by theta inversion. -/
theorem regularizedEvenKernel_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x =
      (HurwitzZeta.evenKernel 0 x - x ^ (-(1 / 2 : ℝ)) : ℝ) := by
  simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
    Set.indicator_of_notMem (Set.notMem_Ioi.mpr hx.2.le),
    Set.indicator_of_mem hx]

/-- The regularized kernel vanishes at the splice point.  Mathlib deliberately
uses this value to retain exact inversion symmetry. -/
@[simp]
theorem regularizedEvenKernel_one :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif 1 = 0 := by
  simp [WeakFEPair.f_modif]

/-- The integral expression appearing on the right side of Riemann's formula,
written with `w` rather than a square root. -/
noncomputable def xiThetaIntegral (w : ℂ) : ℂ :=
  2 * ∫ t : ℝ in Set.Ioi 0,
    (thetaPhi t : ℂ) * Complex.cosh ((t : ℂ) * w)

/-- The theta integral has the required even symmetry before it is identified
with xi. -/
@[simp]
theorem xiThetaIntegral_neg (w : ℂ) : xiThetaIntegral (-w) = xiThetaIntegral w := by
  simp [xiThetaIntegral]

/-- The theta moment appearing in the coefficient formula of the paper. -/
noncomputable def thetaMoment (j : ℕ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0, thetaPhi t * t ^ (2 * j)

/-- Every theta moment is nonnegative. -/
theorem thetaMoment_nonneg (j : ℕ) : 0 ≤ thetaMoment j :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht =>
    mul_nonneg (thetaPhi_pos ht.le).le (pow_nonneg ht.le _)

/-- The moment-side candidate for the coefficient `gammaCoeff`. -/
noncomputable def thetaGammaCoeff (j : ℕ) : ℝ :=
  (2 * (j.factorial : ℝ) / ((2 * j).factorial : ℝ)) * thetaMoment j

/-- Every moment-side coefficient `thetaGammaCoeff j` is nonnegative. -/
theorem thetaGammaCoeff_nonneg (j : ℕ) : 0 ≤ thetaGammaCoeff j :=
  mul_nonneg (by positivity) (thetaMoment_nonneg j)

end RiemannJensen
