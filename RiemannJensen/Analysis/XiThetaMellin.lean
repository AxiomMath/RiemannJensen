module

public import RiemannJensen.Analysis.XiTheta
public import RiemannJensen.Analysis.ThetaDecay
public import RiemannJensen.Analysis.TaylorBridge
public import RiemannJensen.Analysis.ThetaKernelWhole
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Mellin normalization for the xi theta kernel

We relate the theta kernel `thetaPhi` to the conventional whole-line xi kernel `xiWholePhi`
through the identity `thetaPhi (2 * x) = 2 * xiWholePhi x`, and deduce that the half-line cosine
integral `xiThetaIntegral` equals the centered Riemann xi function `centeredXi`.

## Main definitions

* `xiWholeTerm`: One summand of the conventional whole-line xi kernel.
* `xiWholePhi`: The conventional whole-line xi kernel.

## Main results

* `thetaPhi_two_mul`: `thetaPhi (2 * x) = 2 * xiWholePhi x`.
* `xiThetaIntegral_eq_eight_mul_whole`: `xiThetaIntegral w` is eight times the half-line integral
  of `xiWholePhi x * cosh (2 * x * w)`.
* `xiThetaIntegral_eq_centeredXi`: `xiThetaIntegral w = centeredXi w`.
-/

@[expose] public section

namespace RiemannJensen

open Complex MeasureTheory Set

/-- One summand of the conventional whole-line xi kernel. -/
noncomputable def xiWholeTerm (m : ℕ) (x : ℝ) : ℝ :=
  let n : ℝ := (m + 1 : ℕ)
  (2 * Real.pi ^ 2 * n ^ 4 * Real.exp (9 * x) -
      3 * Real.pi * n ^ 2 * Real.exp (5 * x)) *
    Real.exp (-Real.pi * n ^ 2 * Real.exp (4 * x))

/-- The conventional whole-line xi kernel. -/
noncomputable def xiWholePhi (x : ℝ) : ℝ :=
  ∑' m : ℕ, xiWholeTerm m x

/-- `xiWholeTerm m` is the summand `ThetaKernel.phiTerm (m + 1)`. -/
theorem xiWholeTerm_eq_thetaKernel (m : ℕ) (x : ℝ) :
    xiWholeTerm m x = ThetaKernel.phiTerm (m + 1) x := by
  simp only [xiWholeTerm, ThetaKernel.phiTerm]

/-- `xiWholePhi` is the whole-line theta kernel `ThetaKernel.Phi`. -/
theorem xiWholePhi_eq_thetaKernel (x : ℝ) :
    xiWholePhi x = ThetaKernel.Phi x := by
  unfold xiWholePhi ThetaKernel.Phi
  exact tsum_congr fun m ↦ xiWholeTerm_eq_thetaKernel m x

/-- The summand `thetaTerm m` at `2 * x` is twice the summand `xiWholeTerm m` at `x`. -/
theorem thetaTerm_two_mul (m : ℕ) (x : ℝ) :
    thetaTerm m (2 * x) = 2 * xiWholeTerm m x := by
  simp only [thetaTerm, xiWholeTerm]
  rw [show 9 * (2 * x) / 2 = 9 * x by ring,
    show 5 * (2 * x) / 2 = 5 * x by ring,
    show 2 * (2 * x) = 4 * x by ring]
  ring

/-- The theta kernel at `2 * x` is twice the whole-line xi kernel at `x`. -/
theorem thetaPhi_two_mul (x : ℝ) :
    thetaPhi (2 * x) = 2 * xiWholePhi x := by
  unfold thetaPhi xiWholePhi
  rw [← tsum_mul_left]
  exact tsum_congr fun m ↦ thetaTerm_two_mul m x

/-- The theta kernel satisfies `thetaPhi t = 2 * xiWholePhi (t / 2)`. -/
theorem thetaPhi_eq_two_mul_xiWholePhi (t : ℝ) :
    thetaPhi t = 2 * xiWholePhi (t / 2) := by
  rw [← thetaPhi_two_mul]
  congr 1
  ring

/-- The half-line integral `xiThetaIntegral w` is eight times the integral over `(0, ∞)` of
`xiWholePhi x * cosh (2 * x * w)`. -/
theorem xiThetaIntegral_eq_eight_mul_whole (w : ℂ) :
    xiThetaIntegral w =
      8 * ∫ x : ℝ in Set.Ioi 0,
        (xiWholePhi x : ℂ) * Complex.cosh (((2 * x : ℝ) : ℂ) * w) := by
  let g : ℝ → ℂ := fun t ↦
    (thetaPhi t : ℂ) * Complex.cosh ((t : ℂ) * w)
  let Kfun : ℝ → ℂ := fun x ↦
    (xiWholePhi x : ℂ) *
      Complex.cosh (((2 * x : ℝ) : ℂ) * w)
  have hcv := MeasureTheory.integral_comp_mul_left_Ioi g 0
    (by norm_num : (0 : ℝ) < 2)
  rw [show (2 : ℝ) * 0 = 0 by ring] at hcv
  have hscale :
      (∫ t : ℝ in Set.Ioi 0, g t) =
        2 * ∫ x : ℝ in Set.Ioi 0, g (2 * x) := by
    rw [hcv]
    simp
  have hJ :
      (∫ x : ℝ in Set.Ioi 0, g (2 * x)) =
        2 * ∫ x : ℝ in Set.Ioi 0, Kfun x := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [g, Kfun]
    rw [thetaPhi_two_mul]
    push_cast
    ring
  unfold xiThetaIntegral
  change 2 * ∫ t : ℝ in Set.Ioi 0, g t =
    8 * ∫ x : ℝ in Set.Ioi 0, Kfun x
  rw [hscale, hJ]
  ring

/-- The theta integral `xiThetaIntegral w` equals the centered Riemann xi function
`centeredXi w`. -/
theorem xiThetaIntegral_eq_centeredXi (w : ℂ) :
    xiThetaIntegral w = centeredXi w := by
  rw [xiThetaIntegral_eq_eight_mul_whole]
  have hhalf := ThetaKernel.integral_Ioi_ccosh_mul_Phi (2 * w)
  have hconvert :
      (∫ x : ℝ in Set.Ioi 0,
          (xiWholePhi x : ℂ) *
            Complex.cosh ((((2 * x : ℝ) : ℂ)) * w)) =
        ThetaKernel.xi (1 / 2 + (2 * w) / 2) / 8 := by
    rw [← hhalf]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [xiWholePhi_eq_thetaKernel]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  rw [hconvert]
  unfold centeredXi riemannXi ThetaKernel.xi
  ring_nf

end RiemannJensen
