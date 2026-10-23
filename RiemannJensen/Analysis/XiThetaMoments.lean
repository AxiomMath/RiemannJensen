module

public import RiemannJensen.Analysis.XiThetaMellin

/-!
# Theta moments and the Taylor coefficients of `centeredXi`

The even Taylor coefficients of `centeredXi` at zero are positive multiples of the moments
$\int_0^\infty \varphi(t) t^{2j}\,dt$ of `thetaPhi`, hence positive.

## Main definitions

* `XiThetaMoments.ExpMoments`: a function has every exponential moment on `(0, ∞)`.
* `XiThetaMoments.expMoment`: the `k`-th differentiated exponential transform.

## Main results

* `XiThetaMoments.iteratedDeriv_two_mul_coshTransform`: the even derivatives at zero of the
  cosh transform of `φ` are twice the even moments of `φ`.
* `XiThetaMoments.moment_pos`: the moments of a function positive on `(0, ∞)` are positive.
* `expMoments_thetaPhi`: `thetaPhi` has every exponential moment on `(0, ∞)`.
* `gammaCoeff_eq_thetaGammaCoeff`: `gammaCoeff j = thetaGammaCoeff j`.
* `gammaCoeff_pos`: every `gammaCoeff j` is positive.
-/

@[expose] public section

open MeasureTheory Set Complex Metric

noncomputable section

namespace RiemannJensen

namespace XiThetaMoments

/-- `φ` has every exponential moment on the positive half-line. -/
def ExpMoments (φ : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (a : ℝ),
    IntegrableOn (fun t => φ t * t ^ n * Real.exp (a * t)) (Ioi 0)

/-- The differentiated exponential-transform integrand. -/
def term (φ : ℝ → ℝ) (s : ℝ) (k : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  (φ t : ℂ) * ((s * t : ℝ) : ℂ) ^ k *
    Complex.exp (((s * t : ℝ) : ℂ) * w)

/-- The `k`-th differentiated exponential transform. -/
def expMoment (φ : ℝ → ℝ) (s : ℝ) (k : ℕ) (w : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), term φ s k w t

variable {φ : ℝ → ℝ}

/-- A function with every exponential moment is a.e. strongly measurable on `(0, ∞)`. -/
lemma aestronglyMeasurable_of_expMoments (hφ : ExpMoments φ) :
    AEStronglyMeasurable φ (volume.restrict (Ioi (0 : ℝ))) := by
  simpa using (hφ 0 0).aestronglyMeasurable

/-- If `φ` has every exponential moment, then `|φ t| * t ^ n * exp (a * t)` is integrable
on `(0, ∞)`. -/
lemma integrable_bound (hφ : ExpMoments φ) (n : ℕ) (a : ℝ) :
    IntegrableOn (fun t => |φ t| * t ^ n * Real.exp (a * t)) (Ioi 0) := by
  refine (hφ n a).norm.congr ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp [norm_mul, abs_of_pos ht, abs_of_pos (Real.exp_pos _)]

/-- For `|s| = 1`, `‖w‖ ≤ R` and `t > 0`, the integrand `term φ s k w t` has norm at most
`|φ t| * t ^ k * exp (R * t)`. -/
lemma norm_term_le {s : ℝ} (hs : |s| = 1) (k : ℕ) {w : ℂ} {R : ℝ}
    (hw : ‖w‖ ≤ R) {t : ℝ} (ht : 0 < t) :
    ‖term φ s k w t‖ ≤ |φ t| * t ^ k * Real.exp (R * t) := by
  have hst : |s * t| = t := by
    rw [abs_mul, hs, one_mul, abs_of_pos ht]
  have hre : s * t * w.re ≤ R * t :=
    calc
      s * t * w.re ≤ |s * t * w.re| := le_abs_self _
      _ = t * |w.re| := by rw [abs_mul, hst]
      _ ≤ t * R := mul_le_mul_of_nonneg_left ((abs_re_le_norm w).trans hw) ht.le
      _ = R * t := mul_comm _ _
  unfold term
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, hst,
    Complex.re_ofReal_mul]
  gcongr

/-- The integrand `term φ s k w` is a.e. strongly measurable on `(0, ∞)`. -/
lemma aestronglyMeasurable_term (hφ : ExpMoments φ) (s : ℝ) (k : ℕ)
    (w : ℂ) :
    AEStronglyMeasurable (term φ s k w) (volume.restrict (Ioi (0 : ℝ))) := by
  refine ((Complex.continuous_ofReal.comp_aestronglyMeasurable
    (aestronglyMeasurable_of_expMoments hφ)).mul ?_).mul ?_ <;>
  exact Continuous.aestronglyMeasurable (by fun_prop)

/-- For `|s| = 1`, the integrand `term φ s k w` is integrable on `(0, ∞)`. -/
lemma integrable_term (hφ : ExpMoments φ) {s : ℝ} (hs : |s| = 1)
    (k : ℕ) (w : ℂ) :
    Integrable (term φ s k w) (volume.restrict (Ioi (0 : ℝ))) :=
  (integrable_bound hφ k ‖w‖).mono' (aestronglyMeasurable_term hφ s k w)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ht => norm_term_le hs k le_rfl ht)

/-- The derivative in `w` of `term φ s k w t` is `term φ s (k + 1) w t`. -/
lemma hasDerivAt_term (s : ℝ) (k : ℕ) (t : ℝ) (x : ℂ) :
    HasDerivAt (fun w => term φ s k w t) (term φ s (k + 1) x t) x := by
  have h := (((hasDerivAt_id x).const_mul ((s * t : ℝ) : ℂ)).cexp).const_mul
    ((φ t : ℂ) * ((s * t : ℝ) : ℂ) ^ k)
  unfold term
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- For `|s| = 1`, the derivative of `expMoment φ s k` is `expMoment φ s (k + 1)`. -/
lemma hasDerivAt_expMoment (hφ : ExpMoments φ) {s : ℝ} (hs : |s| = 1)
    (k : ℕ) (w₀ : ℂ) :
    HasDerivAt (expMoment φ s k) (expMoment φ s (k + 1) w₀) w₀ :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w t => term φ s k w t)
    (F' := fun w t => term φ s (k + 1) w t) (x₀ := w₀)
    (bound := fun t => |φ t| * t ^ (k + 1) *
      Real.exp ((‖w₀‖ + 1) * t))
    (ball_mem_nhds w₀ zero_lt_one)
    (Filter.Eventually.of_forall fun w => aestronglyMeasurable_term hφ s k w)
    (integrable_term hφ hs k w₀)
    (aestronglyMeasurable_term hφ s (k + 1) w₀)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht x hx => by
      refine norm_term_le hs (k + 1) ?_ ht
      rw [mem_ball, dist_eq_norm] at hx
      linarith [norm_sub_norm_le x w₀])
    (integrable_bound hφ (k + 1) (‖w₀‖ + 1))
    (Filter.Eventually.of_forall fun t x _ => hasDerivAt_term s k t x)).2

/-- The `n`-th derivative of `expMoment φ 1 0 + expMoment φ (-1) 0` is
`expMoment φ 1 n + expMoment φ (-1) n`. -/
lemma iteratedDeriv_expMoment_add (hφ : ExpMoments φ) (n : ℕ) :
    iteratedDeriv n
        (fun w => expMoment φ 1 0 w + expMoment φ (-1) 0 w) =
      fun w => expMoment φ 1 n w + expMoment φ (-1) n w := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext w
      exact ((hasDerivAt_expMoment hφ (by simp) n w).add
        (hasDerivAt_expMoment hφ (by simp) n w)).deriv

/-- The cosh transform `w ↦ 2 ∫_{(0, ∞)} φ t cosh (t w) dt` equals
`expMoment φ 1 0 + expMoment φ (-1) 0`. -/
lemma coshTransform_eq (hφ : ExpMoments φ) :
    (fun w : ℂ =>
        2 * ∫ t in Ioi (0 : ℝ),
          (φ t : ℂ) * Complex.cosh ((t : ℂ) * w)) =
      fun w => expMoment φ 1 0 w + expMoment φ (-1) 0 w := by
  funext w
  unfold expMoment
  rw [← integral_add (integrable_term hφ (by simp) 0 w)
    (integrable_term hφ (by simp) 0 w), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [term, pow_zero, mul_one, one_mul, Complex.cosh]
  push_cast
  ring_nf

/-- For `|s| = 1`, `expMoment φ s (2 * j) 0` is the moment `∫_{(0, ∞)} φ t * t ^ (2 * j) dt`. -/
lemma expMoment_zero_even (j : ℕ) (s : ℝ) (hs : |s| = 1) :
    expMoment φ s (2 * j) 0 =
      ((∫ t in Ioi (0 : ℝ), φ t * t ^ (2 * j) : ℝ) : ℂ) := by
  have hs2 : s ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
  unfold expMoment
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [term, mul_zero, Complex.exp_zero, mul_one]
  have hp : ((s * t) ^ (2 * j) : ℝ) = t ^ (2 * j) := by
    rw [pow_mul, mul_pow, hs2, one_mul, ← pow_mul]
  rw [← Complex.ofReal_pow, hp]
  push_cast
  ring

/-- Even derivatives at zero of the cosh transform are twice its moments. -/
theorem iteratedDeriv_two_mul_coshTransform (hφ : ExpMoments φ) (j : ℕ) :
    iteratedDeriv (2 * j)
        (fun w : ℂ => 2 * ∫ t in Ioi (0 : ℝ),
          (φ t : ℂ) * Complex.cosh ((t : ℂ) * w)) 0 =
      ((2 * ∫ t in Ioi (0 : ℝ), φ t * t ^ (2 * j) : ℝ) : ℂ) := by
  rw [coshTransform_eq hφ, iteratedDeriv_expMoment_add hφ]
  simp only
  rw [expMoment_zero_even j 1 (by simp),
    expMoment_zero_even j (-1) (by simp)]
  push_cast
  ring

/-- Every moment of a function positive on the positive half-line is positive. -/
theorem moment_pos (hφ : ExpMoments φ)
    (hpos : ∀ t, 0 < t → 0 < φ t) (n : ℕ) :
    0 < ∫ t in Ioi (0 : ℝ), φ t * t ^ n := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => φ t * t ^ n :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) =>
      (mul_pos (hpos t ht) (pow_pos ht n)).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn (by simpa using hφ n 0)]
  have hsupp : Function.support (fun t => φ t * t ^ n) ∩ Ioi 0 = Ioi 0 :=
    inter_eq_right.2 fun t (ht : 0 < t) => (mul_pos (hpos t ht) (pow_pos ht n)).ne'
  rw [hsupp, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- Exponential moments transfer through the rescaling
`θ(t) = 2 Φ(t / 2)`. -/
theorem expMoments_of_scaling {Phi θ : ℝ → ℝ}
    (hθ : ∀ t, θ t = 2 * Phi (t / 2))
    (hW : ∀ (k : ℕ) (a : ℝ),
      Integrable (fun t : ℝ => |t| ^ k * Real.exp (a * |t|) * Phi t)) :
    ExpMoments θ := by
  intro n a
  set f : ℝ → ℝ := fun x =>
    Phi x * x ^ n * Real.exp ((2 * a) * x) with hf
  have hbase : IntegrableOn f (Ioi 0) := by
    refine (hW n (2 * a)).integrableOn.congr_fun
      (fun x (hx : 0 < x) => ?_) measurableSet_Ioi
    simp only [hf, abs_of_pos hx]
    ring
  have hcomp : IntegrableOn (fun x => f ((1 / 2 : ℝ) * x)) (Ioi 0) := by
    rwa [integrableOn_Ioi_comp_mul_left_iff f 0
      (show (0 : ℝ) < 1 / 2 by norm_num), mul_zero]
  refine IntegrableOn.congr_fun (hcomp.const_mul ((2 : ℝ) ^ (n + 1)))
    (fun t _ => ?_) measurableSet_Ioi
  simp only [hf, hθ]
  rw [show (2 * a) * (1 / 2 * t) = a * t by ring,
    show t / 2 = 1 / 2 * t by ring, pow_succ, mul_pow]
  have h2 : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination
    (2 * Phi (1 / 2 * t) * t ^ n * Real.exp (a * t)) * h2

end XiThetaMoments

open XiThetaMoments

/-- `thetaPhi` has all exponential moments on `(0, ∞)`. -/
theorem expMoments_thetaPhi : ExpMoments thetaPhi :=
  expMoments_of_scaling (Phi := ThetaKernel.Phi)
    (fun t => by
      rw [thetaPhi_eq_two_mul_xiWholePhi, xiWholePhi_eq_thetaKernel])
    ThetaKernel.integrable_Phi_weight

/-- The Taylor coefficient `gammaCoeff j` equals its theta moment `thetaGammaCoeff j`. -/
theorem gammaCoeff_eq_thetaGammaCoeff (j : ℕ) :
    gammaCoeff j = thetaGammaCoeff j := by
  unfold gammaCoeff thetaGammaCoeff thetaMoment
  rw [show centeredXi = xiThetaIntegral from
    funext fun w => (xiThetaIntegral_eq_centeredXi w).symm]
  unfold xiThetaIntegral
  rw [iteratedDeriv_two_mul_coshTransform expMoments_thetaPhi j,
    Complex.ofReal_re]
  ring

/-- Every coefficient of the square-root xi model is strictly positive. -/
theorem gammaCoeff_pos (j : ℕ) : 0 < gammaCoeff j := by
  rw [gammaCoeff_eq_thetaGammaCoeff, thetaGammaCoeff]
  unfold thetaMoment
  exact mul_pos (div_pos (by positivity) (by positivity))
    (moment_pos expMoments_thetaPhi (fun t ht => thetaPhi_pos ht.le) (2 * j))

end RiemannJensen
