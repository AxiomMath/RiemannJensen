module

public import RiemannJensen.Dedekind.AmplitudeDerivative
public import RiemannJensen.Dedekind.EffectiveLog
public import RiemannJensen.Dedekind.LocalPhaseBounds
public import RiemannJensen.Analysis.GaussianAdapter
public import RiemannJensen.Analysis.LowerContourLocal

/-!
# Gaussian approximation for the normalized Dedekind saddle integral

For a number field `K`, the normalized local integral
`∫ y in -1..1, f y * exp (n * p y)` of the Dedekind saddle-point analysis is compared with its
Gaussian main term `f 0 * (π / ((n / 2) * (D / ‖D‖))) ^ (1 / 2)`, with a relative error of order
`n ^ (-1 / 10)` uniformly on the counting windows.

## Main results

* `dedekind_normalized_local_gaussian_of_C3_C1`: the relative Gaussian estimate for an amplitude
  of class `C¹` and a phase of class `C³` on `[-1, 1]` with explicit bounds.
* `dedekind_local_gaussian_adapter`: the uniform relative Gaussian approximation for the
  normalized Dedekind local integral on every admissible counting window.
-/

@[expose] public section

namespace RiemannJensen

open _root_.Complex Set Filter MeasureTheory intervalIntegral

noncomputable section

/-- Let `f` be of class `C¹` and `p` of class `C³` on `[-1, 1]`, with `f 0 = 1`, `p 0 = p' 0 = 0`,
`p'' 0 = -D / ‖D‖`, `re (p y) ≤ 0`, `c * |y| ≤ ‖p' y‖`, and `f, f', p'', p'''` bounded by `C`.
Then for `1 ≤ n` the integral `∫ y in -1..1, f y * exp (n * p y)` differs from its Gaussian main
term by at most `windowRelConst c C * n ^ (-1 / 10)` times the norm of that main term. -/
theorem dedekind_normalized_local_gaussian_of_C3_C1
    {f f' p p' p'' p''' : ℝ → ℂ} {D : ℂ} {n c C : ℝ}
    (hn : 1 ≤ n) (hc : 0 < c) (hC : 0 ≤ C)
    (hDre : 0 < D.re)
    (hf : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt f (f' y) y)
    (hfcont : ContinuousOn f' (Icc (-1 : ℝ) 1))
    (hp : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p (p' y) y)
    (hp' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hf0 : f 0 = 1) (hp0 : p 0 = 0) (hp'0 : p' 0 = 0)
    (hp''0 : p'' 0 = -(D / (‖D‖ : ℂ)))
    (hre : ∀ y ∈ Icc (-1 : ℝ) 1, (p y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1 : ℝ) 1, c * |y| ≤ ‖p' y‖)
    (hfbd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖f y‖ ≤ C)
    (hf'bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖f' y‖ ≤ C)
    (hp''bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p'' y‖ ≤ C)
    (hp'''bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p''' y‖ ≤ C) :
    ‖(∫ y in (-1 : ℝ)..1, f y * Complex.exp ((n : ℂ) * p y)) -
        f 0 * (((Real.pi : ℂ) /
          (((n / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ ≤
      ‖f 0 * (((Real.pi : ℂ) /
          (((n / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ *
        windowRelConst c C * n ^ (-(1 : ℝ) / 10) := by
  let A : ℂ := D / (‖D‖ : ℂ)
  let G : ℂ := ((Real.pi : ℂ) / (((n / 2 : ℝ) : ℂ) * A)) ^ (1 / 2 : ℂ)
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hAn : ‖A‖ = 1 := norm_div_norm_eq_one hDre
  have hAre : 0 < A.re := re_div_norm_pos hDre
  have hGn : ‖G‖ = Real.sqrt (2 * Real.pi / n) :=
    Gaussian.norm_gaussian_main_term hn0 hAn hAre
  change ‖(∫ y in (-1 : ℝ)..1, f y * Complex.exp ((n : ℂ) * p y)) -
      f 0 * G‖ ≤ ‖f 0 * G‖ * windowRelConst c C * n ^ (-(1 : ℝ) / 10)
  rw [norm_mul, hGn, windowRelConst]
  calc
    ‖(∫ y in (-1 : ℝ)..1, f y * Complex.exp ((n : ℂ) * p y)) - f 0 * G‖
        ≤ gaussianErrorConst c C * n ^ (-(3 : ℝ) / 5) := by
          simpa [G, A, gaussianErrorConst] using Gaussian.gaussian_estimate_of_C3_C1
            (A := A) (n := n) hn hc hC hAn hAre hf hfcont hp hp' hp'' hp0 hp'0
            (by simpa [A] using hp''0) hre hlower hfbd hf'bd hp''bd hp'''bd
    _ = ‖f 0‖ * Real.sqrt (2 * Real.pi / n) *
          (gaussianErrorConst c C / Real.sqrt (2 * Real.pi)) *
          n ^ (-(1 : ℝ) / 10) := by
          rw [hf0, norm_one, one_mul, ← sqrt_div_sqrt_mul_rpow hn0]
          field_simp [(Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)).ne']

/-- A function of norm `1` at `0` whose derivative has norm at most `1 / 2` on `[-1, 1]` has
norm at most `3 / 2` on `[-1, 1]`. -/
theorem norm_le_three_halves_of_hasDerivAt {h h' : ℝ → ℂ}
    (hd : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt h (h' t) t)
    (hb : ∀ t ∈ Icc (-1 : ℝ) 1, ‖h' t‖ ≤ 1 / 2) (h0 : ‖h 0‖ = 1) :
    ∀ y ∈ Icc (-1 : ℝ) 1, ‖h y‖ ≤ 3 / 2 := by
  intro y hy
  have hsub := Gaussian.norm_sub_zero_le_of_hasDerivAt
    (fun t ht => hd t (Gaussian.uIcc_zero_subset hy ht))
    (fun t ht => hb t (Gaussian.uIcc_zero_subset hy ht))
  have hy1 : |y| ≤ 1 := abs_le.2 hy
  linarith [norm_le_norm_sub_add (h y) (h 0)]

/-- For `0 < M`, `c₀ ≤ 1` and `2 ≤ d`, every point of the counting window
`dedekindCountingWindow K M c₀ d` lies in `(dedekindEdgeQ K d, dedekindScaleT K d]`. -/
theorem mem_Ioc_of_mem_dedekindCountingWindow (K : Type) [Field K] [NumberField K]
    {M c₀ q : ℝ} {d : ℕ} (hM : 0 < M) (hc₀ : c₀ ≤ 1) (hd : 2 ≤ d)
    (hq : q ∈ dedekindCountingWindow K M c₀ d) :
    q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hτ : 0 < dedekindEdgeOffset M d :=
    mul_pos hM (Real.sqrt_pos.2 (div_pos (Real.log_pos hdR) (by positivity)))
  exact ⟨by linarith [hq.1],
    hq.2.trans (mul_le_of_le_one_left (dedekindScaleT_pos K d (by omega)).le hc₀)⟩

/-- On `(dedekindEdgeQ K d, dedekindScaleT K d]`, if `4π ≤ dedekindScaleLambda K d`, the Dedekind
saddle Hessian has positive real part. -/
theorem dedekindSaddleHessian_re_pos (K : Type) [Field K] [NumberField K] {d : ℕ} {q : ℝ}
    (hd : 1 ≤ d) (hΛ : 4 * Real.pi ≤ dedekindScaleLambda K d)
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    0 < (dedekindSaddleHessian K d q).re := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hD := dedekindSaddleHessian_re_bounds K d hd hΛ hα
  rw [dedekindSaddle_inverse K d hd hq] at hD
  have hsin : 0 < Real.sin (dedekindSaddleAngle K d q) :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  exact (pow_pos hsin 2).trans_le hD.1

/-- The relative Gaussian estimate for the normalized Dedekind local integral at a single `d` and
`q ∈ (dedekindEdgeQ K d, dedekindScaleT K d]`, from bounds by `C₀ ≥ 3 / 2` on the amplitude and
the standard local phase estimates there. -/
theorem dedekind_local_gaussian_of_bounds (K : Type) [Field K] [NumberField K]
    {d : ℕ} {q C₀ : ℝ} (hd : 1 ≤ d) (hΛ : 4 * Real.pi ≤ dedekindScaleLambda K d)
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hn : 1 ≤ dedekindEffectiveN K d q) (hC₀ : 3 / 2 ≤ C₀)
    (hf : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt (normalizedDedekindLocalAmplitude K d q)
      (dedekindLocalAmplitudeDeriv K d q y) y ∧ ‖dedekindLocalAmplitudeDeriv K d q y‖ ≤ C₀)
    (hfcont : ContinuousOn (dedekindLocalAmplitudeDeriv K d q) (Icc (-1 : ℝ) 1))
    (hf0 : normalizedDedekindLocalAmplitude K d q 0 = 1)
    (hfbd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖normalizedDedekindLocalAmplitude K d q y‖ ≤ C₀)
    (hp''0 : iteratedDeriv 2 (dedekindLocalPhase K d q) 0 =
      -(dedekindSaddleHessian K d q / (‖dedekindSaddleHessian K d q‖ : ℂ)))
    (hre : ∀ y ∈ Icc (-1 : ℝ) 1, (dedekindLocalPhase K d q y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1 : ℝ) 1,
      (1 / 2 : ℝ) * |y| ≤ ‖deriv (dedekindLocalPhase K d q) y‖)
    (hthird : ∀ y ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv 3 (dedekindLocalPhase K d q) y‖ ≤ (1 / 2 : ℝ)) :
    ‖(∫ y in (-1 : ℝ)..1, normalizedDedekindLocalAmplitude K d q y *
          Complex.exp ((dedekindEffectiveN K d q : ℂ) * dedekindLocalPhase K d q y)) -
        normalizedDedekindLocalAmplitude K d q 0 * (((Real.pi : ℂ) /
          (((dedekindEffectiveN K d q / 2 : ℝ) : ℂ) * (dedekindSaddleHessian K d q /
            (‖dedekindSaddleHessian K d q‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ ≤
      ‖normalizedDedekindLocalAmplitude K d q 0 * (((Real.pi : ℂ) /
          (((dedekindEffectiveN K d q / 2 : ℝ) : ℂ) * (dedekindSaddleHessian K d q /
            (‖dedekindSaddleHessian K d q‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ *
        windowRelConst (1 / 2) C₀ * dedekindEffectiveN K d q ^ (-(1 : ℝ) / 10) := by
  have hDre := dedekindSaddleHessian_re_pos K hd hΛ hq
  have hphase := fun y (hy : y ∈ Icc (-1 : ℝ) 1) =>
    dedekindLocalPhase_hasDerivAt_chain K d hd hq hy
  have hp''bd := norm_le_three_halves_of_hasDerivAt (fun y hy => (hphase y hy).2.2) hthird
    (by rw [hp''0, norm_neg, norm_div_norm_eq_one hDre])
  exact dedekind_normalized_local_gaussian_of_C3_C1 hn (by norm_num) (by linarith)
    hDre (fun y hy => (hf y hy).1) hfcont
    (fun y hy => (hphase y hy).1) (fun y hy => (hphase y hy).2.1)
    (fun y hy => (hphase y hy).2.2) hf0 (dedekindLocalPhase_zero K d q)
    (dedekindLocalPhase_first K d hd hq) hp''0 hre hlower hfbd (fun y hy => (hf y hy).2)
    (fun y hy => (hp''bd y hy).trans hC₀) (fun y hy => (hthird y hy).trans (by linarith))

/-- Uniform relative Gaussian approximation for the normalized Dedekind local integral on every
fixed admissible counting window: the error is at most `C * n ^ (-1 / 10)` times the norm of the
Gaussian main term, eventually in `d`, for every `q` in `dedekindCountingWindow K M c₀ d`. -/
theorem dedekind_local_gaussian_adapter
    (K : Type) [Field K] [NumberField K] :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧
      ∀ M c₀ : ℝ, 0 < M → 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q ∈ dedekindCountingWindow K M c₀ d,
        let n := dedekindEffectiveN K d q
        let D := dedekindSaddleHessian K d q
        let f := normalizedDedekindLocalAmplitude K d q
        let p := dedekindLocalPhase K d q
        ‖(∫ y in (-1 : ℝ)..1, f y * Complex.exp ((n : ℂ) * p y)) -
            f 0 * (((Real.pi : ℂ) /
              (((n / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ ≤
          ‖f 0 * (((Real.pi : ℂ) /
              (((n / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ *
            C * n ^ (-(1 : ℝ) / 10) := by
  obtain ⟨cA, CA, hcA, hCA, hamp⟩ := dedekind_local_amplitude_bound K
  obtain ⟨cD, CD, hcD, hCD, hderiv⟩ := dedekind_local_amplitude_deriv K
  obtain ⟨cZ, hcZ, hzero⟩ := eventually_normalizedDedekindLocalAmplitude_zero K
  obtain ⟨cC, hcC, hcont⟩ := eventually_continuousOn_dedekindLocalAmplitudeDeriv K
  let c₁ : ℝ := min 1 (min cA (min cD (min cZ cC)))
  let C₀ : ℝ := max CA (max CD (3 / 2 : ℝ))
  let C : ℝ := windowRelConst (1 / 2) C₀
  have hc₁ : 0 < c₁ := lt_min zero_lt_one (lt_min hcA (lt_min hcD (lt_min hcZ hcC)))
  have hC₀ : 0 < C₀ := hCA.trans_le (le_max_left _ _)
  have hC : 0 < C := by
    unfold C windowRelConst gaussianErrorConst
    have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    positivity
  refine ⟨c₁, C, hc₁, hC, fun M c₀ hM hc₀ hc₀c₁ => ?_⟩
  simp only [c₁, le_min_iff] at hc₀c₁
  obtain ⟨hc₀one, hc₀A, hc₀D, hc₀Z, hc₀C⟩ := hc₀c₁
  obtain ⟨ce, hce, heffective⟩ :=
    eventually_effectiveN_countingWindow_log_lower K M c₀ hM hc₀ hc₀one
  have hloglarge : ∀ᶠ d : ℕ in atTop, 1 / ce ≤ Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨DΛ, hDΛ⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  filter_upwards [hamp c₀ hc₀ hc₀A, hderiv c₀ hc₀ hc₀D,
    hzero c₀ hc₀ hc₀Z, hcont c₀ hc₀ hc₀C,
    eventually_dedekindLocalPhase_re_nonpos K,
    eventually_dedekindLocalPhase_taylor K,
    eventually_dedekindLocalPhase_third K,
    eventually_dedekindLocalPhase_deriv_lower K,
    eventually_ge_atTop DΛ,
    heffective, hloglarge, eventually_ge_atTop 2] with
      d hampd hderivd hzerod hcontd hred htaylor hthird hlower hdΛ
      heffectived hlogd hd2
  intro q hq
  have hqr := mem_Ioc_of_mem_dedekindCountingWindow K hM hc₀one hd2 hq
  have hqtop : q ≤ c₀ * dedekindScaleT K d := hq.2
  have hn : 1 ≤ dedekindEffectiveN K d q :=
    (by linarith [(div_le_iff₀ hce).mp hlogd] : (1 : ℝ) ≤ ce * Real.log d).trans
      (heffectived q hq)
  simpa [C, C₀] using dedekind_local_gaussian_of_bounds K (C₀ := C₀) (by omega)
    (by linarith [hDΛ d hdΛ, Real.pi_pos]) hqr hn ((le_max_right _ _).trans (le_max_right _ _))
    (fun y hy => (hderivd q hqr.1 hqtop y (abs_le.2 hy)).imp_right
      (·.trans ((le_max_left _ _).trans (le_max_right _ _))))
    (hcontd q hqr.1 hqtop) (hzerod q hqr.1 hqtop)
    (fun y hy => (hampd q hqr.1 hqtop y (abs_le.2 hy)).trans (le_max_left _ _))
    (htaylor q hqr.1 hqr.2) (hred q hqr.1 hqr.2) (hlower q hqr.1 hqr.2) (hthird q hqr.1 hqr.2)

end

end RiemannJensen
