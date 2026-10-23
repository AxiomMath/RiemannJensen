module

public import RiemannJensen.Dedekind.FinalRootAssembly
public import RiemannJensen.Dedekind.LeadingSaddlePhase
public import RiemannJensen.Dedekind.AmplitudeBounds
public import RiemannJensen.Dedekind.ActionEffective
public import RiemannJensen.Dedekind.XiConsequences

/-!
# Negative real roots of the Dedekind Jensen polynomials

For a number field `K`, this file supplies the inputs of `DedekindFinalAssembly.Inputs` for the
completed Dedekind zeta function `entireDedekindXi K`, assuming the oscillation estimate
`DedekindOscillation K`, and deduces the lower bound on the number of negative real roots of the
Jensen polynomials of `entireDedekindXi K`.

## Main definitions

* `DedekindOscillation`: The oscillation estimate comparing the rescaled Jensen polynomial at
  `-q` with twice the real part of the leading saddle term on the counting window.

## Main results

* `exists_canonical_final_inputs`: Under `DedekindOscillation K`, the assembly inputs for
  `entireDedekindXi K` exist.
* `canonical_prop_real_roots`: Under `DedekindOscillation K`, the number of negative real roots of
  the degree-`d` Jensen polynomial is eventually at least `d - C * √(d log d)`.
* `canonical_thm_main`: Under `DedekindOscillation K`, the degree-`d` Jensen polynomial is
  eventually nonzero and has at least `d - C * √(d log d)` negative real roots.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Filter Topology Polynomial

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- There are `M, c₀ > 0` and `C` such that, for all large `d` and all `q` in
`dedekindCountingWindow K M c₀ d`, the rescaled Jensen polynomial evaluated at `-q` differs from
`2 * (dedekindLeadingSaddle K d q).re` by at most
`C * ‖dedekindLeadingSaddle K d q‖ * (log d) ^ (-1 / 10)`. -/
def DedekindOscillation : Prop :=
  ∃ M c₀ C : ℝ, 0 < M ∧ 0 < c₀ ∧
    ∀ᶠ d : ℕ in atTop, ∀ q ∈ dedekindCountingWindow K M c₀ d,
      |(rescaledDedekindJensenK K d).eval (-q) -
          2 * (dedekindLeadingSaddle K d q).re| ≤
        C * ‖dedekindLeadingSaddle K d q‖ *
          Real.log (d : ℝ) ^ (-(1 / 10 : ℝ))

private theorem eventually_dedekindEdgeQ_nonneg : ∀ᶠ d : ℕ in atTop, 0 ≤ dedekindEdgeQ K d := by
  filter_upwards [eventually_ge_atTop 1] with d hd
  have hΛ := dedekindScaleLambda_pos K d hd
  unfold dedekindEdgeQ dedekindSaddleQ saddleQAtLambda
  rw [sinRatio_zero]
  have hr : 0 < saddleRadiusAtLambda (dedekindScaleLambda K d) 0 := by
    simpa [dedekindSaddleRadius] using dedekindSaddleRadius_pos K d hd ⟨le_rfl, by positivity⟩
  have hk : 0 < saddleKappa := by
    rw [saddleKappa]
    positivity
  positivity

private theorem eventually_continuousOn_saddleAction (M c₀ : ℝ) (hM : 0 < M) (hc₀one : c₀ < 1) :
    ∀ᶠ d : ℕ in atTop,
      ContinuousOn (Dedekind.saddleAction K d)
        (Dedekind.countingWindow K M c₀ d) := by
  filter_upwards [eventually_ge_atTop 2] with d hd
  have hd1 : 1 ≤ d := by omega
  have hT : 0 < dedekindScaleT K d := dedekindScaleT_pos K d hd1
  have hτ : 0 < dedekindEdgeOffset M d := Dedekind.edgeOffset_pos hM hd
  have hsub : dedekindCountingWindow K M c₀ d ⊆
      Ioo (dedekindEdgeQ K d) (dedekindScaleT K d) := fun q hq =>
    ⟨by linarith [hq.1], hq.2.trans_lt (by
      unfold dedekindUpperEndpoint
      nlinarith)⟩
  exact fun q hq => (dedekind_action_derivative K d hd1 (hsub hq)).continuousAt.continuousWithinAt

private theorem eventually_dedekindLeadingSaddle_ne_zero (M c₀ cA : ℝ)
    (hM : 0 < M) (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1) (hcA : c₀ ≤ cA)
    (hAmp : ∀ c : ℝ, 0 < c → c ≤ cA →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
        dedekindEdgeQ K d < q → q ≤ c * dedekindScaleT K d →
        dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q) ≠ 0) :
    ∀ᶠ d : ℕ in atTop, ∀ q ∈ dedekindCountingWindow K M c₀ d,
      dedekindLeadingSaddle K d q ≠ 0 := by
  obtain ⟨D, hD1, hH⟩ := eventually_dedekindSaddleHessian_re_bounds K
  filter_upwards [hAmp c₀ hc₀ hcA, eventually_ge_atTop D, eventually_ge_atTop 2]
    with d hamp hdD hd2 q hq
  have hd1 : 1 ≤ d := hD1.trans hdD
  have hτ : 0 < dedekindEdgeOffset M d := Dedekind.edgeOffset_pos hM hd2
  have hedge : dedekindEdgeQ K d < q := by linarith [hq.1]
  have hmem : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) :=
    ⟨hedge, hq.2.trans (mul_le_of_le_one_left (dedekindScaleT_pos K d hd1).le hc₀one)⟩
  have hrange := dedekindSaddle_inverse_range K d hd1 hmem
  have hHb := hH d hdD (dedekindSaddleAngle K d q) hrange
  rw [dedekindSaddle_inverse K d hd1 hmem] at hHb
  have hsin : 0 < Real.sin (dedekindSaddleAngle K d q) :=
    Real.sin_pos_of_pos_of_lt_pi hrange.1 (by linarith [hrange.2, Real.pi_pos])
  have hDne : dedekindSaddleHessian K d q ≠ 0 :=
    Complex.ne_zero_of_re_pos ((sq_pos_of_pos hsin).trans_le hHb.1)
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrad : (2 * Real.pi * d * dedekindSaddleHessian K d q : ℂ) ≠ 0 := by
    simp [hdne, hDne, Real.pi_ne_zero]
  unfold dedekindLeadingSaddle
  refine div_ne_zero (mul_ne_zero (div_ne_zero (mod_cast d.factorial_ne_zero)
    (pow_ne_zero _ hdne)) (mul_ne_zero (hamp q hedge hq.2) (exp_ne_zero _)))
    (sqrt_eq_exp hrad ▸ exp_ne_zero _)

/-- The Jensen polynomials of `entireDedekindXi K` are eventually nonzero. -/
theorem eventually_dedekindJensen_entireDedekindXi_ne_zero :
    ∀ᶠ d : ℕ in atTop, dedekindJensen (entireDedekindXi K) d ≠ 0 := by
  obtain ⟨D, hD⟩ := eventually_dedekindJensenK_ne_zero K
  filter_upwards [eventually_ge_atTop D] with d hd
  simpa [dedekindJensenK_eq] using hD d hd

/-- Under `DedekindOscillation K`, the inputs `DedekindFinalAssembly.Inputs` exist for the
completed Dedekind zeta function `entireDedekindXi K`. -/
theorem exists_canonical_final_inputs (hosc : DedekindOscillation K) :
    Nonempty (DedekindFinalAssembly.Inputs (entireDedekindXi K)) := by
  obtain ⟨M, cOsc, Cosc, hM, hcOsc, hosc⟩ := hosc
  obtain ⟨cPolar, hcPolar, hpolar⟩ := eventually_dedekind_leading_polar_on_window K
  obtain ⟨cCont, hcCont, hcont⟩ := dedekind_phase_correction_continuous K
  obtain ⟨cSpan, hcSpan, hspan⟩ := dedekind_phase_span K M hM
  obtain ⟨cAmp, hcAmp, hamp⟩ := dedekind_saddle_amplitude_nonzero K
  let c₀ := min cOsc (min cPolar (min cCont (min cSpan (min cAmp (1 / 2)))))
  have hc₀ : 0 < c₀ := by positivity
  have hc₀half : c₀ ≤ 1 / 2 := by simp [c₀]
  obtain ⟨Cspan, hspan'⟩ := hspan c₀ hc₀ (by simp [c₀])
  exact ⟨{
    N := dedekindDegree K
    N_pos := mod_cast dedekindDegree_pos K
    T := dedekindScaleT K
    Λ := dedekindScaleLambda K
    scale_product := (eventually_ge_atTop 1).mono (dedekindScale_product K)
    scale_lambda_pos := (eventually_ge_atTop 1).mono (dedekindScaleLambda_pos K)
    scale_lambda_upper := eventually_atTop.2 (eventually_dedekindScaleLambda_le_three_log K)
    qe := dedekindEdgeQ K
    qe_nonneg := eventually_dedekindEdgeQ_nonneg K
    M := M
    c₀ := c₀
    M_pos := hM
    c₀_pos := hc₀
    jensen_ne_zero := eventually_dedekindJensen_entireDedekindXi_ne_zero K
    window_nonempty := by
      filter_upwards [dedekind_window_nonempty K M c₀ hM hc₀] with d hd
      rwa [dedekindCountingWindow, Set.nonempty_Icc] at hd
    Z := dedekindLeadingSaddle K
    oscillation := ⟨Cosc, by
      filter_upwards [hosc, eventually_ge_atTop 1] with d hdosc hd1 q hq
      exact hdosc q ⟨hq.1, hq.2.trans
        (mul_le_mul_of_nonneg_right (by simp [c₀]) (dedekindScaleT_pos K d hd1).le)⟩⟩
    leading_ne_zero := eventually_dedekindLeadingSaddle_ne_zero K M c₀ cAmp hM hc₀
      (hc₀half.trans (by norm_num)) (by simp [c₀]) hamp
    S := Dedekind.saddleAction K
    ω := Dedekind.phaseCorrection K
    leading_polar := hpolar M c₀ hM hc₀ (by simp [c₀])
    phase_correction_continuous := hcont M c₀ hM hc₀ (by simp [c₀])
    action_continuous := eventually_continuousOn_saddleAction K M c₀ hM
      (hc₀half.trans_lt (by norm_num))
    phase_span := ⟨Cspan, hspan'⟩ }⟩

/-- Under `DedekindOscillation K`, there are `C > 0` and `D` such that for every `d ≥ D` the
degree-`d` Dedekind Jensen polynomial has at least `d - C * √(d log d)` negative real roots. -/
theorem canonical_prop_real_roots (hosc : DedekindOscillation K) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      (d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (dedekindNegativeRootCountK K d : ℝ) := by
  obtain ⟨I⟩ := exists_canonical_final_inputs K hosc
  simpa [dedekindNegativeRootCountK_eq] using
    (DedekindFinalAssembly.eventual_negativeRootCount_bound
      (entireDedekindXi K) I)

/-- Under `DedekindOscillation K`, there are `C > 0` and `d₀ ≥ 2` such that for every `d ≥ d₀`
the degree-`d` Dedekind Jensen polynomial `dedekindJensenK K d` is nonzero and has at least
`d - C * √(d log d)` negative real roots. -/
theorem canonical_thm_main (hosc : DedekindOscillation K) :
    ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      dedekindJensenK K d ≠ 0 ∧
        (d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
          (dedekindNegativeRootCountK K d : ℝ) := by
  obtain ⟨I⟩ := exists_canonical_final_inputs K hosc
  simpa [dedekindJensenK_eq, dedekindNegativeRootCountK_eq] using
    (DedekindFinalAssembly.dedekindJensen_main (entireDedekindXi K) I)

end

end RiemannJensen
