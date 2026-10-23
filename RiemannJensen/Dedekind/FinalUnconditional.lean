module

public import RiemannJensen.Dedekind.LowerContributionFinal
public import RiemannJensen.Dedekind.OscillationAssembly

/-!
# Unconditional Dedekind oscillation and the almost-all-real-roots theorem

For a number field `K`, the rescaled Jensen polynomials of the Dedekind zeta function are
approximated on the counting window by twice the real part of the leading saddle term, with
relative error `O((log d) ^ (-1 / 10))`. Consequently the degree-`d` Jensen polynomial has at least
`d - O(√(d log d))` distinct negative real roots.

## Main results

* `dedekind_oscillation`: `DedekindOscillation K` holds.
* `dedekind_prop_real_roots`: for large `d`, the number of distinct negative real roots of the
  degree-`d` Jensen polynomial is at least `d - C * √(d log d)`.
* `dedekind_thm_main`: for all `d ≥ d₀`, the degree-`d` Jensen polynomial is nonzero and has at
  least `d - C * √(d log d)` distinct negative real roots.
-/

@[expose] public section

namespace RiemannJensen

open Filter

noncomputable section

variable (K : Type) [Field K] [NumberField K]

private theorem one_div_cube_le_log_rpow {d : ℕ} (hd : 1 ≤ d)
    (hlog : 1 ≤ Real.log (d : ℝ)) :
    1 / (d : ℝ) ^ 3 ≤ Real.log (d : ℝ) ^ (-(1 : ℝ) / 10) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : Real.log (d : ℝ) ^ (-(1 : ℝ)) ≤ Real.log (d : ℝ) ^ (-(1 : ℝ) / 10) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  rw [Real.rpow_neg_one] at h1
  have hlogle : Real.log (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < d),
      le_self_pow₀ hdR (by norm_num : 3 ≠ 0)]
  rw [one_div]
  exact (inv_anti₀ (by linarith) hlogle).trans h1

/-- The counting window shrinks as the edge parameter `M` grows and the cutoff `c` shrinks. -/
theorem dedekindCountingWindow_subset {M M' c c' : ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hM : M' ≤ M) (hc : c ≤ c') :
    dedekindCountingWindow K M c d ⊆ dedekindCountingWindow K M' c' d := by
  intro q hq
  refine ⟨hq.1.trans' ?_, hq.2.trans ?_⟩
  · unfold dedekindEdgeOffset
    gcongr
  · exact mul_le_mul_of_nonneg_right hc (dedekindScaleT_pos K d hd).le

/-- There are `M, c₀ > 0` with `c₀ ≤ π / 128` and `C > 0` such that, for all large `d` and all
`q` in `dedekindCountingWindow K M c₀ d`, the lower contour contribution differs from the leading
saddle term by at most `C * ‖dedekindLeadingSaddle K d q‖ * (log d) ^ (-1 / 10)`. -/
theorem exists_eventually_dedekind_lower_contribution_log :
    ∃ M c₀ C : ℝ, 0 < M ∧ 0 < c₀ ∧ c₀ ≤ Real.pi / 128 ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop, ∀ q ∈ dedekindCountingWindow K M c₀ d,
        ‖dedekindLowerContribution K d q - dedekindLeadingSaddle K d q‖ ≤
          C * ‖dedekindLeadingSaddle K d q‖ *
            Real.log (d : ℝ) ^ (-(1 / 10 : ℝ)) := by
  obtain ⟨M₀, c₀₀, C₀, hM₀, hc₀₀, hC₀, hlower⟩ :=
    exists_eventually_dedekind_lower_contribution K
  let M := max M₀ (dedekindOscillationM K)
  let c₀ := min c₀₀ (min (dedekindOscillationC0 K) (Real.pi / 128))
  have hM : 0 < M := hM₀.trans_le (le_max_left _ _)
  have hc₀ : 0 < c₀ := lt_min hc₀₀
    (lt_min (dedekindOscillationC0_pos K) (div_pos Real.pi_pos (by norm_num)))
  have hcSmall : c₀ ≤ Real.pi / 128 :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ce, hce, heff⟩ := eventually_effectiveN_countingWindow_log_lower
    K M c₀ hM hc₀ (hcSmall.trans (by linarith [Real.pi_lt_four]))
  let C : ℝ := C₀ * ce ^ (-(1 : ℝ) / 10) + C₀
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨M, c₀, C, hM, hc₀, hcSmall, hC, ?_⟩
  filter_upwards [hlower, heff, eventually_dedekind_remote_error K,
    tendsto_atTop.1 (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1,
    eventually_ge_atTop (1 : ℕ)] with
      d hlow heffd hrem (hlog : 1 ≤ Real.log (d : ℝ)) hd
  intro q hq
  have hn' : dedekindEffectiveN K d q ^ (-(1 : ℝ) / 10) ≤
      ce ^ (-(1 : ℝ) / 10) * Real.log (d : ℝ) ^ (-(1 : ℝ) / 10) := by
    rw [← Real.mul_rpow hce.le (by linarith)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (heffd q hq) (by norm_num)
  have hr := (hrem q (dedekindCountingWindow_subset K hd (le_max_right _ _)
    ((min_le_right _ _).trans (min_le_left _ _)) hq)).trans (one_div_cube_le_log_rpow hd hlog)
  have hsum :
      C₀ * dedekindEffectiveN K d q ^ (-(1 : ℝ) / 10) +
          C₀ * (d : ℝ) ^ (dedekindDegree K + 1) *
            Real.exp (-(d * (dedekindRemoteGapConst *
              min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹))) ≤
        C * Real.log (d : ℝ) ^ (-(1 : ℝ) / 10) := by
    simp only [C]
    linarith [mul_le_mul_of_nonneg_left hn' hC₀.le, mul_le_mul_of_nonneg_left hr hC₀.le]
  calc
    ‖dedekindLowerContribution K d q - dedekindLeadingSaddle K d q‖
        ≤ ‖dedekindLeadingSaddle K d q‖ *
          (C₀ * dedekindEffectiveN K d q ^ (-(1 : ℝ) / 10) +
            C₀ * (d : ℝ) ^ (dedekindDegree K + 1) *
              Real.exp (-(d * (dedekindRemoteGapConst *
                min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹)))) :=
      hlow q (dedekindCountingWindow_subset K hd (le_max_left _ _) (min_le_left _ _) hq)
    _ ≤ ‖dedekindLeadingSaddle K d q‖ *
          (C * Real.log (d : ℝ) ^ (-(1 : ℝ) / 10)) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = C * ‖dedekindLeadingSaddle K d q‖ *
          Real.log (d : ℝ) ^ (-(1 / 10 : ℝ)) := by ring_nf

/-- The rescaled Dedekind Jensen polynomials satisfy `DedekindOscillation K`: on the counting
window, their value at `-q` is twice the real part of the leading saddle term up to a relative
error `O((log d) ^ (-1 / 10))`. -/
theorem dedekind_oscillation : DedekindOscillation K := by
  obtain ⟨M, c₀, C, hM, hc₀, hcsmall, hC, hlow⟩ :=
    exists_eventually_dedekind_lower_contribution_log K
  exact dedekind_oscillation_of_lower_contribution K hM hc₀ hcsmall hlow

/-- There are `C > 0` and `D` such that for every `d ≥ D` the degree-`d` Dedekind Jensen
polynomial has at least `d - C * √(d log d)` distinct negative real roots. -/
theorem dedekind_prop_real_roots :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      (d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (dedekindNegativeRootCountK K d : ℝ) :=
  canonical_prop_real_roots K (dedekind_oscillation K)

/-- There are `C > 0` and `d₀ ≥ 2` such that for every `d ≥ d₀` the degree-`d` Dedekind Jensen
polynomial is nonzero and has at least `d - C * √(d log d)` distinct negative real roots. -/
theorem dedekind_thm_main :
    ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      dedekindJensenK K d ≠ 0 ∧
        (d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
          (dedekindNegativeRootCountK K d : ℝ) :=
  canonical_thm_main K (dedekind_oscillation K)

end

end RiemannJensen
