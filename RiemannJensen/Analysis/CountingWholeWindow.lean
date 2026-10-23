module

public import RiemannJensen.Analysis.CountingFixedWidth
public import RiemannJensen.Analysis.EdgeQuadratic

/-!
# The whole counting window

On the scale window the saddle angle `α` satisfies the edge comparison
`q - q_edge ≤ 6 α²` whenever `α < 1/2`. Consequently the fixed-width lower-contour estimate and
oscillatory formula hold on the whole counting window under the single hypothesis
`1 ≤ n_{1/1000}`.

## Main results

* `edge_comparison_on_scale_window`: `q - q_edge ≤ 6 α²` for `α < 1/2` on the scale window.
* `exists_countingWindow_lowerContribution_estimate_fixedWidth`: the fixed-width
  lower-contour estimate on the whole counting window.
* `exists_countingWindow_rescaledJensen_eval_fixedWidth`: the fixed-width oscillatory formula
  on the whole counting window.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- On the scale window, if the saddle angle `α` satisfies `α < 1/2`, then
`q - edgeQ d ≤ 6 α²`. -/
theorem edge_comparison_on_scale_window (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d) {q : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d))
    (hα : saddleAngle d q < 1 / 2) : q - edgeQ d ≤ 6 * saddleAngle d q ^ 2 := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, -, hinv⟩
  have h := saddleQ_sub_edge_upper d hd hΛ (α := saddleAngle d q) ⟨hα0.le, hα.le⟩
  rwa [hinv] at h

/-- **Fixed-width lower-contour estimate on the whole counting window.** For `d ≥ 2` and `q`
in the counting window with `1 ≤ n_{1/1000}`, the lower contribution differs from the leading
saddle term by at most the stated relative error. -/
theorem exists_countingWindow_lowerContribution_estimate_fixedWidth :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {M c₀ q : ℝ},
      2 ≤ d → 24 * Real.pi ≤ scaleLambda d →
      0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
      40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d →
      1 ≤ effectiveN (1 / 1000) d q →
      ‖lowerContribution d q - leadingSaddle d q‖ ≤
        ‖leadingSaddle d q‖ *
          (windowRelConst (1 / 2) (max (4 + 8 * 2 * zetaLogDerivMajorant) (3 / 2)) *
              effectiveN (1 / 1000) d q ^ (-(1 : ℝ) / 10) +
            Real.pi * C * Real.sqrt (2 * Real.pi * 4) * d *
              Real.exp (-(d * ((1 / 1000 : ℝ) ^ 2 * remoteGapConst 6 *
                min ((q - edgeQ d) ^ 2) q⁻¹)))) := by
  obtain ⟨C, hC, hest⟩ := exists_countingWindow_lowerContribution_estimate_of_edge_fixedWidth
  refine ⟨C, hC, ?_⟩
  intro d M c₀ q hd hΛ hM hc₀ hcsmall hscale hq hn
  obtain ⟨hsc, -⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  exact hest hd hΛ hM hc₀ hcsmall hscale hq (by norm_num)
    (edge_comparison_on_scale_window d (hd.trans' (by norm_num)) hΛ hsc) hn

/-- **Fixed-width oscillatory formula on the whole counting window.** For `d ≥ 2` with
`gammaCoeff d ≠ 0` and `q` in the counting window with `1 ≤ n_{1/1000}`, the value of the
rescaled Jensen polynomial at `-q` differs from `2 Re` of the leading saddle term by at most the
stated relative error. -/
theorem exists_countingWindow_rescaledJensen_eval_fixedWidth :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {M c₀ q : ℝ},
      2 ≤ d → gammaCoeff d ≠ 0 → 24 * Real.pi ≤ scaleLambda d →
      0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
      40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d →
      1 ≤ effectiveN (1 / 1000) d q →
      |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| ≤
        2 * ‖leadingSaddle d q‖ *
          (windowRelConst (1 / 2) (max (4 + 8 * 2 * zetaLogDerivMajorant) (3 / 2)) *
              effectiveN (1 / 1000) d q ^ (-(1 : ℝ) / 10) +
            Real.pi * C * Real.sqrt (2 * Real.pi * 4) * d *
              Real.exp (-(d * ((1 / 1000 : ℝ) ^ 2 * remoteGapConst 6 *
                min ((q - edgeQ d) ^ 2) q⁻¹)))) := by
  obtain ⟨C, hC, hest⟩ := exists_countingWindow_rescaledJensen_eval_of_edge_fixedWidth
  refine ⟨C, hC, ?_⟩
  intro d M c₀ q hd hγ hΛ hM hc₀ hcsmall hscale hq hn
  obtain ⟨hsc, -⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  exact hest hd hγ hΛ hM hc₀ hcsmall hscale hq (by norm_num)
    (edge_comparison_on_scale_window d (hd.trans' (by norm_num)) hΛ hsc) hn

end RiemannJensen
