module

public import RiemannJensen.Dedekind.ActionEffective

/-!
# Logarithmic lower bound for the effective Dedekind parameter

For fixed positive window parameters, the effective Gaussian parameter `dedekindEffectiveN` is
bounded below by a positive multiple of `log d` uniformly on the counting window, for all
sufficiently large `d`.

## Main results

* `eventually_effectiveN_countingWindow_log_lower`: there is `c > 0` such that eventually in `d`,
  `c * log d ≤ dedekindEffectiveN K d q` for every `q` in `dedekindCountingWindow K M c₀ d`.
-/

@[expose] public section

namespace RiemannJensen

open Set Filter
open scoped Topology

noncomputable section

/-- For `0 ≤ x ≤ 1`, `min M 1 * x` is at most `√(M * x)`. -/
theorem min_one_mul_le_sqrt_mul {M x : ℝ} (hM : 0 < M) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    min M 1 * x ≤ Real.sqrt (M * x) := by
  have hkM : min M 1 ^ 2 ≤ M := by
    rcases le_total M 1 with h | h
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right h]
      linarith
  rw [Real.le_sqrt (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hx1 hx0, mul_le_mul_of_nonneg_right hkM hx0,
    sq_nonneg (min M 1)]

/-- The edge term `a * d * δ * √δ` with `δ = dedekindEdgeOffset M d` dominates
`a * M * min M 1 * log d`. -/
theorem mul_log_le_dedekindEdgeOffset_mul_sqrt {a M : ℝ} (ha : 0 ≤ a) (hM : 0 < M)
    {d : ℕ} (hd : 1 < d) :
    a * M * min M 1 * Real.log d ≤
      a * d * dedekindEdgeOffset M d * Real.sqrt (dedekindEdgeOffset M d) := by
  have hdpos : (0 : ℝ) < d := by positivity
  have hx0 : 0 ≤ Real.log (d : ℝ) / d :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hd.le)) hdpos.le
  have hx1 : Real.log (d : ℝ) / d ≤ 1 :=
    (div_le_one hdpos).2 ((Real.log_le_sub_one_of_pos hdpos).trans (by linarith))
  set x := Real.sqrt (Real.log (d : ℝ) / d)
  have hlog : Real.log (d : ℝ) = d * x ^ 2 := by
    rw [Real.sq_sqrt hx0]
    field_simp
  calc
    a * M * min M 1 * Real.log d = a * d * (M * x) * (min M 1 * x) := by
      rw [hlog]
      ring
    _ ≤ a * d * (M * x) * Real.sqrt (M * x) :=
      mul_le_mul_of_nonneg_left
        (min_one_mul_le_sqrt_mul hM (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 hx1)) (by positivity)

variable (K : Type) [Field K] [NumberField K]

/-- For fixed positive window parameters, the effective Gaussian parameter is
uniformly bounded below by a positive multiple of `log d` on the counting
window, for all sufficiently large degrees. -/
theorem eventually_effectiveN_countingWindow_log_lower
    (M c₀ : ℝ) (hM : 0 < M) (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ d : ℕ in atTop, ∀ q ∈ dedekindCountingWindow K M c₀ d,
        c * Real.log d ≤ dedekindEffectiveN K d q := by
  set cEdge : ℝ := (dedekindLocalEpsilon ^ 2 / 96) * M * min M 1
  set cTail : ℝ := (dedekindLocalEpsilon ^ 2 / 3000) *
    (dedekindDegree K : ℝ) / (4 * Real.pi * c₀) with hcTail_def
  have hε : 0 < dedekindLocalEpsilon := by norm_num [dedekindLocalEpsilon]
  have hN : (0 : ℝ) < dedekindDegree K := by exact_mod_cast dedekindDegree_pos K
  have hcTail : 0 < cTail := by positivity
  refine ⟨min cEdge cTail, lt_min (by positivity) hcTail, ?_⟩
  obtain ⟨DΛ, hDΛ⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  obtain ⟨DF, -, hDF⟩ :=
    eventually_const_le_dedekindScaleLambda K (4 * (1 + Real.log (dedekindScaleA K)))
  obtain ⟨DL, hDL⟩ := eventually_log_le_dedekindScaleLambda K
  filter_upwards [eventually_ge_atTop DΛ, eventually_ge_atTop DF,
    eventually_ge_atTop DL, eventually_ge_atTop (2 : ℕ)] with d hdΛ hdF hdL hd2 q hq
  have hd1 : 1 ≤ d := by omega
  have hlogpos : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast hd2)
  have htailEq : (dedekindLocalEpsilon ^ 2 / 3000) * d / dedekindUpperEndpoint K c₀ d =
      cTail * dedekindScaleLambda K d := by
    rw [hcTail_def, dedekindUpperEndpoint]
    field_simp [(dedekindScaleT_pos K d hd1).ne', hc₀.ne']
    nlinarith [dedekindScale_product K d hd1]
  refine (le_min ?_ ?_).trans
    (dedekind_effective_window K M c₀ hM hc₀ hc₀one d hd2 (hDΛ d hdΛ) (hDF d hdF) hq)
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hlogpos.le).trans
      (mul_log_le_dedekindEdgeOffset_mul_sqrt (by positivity) hM hd2)
  · rw [htailEq]
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hlogpos.le).trans
      (mul_le_mul_of_nonneg_left (hDL d hdL) hcTail.le)

end

end RiemannJensen
