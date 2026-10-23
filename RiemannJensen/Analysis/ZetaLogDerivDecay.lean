module

public import RiemannJensen.Analysis.ZetaBounds

/-!
# Exponential decay of the logarithmic derivative of zeta

On `re s ≥ 4` the logarithmic derivative `ζ'/ζ` decays like `2^{-re s}`.  This
follows from the von Mangoldt Dirichlet series, since `Λ(1) = 0` and
`n^{-σ} ≤ 2^{4-σ} n^{-4}` for `n ≥ 2`.
-/

@[expose] public section

namespace RiemannJensen

open Complex ArithmeticFunction

/-- Termwise comparison of the von Mangoldt series at `s` with the series at `4`. -/
theorem norm_term_vonMangoldt_le_decay {s : ℂ} (hs : 4 ≤ s.re) (n : ℕ) :
    ‖LSeries.term (fun m : ℕ ↦ (vonMangoldt m : ℂ)) s n‖ ≤
      (2 : ℝ) ^ (4 - s.re) *
        ‖LSeries.term (fun m : ℕ ↦ (vonMangoldt m : ℂ)) (4 : ℂ) n‖ := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp [LSeries.term]
  · rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right (by omega),
      ite_eq_right (by omega), show ((4 : ℂ)).re = 4 by norm_num,
      show (2 : ℝ) ^ (4 - s.re) = ((2 : ℝ) ^ (s.re - 4))⁻¹ by
        rw [← Real.rpow_neg (by norm_num), neg_sub], inv_mul_eq_div, div_div]
    refine div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) ?_
    calc (n : ℝ) ^ (4 : ℝ) * (2 : ℝ) ^ (s.re - 4)
        ≤ (n : ℝ) ^ (4 : ℝ) * (n : ℝ) ^ (s.re - 4) := by
          gcongr
          exact_mod_cast hn
      _ = (n : ℝ) ^ s.re := by
          rw [← Real.rpow_add (by positivity)]
          ring_nf

/-- Exponential decay of `ζ'/ζ` on `re s ≥ 4`. -/
theorem norm_zetaLogDeriv_le_decay {s : ℂ} (hs : 4 ≤ s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤
      (2 : ℝ) ^ (4 - s.re) * zetaLogDerivMajorant := by
  rw [← norm_neg, ← neg_div, ← LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by linarith)]
  exact tsum_of_norm_bounded
    ((LSeriesSummable_vonMangoldt (by norm_num : (1 : ℝ) < (4 : ℂ).re)).norm.hasSum.mul_left _)
    (norm_term_vonMangoldt_le_decay hs)

/-- `σ · 2^{4-σ} ≤ 4` for `σ ≥ 4`. -/
theorem mul_two_rpow_four_sub_le {σ : ℝ} (hσ : 4 ≤ σ) :
    σ * (2 : ℝ) ^ (4 - σ) ≤ 4 := by
  have hexp : 1 + (σ - 4) / 4 ≤ (2 : ℝ) ^ (σ - 4) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    nlinarith [Real.log_two_gt_d9, Real.add_one_le_exp (Real.log 2 * (σ - 4))]
  have h2 : (2 : ℝ) ^ (4 - σ) = ((2 : ℝ) ^ (σ - 4))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num), neg_sub]
  rw [h2, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  linarith

/-- If `x ≤ K · re(1/2 + w)` and `re(1/2 + w) ≥ 4`, then `x · ‖ζ'/ζ(1/2+w)‖` is
bounded by an absolute multiple of `K`. -/
theorem mul_norm_zetaLogDeriv_le {K x : ℝ} {w : ℂ} (hK : 0 ≤ K)
    (hw : 4 ≤ (1 / 2 + w).re) (hx : x ≤ K * (1 / 2 + w).re) :
    x * ‖deriv riemannZeta (1 / 2 + w) / riemannZeta (1 / 2 + w)‖ ≤
      4 * K * zetaLogDerivMajorant :=
  calc x * ‖deriv riemannZeta (1 / 2 + w) / riemannZeta (1 / 2 + w)‖
      ≤ (K * (1 / 2 + w).re) * ((2 : ℝ) ^ (4 - (1 / 2 + w).re) * zetaLogDerivMajorant) :=
        mul_le_mul hx (norm_zetaLogDeriv_le_decay hw) (norm_nonneg _)
          (mul_nonneg hK (by linarith))
    _ = K * zetaLogDerivMajorant * ((1 / 2 + w).re * (2 : ℝ) ^ (4 - (1 / 2 + w).re)) := by
        ring
    _ ≤ K * zetaLogDerivMajorant * 4 :=
        mul_le_mul_of_nonneg_left (mul_two_rpow_four_sub_le hw)
          (mul_nonneg hK zetaLogDerivMajorant_nonneg)
    _ = 4 * K * zetaLogDerivMajorant := by ring

end RiemannJensen
