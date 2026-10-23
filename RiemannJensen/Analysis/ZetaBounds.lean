module

public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Elementary bounds for the Riemann zeta function

This file proves estimates for `riemannZeta σ` on the real half-line `σ > 1`, obtained from the
Dirichlet series and the integral test, and uniform bounds for `ζ`, `1 / ζ` and the logarithmic
derivative `ζ' / ζ` on the half-plane `re s ≥ 4`, obtained from absolutely convergent Dirichlet
series.

## Main definitions

* `zetaLogDerivMajorant`: The sum `∑ ‖Λ(n) / n ^ 4‖` of the norms of the terms of the von Mangoldt
  Dirichlet series at `4`.

## Main results

* `re_riemannZeta_le_div_sub_one`: For `σ > 1`, `ζ(σ) ≤ σ / (σ - 1)`.
* `norm_riemannZeta_le_four_thirds`: For `re s ≥ 4`, `‖ζ(s)‖ ≤ 4 / 3`.
* `three_fourths_le_norm_riemannZeta`: For `re s ≥ 4`, `3 / 4 ≤ ‖ζ(s)‖`.
* `norm_riemannZeta_logDeriv_le_majorant`: For `re s ≥ 4`,
  `‖ζ'(s) / ζ(s)‖ ≤ zetaLogDerivMajorant`.
-/

@[expose] public section

namespace RiemannJensen

open Real Complex Finset Nat
open ArithmeticFunction

/-- The Dirichlet series for `ζ` in its half-plane of absolute convergence. -/
theorem hasSum_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℂ) ^ s) (riemannZeta s) := by
  convert (summable_one_div_nat_cpow.mpr hs).hasSum
  exact zeta_eq_tsum_one_div_nat_cpow hs

/-- For real `σ > 1`, `∑ 1 / n ^ σ` sums to the real part of `ζ(σ)`. -/
theorem hasSum_re_riemannZeta {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ σ) (riemannZeta σ).re := by
  convert hasSum_re <| hasSum_riemannZeta (s := σ) (by simpa) with n
  rw [← ofReal_natCast, ← ofReal_cpow (by positivity), ← ofReal_one, ← ofReal_div, ofReal_re]

/-- The real zeta value as a real `tsum`. -/
theorem re_riemannZeta_eq_tsum_one_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta σ).re = ∑' n : ℕ, 1 / (n : ℝ) ^ σ :=
  (hasSum_re_riemannZeta hσ).tsum_eq.symm

/-- For real `σ > 1`, the real part of `ζ(σ)` exceeds `1`. -/
theorem one_lt_re_riemannZeta {σ : ℝ} (hσ : 1 < σ) : 1 < (riemannZeta σ).re := by
  have hrange : (1 : ℝ) < ∑ n ∈ range 3, 1 / (n : ℝ) ^ σ := by
    simpa [sum_range_succ, zero_rpow (by positivity : σ ≠ 0)] using
      lt_add_of_pos_right (1 : ℝ) (one_div_pos.mpr <| rpow_pos_of_pos two_pos σ)
  exact hrange.trans_le <| sum_le_hasSum _
    (fun _ _ ↦ one_div_nonneg.mpr <| rpow_nonneg (by positivity) _)
    (hasSum_re_riemannZeta hσ)

/-- For real `σ > 1`, the real part of `ζ(σ)` is at most `σ / (σ - 1)`. -/
theorem re_riemannZeta_le_div_sub_one {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta σ).re ≤ σ / (σ - 1) := by
  have hintegrable := integrableOn_Ioi_rpow_of_lt (neg_lt_neg hσ) one_pos
  have hcomp := AntitoneOn.tsum_comp_add_le_integral 1
    ((antitoneOn_rpow_Ioi_of_exponent_nonpos
      (neg_nonpos.mpr (by positivity))).mono (Set.Ici_subset_Ioi.mpr (by positivity)))
    (by norm_cast) fun _ _ ↦ rpow_nonneg (by grind) _
  rw [re_riemannZeta_eq_tsum_one_div_rpow hσ,
    ← Summable.sum_add_tsum_nat_add 2 (summable_one_div_nat_rpow.mpr hσ)]
  simp_rw [← inv_eq_one_div, ← rpow_neg (Nat.cast_nonneg _)]
  grw [hcomp, integral_Ioi_rpow_of_lt (by grind) (by positivity)]
  suffices 1 + -1 / (-σ + 1) = σ / (σ - 1) by
    simp [sum_range_succ, zero_rpow (by grind : -σ ≠ 0), this]
  grind

/-- For real `σ > 1`, `log ζ(σ) ≤ log σ - log (σ - 1)`. -/
theorem log_re_riemannZeta_le_log_sub_log_sub_one {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta σ).re.log ≤ σ.log - (σ - 1).log := by
  grw [re_riemannZeta_le_div_sub_one hσ,
    log_div (by positivity) (by positivity)]
  exact riemannZeta_re_pos_of_one_lt hσ

/-- For `1 < re s`, `‖ζ s‖ ≤ ζ(re s)`. -/
theorem norm_riemannZeta_le_re_riemannZeta_re {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ (riemannZeta s.re).re := by
  rw [← (hasSum_riemannZeta hs).tsum_eq]
  calc
    ‖∑' n : ℕ, 1 / (n : ℂ) ^ s‖ ≤ ∑' n : ℕ, ‖1 / (n : ℂ) ^ s‖ :=
      norm_tsum_le_tsum_norm (summable_one_div_nat_cpow.mpr hs).norm
    _ = ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := tsum_congr fun n ↦ by
      rw [norm_div, norm_one, ← ofReal_natCast,
        norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) (by linarith : s.re ≠ 0)]
    _ = (riemannZeta s.re).re :=
      (hasSum_re_riemannZeta hs).tsum_eq

/-- For `1 < re s`, the Möbius Dirichlet series satisfies `‖L(μ, s)‖ ≤ ζ(re s)`. -/
theorem norm_LSeries_moebius_le_re_riemannZeta_re {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (fun n : ℕ ↦ (moebius n : ℂ)) s‖ ≤
      (riemannZeta s.re).re := by
  apply (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).hasSum.norm_le_of_bounded
    (hasSum_re_riemannZeta hs)
  intro n
  rw [LSeries.term_def]
  split_ifs with hn
  · simp only [norm_zero]
    positivity
  · rw [norm_div, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos
      (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ) < n)]
    have hμ : ‖(moebius n : ℂ)‖ ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
    simpa only [one_div] using
      (div_le_div_of_nonneg_right hμ (Real.rpow_nonneg (by positivity) _))

/-- For `re s ≥ 4`, the real zeta value `ζ(re s)` is at most `4 / 3`. -/
theorem re_riemannZeta_re_le_four_thirds {s : ℂ} (hs : 4 ≤ s.re) :
    (riemannZeta s.re).re ≤ 4 / 3 :=
  (re_riemannZeta_le_div_sub_one (by linarith)).trans <|
    (div_le_iff₀ (by linarith : 0 < s.re - 1)).2 (by linarith)

/-- For `4 ≤ re s`, `‖ζ s‖ ≤ 4 / 3`. -/
theorem norm_riemannZeta_le_four_thirds {s : ℂ} (hs : 4 ≤ s.re) :
    ‖riemannZeta s‖ ≤ (4 : ℝ) / 3 :=
  (norm_riemannZeta_le_re_riemannZeta_re (by linarith)).trans
    (re_riemannZeta_re_le_four_thirds hs)

/-- For `4 ≤ re s`, `3 / 4 ≤ ‖ζ s‖`. -/
theorem three_fourths_le_norm_riemannZeta {s : ℂ} (hs : 4 ≤ s.re) :
    (3 : ℝ) / 4 ≤ ‖riemannZeta s‖ := by
  have hre : 1 < s.re := by linarith
  have hprod := LSeries_one_mul_Lseries_moebius hre
  rw [LSeries_one_eq_riemannZeta hre] at hprod
  have hμ : ‖LSeries (fun n : ℕ ↦ (moebius n : ℂ)) s‖ ≤
      (4 : ℝ) / 3 :=
    (norm_LSeries_moebius_le_re_riemannZeta_re hre).trans (re_riemannZeta_re_le_four_thirds hs)
  have hone : (1 : ℝ) = ‖riemannZeta s‖ *
      ‖LSeries (fun n : ℕ ↦ (moebius n : ℂ)) s‖ := by
    rw [← norm_mul, hprod, norm_one]
  nlinarith [norm_nonneg (riemannZeta s),
    norm_nonneg (LSeries (fun n : ℕ ↦ (moebius n : ℂ)) s)]

/-- The sum `∑ₙ ‖Λ(n) / n ^ 4‖` of the norms of the von Mangoldt Dirichlet series terms at `4`;
it bounds `‖ζ' / ζ‖` on `re s ≥ 4`. -/
noncomputable def zetaLogDerivMajorant : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun m : ℕ ↦ (vonMangoldt m : ℂ)) (4 : ℂ) n‖

/-- The majorant `zetaLogDerivMajorant` is nonnegative. -/
theorem zetaLogDerivMajorant_nonneg : 0 ≤ zetaLogDerivMajorant :=
  tsum_nonneg fun _ ↦ norm_nonneg _

/-- For `4 ≤ re s`, `‖ζ' s / ζ s‖ ≤ zetaLogDerivMajorant`. -/
theorem norm_riemannZeta_logDeriv_le_majorant {s : ℂ} (hs : 4 ≤ s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ zetaLogDerivMajorant := by
  have hbound :
      ‖LSeries (fun n : ℕ ↦ (vonMangoldt n : ℂ)) s‖ ≤
        zetaLogDerivMajorant :=
    tsum_of_norm_bounded
      (ArithmeticFunction.LSeriesSummable_vonMangoldt
        (by norm_num : (1 : ℝ) < (4 : ℂ).re)).norm.hasSum
      (LSeries.norm_term_le_of_re_le_re _ (by simpa using hs))
  rwa [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by linarith), neg_div,
    norm_neg] at hbound

/-- For `4 ≤ re s`, `ζ s ≠ 0`. -/
theorem riemannZeta_ne_zero_of_four_le_re {s : ℂ} (hs : 4 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by linarith)

end RiemannJensen
