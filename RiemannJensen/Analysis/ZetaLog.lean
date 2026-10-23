module

public import RiemannJensen.Analysis.ZetaBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# A bounded principal logarithm of zeta in the far right half-plane

On the closed half-plane `re s ≥ 4`, the Riemann zeta function lies within distance `1/3` of one,
so its principal logarithm is continuous, exponentiates back to zeta, and has norm at most `1/2`.

## Main results

* `norm_riemannZeta_sub_one_le_one_third`: `‖ζ(s) - 1‖ ≤ 1/3` for `re s ≥ 4`.
* `re_riemannZeta_pos_of_four_le_re`: `ζ(s)` has positive real part for `re s ≥ 4`.
* `exp_log_riemannZeta_of_four_le`: `exp (log ζ(s)) = ζ(s)` for `re s ≥ 4`.
* `norm_log_riemannZeta_le_half`: `‖log ζ(s)‖ ≤ 1/2` for `re s ≥ 4`.
* `continuousOn_log_riemannZeta`: `log ζ` is continuous on `re s ≥ 4`.
-/

@[expose] public section

namespace RiemannJensen

open Real Complex Finset

/-- In `re s ≥ 4`, zeta lies in the closed disk of radius `1/3` about one. -/
theorem norm_riemannZeta_sub_one_le_one_third {s : ℂ} (hs : 4 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ (1 : ℝ) / 3 := by
  have hre : 1 < s.re := by linarith
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hsum := summable_one_div_nat_cpow.mpr hre
  have hzsum := hasSum_riemannZeta hre
  have htail : riemannZeta s - 1 = ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℂ) ^ s := by
    rw [← hzsum.tsum_eq, ← hsum.sum_add_tsum_nat_add 2]
    simp [sum_range_succ, zero_cpow hs0]
  rw [htail]
  calc
    ‖∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℂ) ^ s‖
        ≤ ∑' n : ℕ, ‖1 / ((n + 2 : ℕ) : ℂ) ^ s‖ :=
      norm_tsum_le_tsum_norm (hsum.comp_injective (fun _ _ h => by omega)).norm
    _ = ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ s.re := by
      apply tsum_congr
      intro n
      rw [norm_div, norm_one]
      change 1 / ‖(((n + 2 : ℕ) : ℝ) : ℂ) ^ s‖ =
        1 / ((n + 2 : ℕ) : ℝ) ^ s.re
      push_cast
      rw [show ((n : ℂ) + 2) = (((n : ℝ) + 2 : ℝ) : ℂ) by norm_num]
      rw [norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < n + 2)]
    _ = (riemannZeta s.re).re - 1 := by
      have hrsum := summable_one_div_nat_rpow.mpr hre
      rw [re_riemannZeta_eq_tsum_one_div_rpow hre,
        ← hrsum.sum_add_tsum_nat_add 2]
      simp [sum_range_succ, zero_rpow (by linarith : s.re ≠ 0)]
    _ ≤ s.re / (s.re - 1) - 1 := by
      linarith [re_riemannZeta_le_div_sub_one hre]
    _ ≤ 1 / 3 := by
      rw [div_sub_one (by linarith : s.re - 1 ≠ 0)]
      apply (div_le_iff₀ (by linarith : 0 < s.re - 1)).2
      nlinarith

/-- Zeta has positive real part throughout `re s ≥ 4`. -/
theorem re_riemannZeta_pos_of_four_le_re {s : ℂ} (hs : 4 ≤ s.re) :
    0 < (riemannZeta s).re := by
  have hnorm := norm_riemannZeta_sub_one_le_one_third hs
  have hre := abs_re_le_norm (riemannZeta s - 1)
  rw [sub_re, one_re] at hre
  have hlower := neg_le_of_abs_le hre
  linarith

/-- The principal zeta logarithm exponentiates back to zeta on the far right
half-plane. -/
theorem exp_log_riemannZeta_of_four_le {s : ℂ} (hs : 4 ≤ s.re) :
    Complex.exp (Complex.log (riemannZeta s)) = riemannZeta s :=
  Complex.exp_log (riemannZeta_ne_zero_of_four_le_re hs)

/-- The principal logarithm of zeta is bounded by `1/2` on `re s ≥ 4`. -/
theorem norm_log_riemannZeta_le_half {s : ℂ} (hs : 4 ≤ s.re) :
    ‖Complex.log (riemannZeta s)‖ ≤ (1 : ℝ) / 2 := by
  have hsmall := norm_riemannZeta_sub_one_le_one_third hs
  have hhalf : ‖riemannZeta s - 1‖ ≤ (1 : ℝ) / 2 := by linarith
  have hlog := Complex.norm_log_one_add_half_le_self hhalf
  rw [show 1 + (riemannZeta s - 1) = riemannZeta s by ring] at hlog
  linarith

/-- The principal logarithm of zeta is continuous on the closed half-plane
`re s ≥ 4`. -/
theorem continuousOn_log_riemannZeta :
    ContinuousOn (fun s : ℂ => Complex.log (riemannZeta s)) {s | 4 ≤ s.re} := by
  apply ContinuousOn.clog
  · intro s hs
    exact (differentiableAt_riemannZeta (by
      intro h
      subst s
      norm_num at hs)).continuousAt.continuousWithinAt
  · intro s hs
    exact Or.inl (re_riemannZeta_pos_of_four_le_re hs)

end RiemannJensen
