module

public import RiemannJensen.Dedekind.ZetaStripBounds
public import RiemannJensen.Dedekind.ContinuedZeta

/-!
# Polynomial bounds for the Dedekind zeta function on vertical strips

Let `K` be a number field of degree `N` over `ℚ`, and let `f` be holomorphic on `ℂ ∖ {1}` and equal
to the Dedekind zeta function of `K` on `Re s > 1`. Then for some `C > 0`, `‖f s‖ ≤ C (1 + ‖s‖)^N`
on the line `Re s = -1/2`, `‖f s‖ ≤ C` on the line `Re s = 3/2`, and `‖f s‖ ≤ C ‖s‖^N` whenever
`‖s‖ ≥ 2` and either `-1/2 ≤ Re s ≤ 3/2` or `Re s ≥ 1/2`. These bounds hold in particular for the
continuation `analyticDedekindZeta K`.

## Main results

* `zeta_left_boundary_of_continuation`: `‖f s‖ ≤ C (1 + ‖s‖)^N` on `Re s = -1/2`.
* `zeta_right_boundary_of_continuation`: `f` is bounded on `Re s = 3/2`.
* `zeta_strip_of_continuation`: `‖f s‖ ≤ C ‖s‖^N` on `-1/2 ≤ Re s ≤ 3/2`, `‖s‖ ≥ 2`.
* `zeta_global_of_continuation`: `‖f s‖ ≤ C ‖s‖^N` on `Re s ≥ 1/2`, `‖s‖ ≥ 2`.
* `dedekind_zeta_left_boundary`, `dedekind_zeta_right_boundary`, `dedekind_zeta_strip`,
  `dedekind_zeta_global`: the same bounds for `analyticDedekindZeta K`.
-/

@[expose] public section

namespace RiemannJensen

noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {f : ℂ → ℂ}

/-- A holomorphic function on `ℂ ∖ {1}` agreeing with the Dedekind zeta function of `K` on
`Re s > 1` satisfies `‖f s‖ ≤ C (1 + ‖s‖)^N` on the line `Re s = -1/2`, for some `C > 0`, where
`N = [K : ℚ]`. -/
theorem zeta_left_boundary_of_continuation (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hfζ : ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = -1 / 2 → ‖f s‖ ≤ C * (1 + ‖s‖) ^ Module.finrank ℚ K := by
  obtain ⟨C, hC⟩ := AntRHScratch.left_line (K := K) hf hfζ
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun s hs => ?_⟩
  calc
    ‖f s‖ ≤ C * (1 + |s.im|) ^ Module.finrank ℚ K := hC s hs
    _ ≤ max C 1 * (1 + ‖s‖) ^ Module.finrank ℚ K :=
      mul_le_mul (le_max_left _ _)
        (pow_le_pow_left₀ (by positivity) (by linarith [Complex.abs_im_le_norm s]) _)
        (by positivity) (zero_le_one.trans (le_max_right _ _))

/-- A function agreeing with the Dedekind zeta function of `K` on `Re s > 1` is bounded by some
`C > 0` on the line `Re s = 3/2`. -/
theorem zeta_right_boundary_of_continuation
    (hfζ : ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = 3 / 2 → ‖f s‖ ≤ C := by
  obtain ⟨C, hC⟩ := AntRHScratch.right_line (K := K) hfζ
  exact ⟨max C 1, lt_max_of_lt_right one_pos, fun s hs => (hC s hs).trans (le_max_left _ _)⟩

/-- A bound `C (1 + |Im s|)^N` implies a bound `C' ‖s‖^N` on `‖s‖ ≥ 2`, for some `C' > 0`. -/
theorem exists_mul_one_add_abs_im_pow_le_mul_norm_pow (C : ℝ) (N : ℕ) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ s : ℂ, 2 ≤ ‖s‖ → C * (1 + |s.im|) ^ N ≤ C' * ‖s‖ ^ N := by
  refine ⟨max C 0 * 2 ^ N + 1, by positivity, fun s hs => ?_⟩
  calc
    C * (1 + |s.im|) ^ N ≤ max C 0 * (2 * ‖s‖) ^ N :=
      mul_le_mul (le_max_left _ _)
        (pow_le_pow_left₀ (by positivity) (by linarith [Complex.abs_im_le_norm s]) _)
        (by positivity) (le_max_right _ _)
    _ = max C 0 * 2 ^ N * ‖s‖ ^ N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

/-- A holomorphic function on `ℂ ∖ {1}` agreeing with the Dedekind zeta function of `K` on
`Re s > 1` satisfies `‖f s‖ ≤ C ‖s‖^N` for `-1/2 ≤ Re s ≤ 3/2` and `‖s‖ ≥ 2`, for some `C > 0`,
where `N = [K : ℚ]`. -/
theorem zeta_strip_of_continuation (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hfζ : ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 2 ≤ ‖s‖ →
      ‖f s‖ ≤ C * ‖s‖ ^ Module.finrank ℚ K := by
  obtain ⟨C, hC⟩ := AntRHScratch.strip (K := K) hf hfζ
  obtain ⟨C', hC', h⟩ := exists_mul_one_add_abs_im_pow_le_mul_norm_pow C (Module.finrank ℚ K)
  exact ⟨C', hC', fun s hs₁ hs₂ hsn => (hC s hs₁ hs₂ hsn).trans (h s hsn)⟩

/-- A holomorphic function on `ℂ ∖ {1}` agreeing with the Dedekind zeta function of `K` on
`Re s > 1` satisfies `‖f s‖ ≤ C ‖s‖^N` for `Re s ≥ 1/2` and `‖s‖ ≥ 2`, for some `C > 0`, where
`N = [K : ℚ]`. -/
theorem zeta_global_of_continuation (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hfζ : ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ ‖s‖ → ‖f s‖ ≤ C * ‖s‖ ^ Module.finrank ℚ K := by
  obtain ⟨C, hC⟩ := AntRHScratch.global (K := K) hf hfζ
  obtain ⟨C', hC', h⟩ := exists_mul_one_add_abs_im_pow_le_mul_norm_pow C (Module.finrank ℚ K)
  exact ⟨C', hC', fun s hs hsn => (hC s hs hsn).trans (h s hsn)⟩

/-- The continued Dedekind zeta function satisfies `‖ζ_K(s)‖ ≤ C (1 + ‖s‖)^N` on the line
`Re s = -1/2`, for some `C > 0`. -/
theorem dedekind_zeta_left_boundary :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = -1 / 2 →
      ‖analyticDedekindZeta K s‖ ≤ C * (1 + ‖s‖) ^ dedekindDegree K := by
  simpa [dedekindDegree] using zeta_left_boundary_of_continuation K
    (analyticDedekindZeta_holomorphic K) (analyticDedekindZeta_eq_raw K)

/-- The continued Dedekind zeta function is bounded on the line `Re s = 3/2`. -/
theorem dedekind_zeta_right_boundary :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = 3 / 2 →
      ‖analyticDedekindZeta K s‖ ≤ C :=
  zeta_right_boundary_of_continuation K (analyticDedekindZeta_eq_raw K)

/-- The continued Dedekind zeta function satisfies `‖ζ_K(s)‖ ≤ C ‖s‖^N` for `-1/2 ≤ Re s ≤ 3/2`
and `‖s‖ ≥ 2`, for some `C > 0`. -/
theorem dedekind_zeta_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 2 ≤ ‖s‖ →
      ‖analyticDedekindZeta K s‖ ≤ C * ‖s‖ ^ dedekindDegree K := by
  simpa [dedekindDegree] using zeta_strip_of_continuation K
    (analyticDedekindZeta_holomorphic K) (analyticDedekindZeta_eq_raw K)

/-- The continued Dedekind zeta function satisfies `‖ζ_K(s)‖ ≤ C ‖s‖^N` for `Re s ≥ 1/2` and
`‖s‖ ≥ 2`, for some `C > 0`. -/
theorem dedekind_zeta_global :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ ‖s‖ →
      ‖analyticDedekindZeta K s‖ ≤ C * ‖s‖ ^ dedekindDegree K := by
  simpa [dedekindDegree] using zeta_global_of_continuation K
    (analyticDedekindZeta_holomorphic K) (analyticDedekindZeta_eq_raw K)

end

end RiemannJensen
