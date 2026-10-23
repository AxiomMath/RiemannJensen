module

public import RiemannJensen.Dedekind.GammaSector

/-!
# A logarithm of the Dedekind Gamma remainder on the large sector

Far enough out in the closed sector, the Gamma remainder lies in the disk of
radius `1 / 2` about one.  The principal complex logarithm therefore gives a
single consistent branch there.  This file records its exponential identity
and its uniform `O_K(‖w‖⁻¹)` bound.
-/

@[expose] public section

namespace RiemannJensen

open Complex

noncomputable section

/-- The principal logarithm of the combined Dedekind archimedean remainder. On the large
sector the remainder lies within `1 / 2` of one, so this is a consistent branch of `log` there. -/
def dedekindGammaLog (K : Type) [Field K] [NumberField K] (w : ℂ) : ℂ :=
  Complex.log (dedekindGammaRemainder K w)

/-- There is `W > 0` such that for `‖w‖ ≥ W` with `|arg w| ≤ 2π/3`, the Gamma remainder
equals `exp (dedekindGammaLog K w)`. -/
theorem dedekindGammaRemainder_eq_exp_log (K : Type) [Field K] [NumberField K] :
    ∃ W : ℝ, 0 < W ∧
      ∀ w : ℂ, |Complex.arg w| ≤ 2 * Real.pi / 3 → W ≤ ‖w‖ →
        dedekindGammaRemainder K w = Complex.exp (dedekindGammaLog K w) := by
  obtain ⟨W, hW, hnear⟩ := GammaSector.dedekindGammaRemainder_near_one K
  exact ⟨W, hW, fun w hwarg hwnorm => (Complex.exp_log (hnear w hwarg hwnorm).2).symm⟩

/-- There are `C, W > 0` such that `‖dedekindGammaLog K w‖ ≤ C / ‖w‖` whenever
`|arg w| ≤ 2π/3` and `‖w‖ ≥ W`. -/
theorem norm_dedekindGammaLog_le (K : Type) [Field K] [NumberField K] :
    ∃ C W : ℝ, 0 < C ∧ 0 < W ∧
      ∀ w : ℂ, |Complex.arg w| ≤ 2 * Real.pi / 3 → W ≤ ‖w‖ →
        ‖dedekindGammaLog K w‖ ≤ C / ‖w‖ := by
  obtain ⟨C₀, W₀, hC₀, hW₀, hrem⟩ := GammaSector.dedekindGammaRemainder_tends_one K
  refine ⟨3 / 2 * C₀, max W₀ (2 * C₀), by positivity, hW₀.trans_le (le_max_left _ _),
    fun w hwarg hwnorm => ?_⟩
  have hW₀w : W₀ ≤ ‖w‖ := (le_max_left _ _).trans hwnorm
  have hn : 0 < ‖w‖ := hW₀.trans_le hW₀w
  have hremw := hrem w hwarg hW₀w
  have hhalf : ‖dedekindGammaRemainder K w - 1‖ ≤ 1 / 2 := by
    refine hremw.trans ?_
    rw [div_le_iff₀ hn]
    linarith [(le_max_right W₀ (2 * C₀)).trans hwnorm]
  calc
    ‖dedekindGammaLog K w‖ ≤ 3 / 2 * ‖dedekindGammaRemainder K w - 1‖ := by
      simpa [dedekindGammaLog] using norm_log_one_add_half_le_self hhalf
    _ ≤ 3 / 2 * (C₀ / ‖w‖) := by gcongr
    _ = 3 / 2 * C₀ / ‖w‖ := by ring

end

end RiemannJensen
