module

public import RiemannJensen.MainTheorem.Uniformize
public import RiemannJensen.Analysis.XiThetaMoments
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical losses from the counting window

Elementary bounds from the exact scale identity: the upper-window loss
`d / sqrt (c₀ * scaleT d) = O(sqrt (d log d))` and the edge-displacement loss
`d τ sqrt τ = O(sqrt (d log d))`. Eventual oscillation and phase-span hypotheses
then give the additive root loss `d ≤ negativeJensenRootCount d + loss d`, and
from it the main counting theorem conditionally.
-/

@[expose] public section

namespace RiemannJensen

/-- From degree three onward, the logarithm of the degree is at least one. -/
theorem one_le_log_nat {d : ℕ} (hd : 3 ≤ d) : (1 : ℝ) ≤ Real.log (d : ℝ) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith [Real.log_le_log (by norm_num) hdR, Real.log_three_gt_d9]

/-- For `d ≥ 1`, `d * sqrt (log d / d) = sqrt (d * log d)`. -/
theorem nat_mul_sqrt_log_div_nat {d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) * Real.sqrt (Real.log (d : ℝ) / d) =
      Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [show (d : ℝ) * Real.log d = d ^ 2 * (Real.log d / d) by field_simp,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hdR.le]

/-- Fixed upper-window parameter loss:
`d / sqrt (c₀ * scaleT d) = O(sqrt (d log d))` for every fixed `c₀ > 0`. -/
theorem exists_upper_window_loss_bound {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d →
      (d : ℝ) / Real.sqrt (c₀ * scaleT d) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
  refine ⟨1 / Real.sqrt (2 * Real.pi * c₀), by positivity, fun d hd => ?_⟩
  have hd1 : 1 ≤ d := by omega
  have hT : 0 < scaleT d := lt_trans (by positivity) (scaleT_gt_base d hd1)
  have hΛ := scaleLambda_pos d hd1
  have hlog := one_le_log_nat hd
  have hΛupper : scaleLambda d ≤ 2 * Real.log (d : ℝ) := by
    simpa [max_eq_right hlog] using scaleLambda_le_two_mul_max_log d hd1
  have hprod := scaleT_mul_scaleLambda d hd1
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, Real.sq_sqrt (by positivity), mul_pow, one_div, inv_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp
  nlinarith [Real.pi_pos]

/-- The edge displacement `τ = M sqrt(log d / d)` costs at most
`M sqrt(d log d)` after multiplication by `d sqrt τ`, provided `0 ≤ τ ≤ 1`. -/
theorem edge_window_loss_bound {d : ℕ} (hd : 1 ≤ d) {M τ : ℝ}
    (hτ : τ = M * Real.sqrt (Real.log (d : ℝ) / d)) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (d : ℝ) * τ * Real.sqrt τ ≤ M * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
  calc
    (d : ℝ) * τ * Real.sqrt τ ≤ (d : ℝ) * τ * 1 :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_one.2 hτ1) (by positivity)
    _ = M * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
      rw [← nat_mul_sqrt_log_div_nat hd, hτ]
      ring

/-- Big-O packaging of `edge_window_loss_bound` for a fixed nonnegative `M`.
The threshold condition `τ ≤ 1` remains explicit. -/
theorem exists_edge_window_loss_bound {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ τ : ℝ,
      τ = M * Real.sqrt (Real.log (d : ℝ) / d) → 0 ≤ τ → τ ≤ 1 →
      (d : ℝ) * τ * Real.sqrt τ ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
  refine ⟨M + 1, by linarith, fun d hd τ hτ hτ0 hτ1 => ?_⟩
  nlinarith [edge_window_loss_bound hd hτ hτ0 hτ1,
    Real.sqrt_nonneg ((d : ℝ) * Real.log (d : ℝ))]

/-- Explicit oscillation and phase-span hypotheses on an eventual family of
positive windows give `d ≤ negativeJensenRootCount d + loss d` for all `d ≥ D`. -/
theorem eventual_nat_loss_of_phaseSpan {D : ℕ} (hD : 1 ≤ D) (loss : ℕ → ℕ)
    (a b : ℕ → ℝ) (R E θ : ℕ → ℝ → ℝ)
    (ha : ∀ d : ℕ, D ≤ d → 0 < a d)
    (hab : ∀ d : ℕ, D ≤ d → a d ≤ b d)
    (hPcont : ∀ d : ℕ, D ≤ d →
      ContinuousOn (fun q => (rescaledJensen d).eval (-q)) (Set.Icc (a d) (b d)))
    (hθcont : ∀ d : ℕ, D ≤ d → ContinuousOn (θ d) (Set.Icc (a d) (b d)))
    (hR : ∀ d : ℕ, D ≤ d → ∀ q ∈ Set.Icc (a d) (b d), 0 < R d q)
    (hE : ∀ d : ℕ, D ≤ d → ∀ q ∈ Set.Icc (a d) (b d), |E d q| < 1 / 2)
    (hformula : ∀ d : ℕ, D ≤ d → ∀ q ∈ Set.Icc (a d) (b d),
      (rescaledJensen d).eval (-q) =
        2 * R d q * (Real.cos (θ d q) + E d q))
    (hspan : ∀ d : ℕ, D ≤ d →
      (((d - loss d) + 1 : ℕ) : ℝ) * Real.pi ≤ θ d (b d) - θ d (a d)) :
    ∀ d : ℕ, D ≤ d → d ≤ negativeJensenRootCount d + loss d := by
  intro d hd
  have := le_negativeJensenRootCount_of_phaseSpan d (hD.trans hd) (gammaCoeff_pos d).ne'
    (R d) (E d) (θ d) (a d) (b d) (ha d hd) (hab d hd)
    (hPcont d hd) (hθcont d hd) (hR d hd) (hE d hd) (hformula d hd) (hspan d hd)
  omega

/-- The main counting theorem, conditional on explicit eventual oscillation and
phase-span hypotheses whose natural loss is `O(sqrt (d log d))`. -/
theorem riemannJensen_main_of_eventual_phaseSpan_nat_loss
    {D : ℕ} (hD : 2 ≤ D) (loss : ℕ → ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (a b : ℕ → ℝ) (R E θ : ℕ → ℝ → ℝ)
    (ha : ∀ d : ℕ, D ≤ d → 0 < a d)
    (hab : ∀ d : ℕ, D ≤ d → a d ≤ b d)
    (hPcont : ∀ d : ℕ, D ≤ d →
      ContinuousOn (fun q => (rescaledJensen d).eval (-q)) (Set.Icc (a d) (b d)))
    (hθcont : ∀ d : ℕ, D ≤ d → ContinuousOn (θ d) (Set.Icc (a d) (b d)))
    (hR : ∀ d : ℕ, D ≤ d → ∀ q ∈ Set.Icc (a d) (b d), 0 < R d q)
    (hE : ∀ d : ℕ, D ≤ d → ∀ q ∈ Set.Icc (a d) (b d), |E d q| < 1 / 2)
    (hformula : ∀ d : ℕ, D ≤ d → ∀ q ∈ Set.Icc (a d) (b d),
      (rescaledJensen d).eval (-q) =
        2 * R d q * (Real.cos (θ d q) + E d q))
    (hspan : ∀ d : ℕ, D ≤ d →
      (((d - loss d) + 1 : ℕ) : ℝ) * Real.pi ≤ θ d (b d) - θ d (a d))
    (hloss : ∀ d : ℕ, D ≤ d →
      (loss d : ℝ) ≤ C₀ * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ((nonrealJensenRootCount d : ℝ) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) ∧
      ((d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ)) :=
  riemannJensen_main_of_eventual_nat_loss (fun d _ => gammaCoeff_pos d) loss hC₀
    (eventual_nat_loss_of_phaseSpan (by omega) loss a b R E θ ha hab hPcont hθcont hR hE
      hformula hspan)
    hloss

end RiemannJensen
