module

public import RiemannJensen.Xi
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# The degree-dependent gamma scale

This file defines the degree-dependent scale `scaleT d` as an infimum of a set of reals determined
by the level function `scaleLevel`, rather than through a Lambert-W function. For positive degrees
the infimum is the unique point at which `scaleLevel` takes the value `d`.
-/

@[expose] public section

namespace RiemannJensen

open Polynomial

/-- The real level function whose positive inverse defines the gamma scale. -/
noncomputable def scaleLevel (t : ℝ) : ℝ :=
  (t / (2 * Real.pi)) * (Real.log (t / (2 * Real.pi)) - 1)

/-- The degree-dependent gamma scale: the infimum of all `t > 2πe` with `d ≤ scaleLevel t`. -/
noncomputable def scaleT (d : ℕ) : ℝ :=
  sInf {t : ℝ | 2 * Real.pi * Real.exp 1 < t ∧ (d : ℝ) ≤ scaleLevel t}

/-- Twice the logarithmic coordinate of `scaleT`. -/
noncomputable def scaleLambda (d : ℕ) : ℝ :=
  2 * (Real.log (scaleT d / (2 * Real.pi)) - 1)

/-- The reciprocal Jensen polynomial.  Once `J_d` has degree `d`, this is
exactly `X^d J_d(X⁻¹)`. -/
noncomputable def reciprocalJensen (d : ℕ) : ℝ[X] :=
  (jensenPolynomial d).reverse

/-- The reciprocal Jensen polynomial in the saddle-point normalization. -/
noncomputable def rescaledJensen (d : ℕ) : ℝ[X] :=
  C (((scaleT d) ^ 2 / (d : ℝ)) ^ d) *
    (reciprocalJensen d).comp (C ((d : ℝ) / (scaleT d) ^ 2) * X)

/-- The simpler logarithmic-coordinate form of the scale level. -/
noncomputable def scaleAux (x : ℝ) : ℝ := Real.exp (x + 1) * x

private theorem scaleAux_zero : scaleAux 0 = 0 := by
  simp [scaleAux]

private theorem continuous_scaleAux : Continuous scaleAux := by
  unfold scaleAux
  fun_prop

private theorem strictMonoOn_scaleAux : StrictMonoOn scaleAux (Set.Ici 0) := by
  intro x hx y hy hxy
  calc
    scaleAux x = x * Real.exp (x + 1) := by simp [scaleAux, mul_comm]
    _ < y * Real.exp (x + 1) :=
      mul_lt_mul_of_pos_right hxy (Real.exp_pos _)
    _ ≤ y * Real.exp (y + 1) :=
      mul_le_mul_of_nonneg_left (Real.exp_monotone (by linarith)) hy
    _ = scaleAux y := by simp [scaleAux, mul_comm]

private theorem natCast_le_scaleAux_natCast (d : ℕ) : (d : ℝ) ≤ scaleAux d := by
  have hexp : (1 : ℝ) ≤ Real.exp ((d : ℝ) + 1) := Real.one_le_exp (by positivity)
  rw [scaleAux]
  nlinarith

private theorem scaleLevel_two_pi_mul_exp (x : ℝ) :
    scaleLevel (2 * Real.pi * Real.exp (x + 1)) = scaleAux x := by
  rw [scaleLevel, show (2 * Real.pi * Real.exp (x + 1)) / (2 * Real.pi) =
      Real.exp (x + 1) by field_simp, Real.log_exp]
  simp [scaleAux]

private theorem log_coordinate_pos {t : ℝ} (ht : 2 * Real.pi * Real.exp 1 < t) :
    0 < Real.log (t / (2 * Real.pi)) - 1 := by
  have hratio : Real.exp 1 < t / (2 * Real.pi) :=
    (lt_div_iff₀ (by positivity)).2 (by linarith)
  have hlog : (1 : ℝ) < Real.log (t / (2 * Real.pi)) :=
    (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos 1) hratio)).2 hratio
  linarith

private theorem exp_log_coordinate {t : ℝ} (ht : 2 * Real.pi * Real.exp 1 < t) :
    2 * Real.pi * Real.exp ((Real.log (t / (2 * Real.pi)) - 1) + 1) = t := by
  have htpos : 0 < t := lt_trans (by positivity) ht
  rw [sub_add_cancel, Real.exp_log (by positivity)]
  field_simp

private theorem scaleLevel_eq_scaleAux_log {t : ℝ} (ht : 2 * Real.pi * Real.exp 1 < t) :
    scaleLevel t = scaleAux (Real.log (t / (2 * Real.pi)) - 1) := by
  conv_lhs => rw [← exp_log_coordinate ht]
  rw [scaleLevel_two_pi_mul_exp]

/-- For every positive degree there is a unique positive logarithmic
coordinate solving the scale equation. -/
theorem existsUnique_scale_coordinate (d : ℕ) (hd : 1 ≤ d) :
    ∃! x : ℝ, 0 < x ∧ scaleAux x = d := by
  obtain ⟨x, hx, heq⟩ : ∃ x ∈ Set.Icc 0 (d : ℝ), scaleAux x = d :=
    intermediate_value_Icc (Nat.cast_nonneg d) continuous_scaleAux.continuousOn
      ⟨by simp [scaleAux_zero], natCast_le_scaleAux_natCast d⟩
  have hxpos : 0 < x := hx.1.lt_of_ne <| by
    rintro rfl
    have : d = 0 := by simpa [scaleAux_zero] using heq.symm
    omega
  exact ⟨x, ⟨hxpos, heq⟩, fun y hy => (strictMonoOn_scaleAux.injOn (Set.mem_Ici.2 hxpos.le)
    (Set.mem_Ici.2 hy.1.le) (heq.trans hy.2.symm)).symm⟩

/-- The scale-defining set has an actual least element for positive degrees,
and the level at that least element is exactly `d`. -/
theorem exists_isLeast_scaleSet (d : ℕ) (hd : 1 ≤ d) :
    ∃ t : ℝ, IsLeast
      {u : ℝ | 2 * Real.pi * Real.exp 1 < u ∧ (d : ℝ) ≤ scaleLevel u} t ∧
      scaleLevel t = d := by
  obtain ⟨x, hx, -⟩ := existsUnique_scale_coordinate d hd
  have htlevel := (scaleLevel_two_pi_mul_exp x).trans hx.2
  refine ⟨_, ⟨⟨mul_lt_mul_of_pos_left (Real.exp_strictMono (by linarith [hx.1])) (by positivity),
    htlevel.ge⟩, fun u hu => ?_⟩, htlevel⟩
  have hu' := hu.2
  rw [scaleLevel_eq_scaleAux_log hu.1, ← hx.2] at hu'
  have hxy : x ≤ Real.log (u / (2 * Real.pi)) - 1 :=
    (strictMonoOn_scaleAux.le_iff_le (Set.mem_Ici.2 hx.1.le)
      (Set.mem_Ici.2 (log_coordinate_pos hu.1).le)).mp hu'
  rw [← exp_log_coordinate hu.1]
  exact mul_le_mul_of_nonneg_left (Real.exp_monotone (by linarith)) (by positivity)

/-- For `1 ≤ d`, `scaleT d` lies strictly above `2πe` and solves `scaleLevel (scaleT d) = d`. -/
theorem scaleT_mem_and_level (d : ℕ) (hd : 1 ≤ d) :
    2 * Real.pi * Real.exp 1 < scaleT d ∧ scaleLevel (scaleT d) = d := by
  obtain ⟨t, ht, htlevel⟩ := exists_isLeast_scaleSet d hd
  rw [show scaleT d = t from ht.csInf_eq]
  exact ⟨ht.1.1, htlevel⟩

/-- Exact defining equation for the gamma scale. -/
theorem scaleT_level (d : ℕ) (hd : 1 ≤ d) :
    scaleLevel (scaleT d) = d :=
  (scaleT_mem_and_level d hd).2

/-- The gamma scale is strictly beyond its lower endpoint. -/
theorem scaleT_gt_base (d : ℕ) (hd : 1 ≤ d) :
    2 * Real.pi * Real.exp 1 < scaleT d :=
  (scaleT_mem_and_level d hd).1

/-- The gamma scale is positive for positive degree. -/
theorem scaleT_pos (d : ℕ) (hd : 1 ≤ d) : 0 < scaleT d :=
  lt_trans (by positivity) (scaleT_gt_base d hd)

/-- The logarithmic scale is positive for positive degree. -/
theorem scaleLambda_pos (d : ℕ) (hd : 1 ≤ d) : 0 < scaleLambda d := by
  rw [scaleLambda]
  exact mul_pos (by norm_num) (log_coordinate_pos (scaleT_gt_base d hd))

/-- The logarithmic coordinate is exactly half of `scaleLambda`. -/
theorem scaleLambda_div_two (d : ℕ) :
    scaleLambda d / 2 = Real.log (scaleT d / (2 * Real.pi)) - 1 := by
  rw [scaleLambda]
  ring

/-- The logarithmic coordinate satisfies its elementary exponential equation. -/
theorem scaleAux_scaleLambda (d : ℕ) (hd : 1 ≤ d) :
    scaleAux (scaleLambda d / 2) = d := by
  rw [scaleLambda_div_two, ← scaleLevel_eq_scaleAux_log (scaleT_gt_base d hd)]
  exact scaleT_level d hd

/-- Lower logarithmic comparison for the scale. -/
theorem log_nat_sub_one_le_scaleLambda (d : ℕ) (hd : 1 ≤ d) :
    Real.log d - 1 ≤ scaleLambda d := by
  set x := scaleLambda d / 2 with hx
  have hbound : (d : ℝ) ≤ Real.exp (2 * x + 1) := by
    rw [← scaleAux_scaleLambda d hd, ← hx, scaleAux]
    calc
      Real.exp (x + 1) * x ≤ Real.exp (x + 1) * Real.exp x :=
        mul_le_mul_of_nonneg_left (le_trans (by linarith) (Real.add_one_le_exp x))
          (Real.exp_nonneg _)
      _ = Real.exp (2 * x + 1) := by
        rw [← Real.exp_add]
        ring_nf
  have hlog : Real.log d ≤ 2 * x + 1 :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.2 hd)).2 hbound
  linarith

/-- Upper logarithmic comparison for the scale: `Λ_d ≤ 2 max 1 (log d)`. Together with
`log_nat_sub_one_le_scaleLambda` this gives `Λ_d ≍ log d`. -/
theorem scaleLambda_le_two_mul_max_log (d : ℕ) (hd : 1 ≤ d) :
    scaleLambda d ≤ 2 * max 1 (Real.log d) := by
  set x := scaleLambda d / 2 with hx
  have hxd : scaleAux x = d := scaleAux_scaleLambda d hd
  have hxle : x ≤ max 1 (Real.log d) := by
    rcases le_or_gt x 1 with hxone | hone
    · exact hxone.trans (le_max_left _ _)
    have hexp : Real.exp x < scaleAux x := by
      rw [scaleAux]
      calc
        Real.exp x < Real.exp (x + 1) := Real.exp_strictMono (by linarith)
        _ < Real.exp (x + 1) * x :=
          (lt_mul_iff_one_lt_right (Real.exp_pos _)).2 hone
    exact ((Real.lt_log_iff_exp_lt (Nat.cast_pos.2 hd)).2 (by simpa [hxd] using hexp)).le.trans
      (le_max_right _ _)
  linarith [hx]

/-- The exact product identity `T_d Λ_d = 4πd`. -/
theorem scaleT_mul_scaleLambda (d : ℕ) (hd : 1 ≤ d) :
    scaleT d * scaleLambda d = 4 * Real.pi * d := by
  have hlevel := scaleT_level d hd
  rw [scaleLevel] at hlevel
  rw [scaleLambda]
  field_simp at hlevel ⊢
  nlinarith [Real.pi_pos]

/-- Exponential reconstruction of the scale from its logarithmic coordinate. -/
theorem scaleT_eq_exp_scaleLambda (d : ℕ) (hd : 1 ≤ d) :
    scaleT d = 2 * Real.pi * Real.exp (scaleLambda d / 2 + 1) := by
  have hpos : 0 < scaleT d / (2 * Real.pi) := div_pos (scaleT_pos d hd) (by positivity)
  rw [scaleLambda, show 2 * (Real.log (scaleT d / (2 * Real.pi)) - 1) / 2 + 1 =
    Real.log (scaleT d / (2 * Real.pi)) by ring, Real.exp_log hpos]
  field_simp

/-- Any `t > 2πe` with `scaleLevel t = d` equals `scaleT d`. -/
theorem scaleT_unique (d : ℕ) (hd : 1 ≤ d) {t : ℝ}
    (ht : 2 * Real.pi * Real.exp 1 < t) (heq : scaleLevel t = d) :
    t = scaleT d := by
  have hT := scaleT_gt_base d hd
  have hxy := strictMonoOn_scaleAux.injOn (Set.mem_Ici.2 (log_coordinate_pos ht).le)
    (Set.mem_Ici.2 (log_coordinate_pos hT).le) (by
      rw [← scaleLevel_eq_scaleAux_log ht, ← scaleLevel_eq_scaleAux_log hT, heq,
        scaleT_level d hd])
  rw [← exp_log_coordinate ht, ← exp_log_coordinate hT, hxy]

/-- Evaluation of the rescaled reciprocal polynomial. -/
theorem eval_rescaledJensen (d : ℕ) (x : ℝ) :
    (rescaledJensen d).eval x =
      (((scaleT d) ^ 2 / (d : ℝ)) ^ d) *
        (reciprocalJensen d).eval (((d : ℝ) / (scaleT d) ^ 2) * x) := by
  simp [rescaledJensen]

/-- Roots of `rescaledJensen d` correspond to roots of `reciprocalJensen d` under
`x ↦ (d / T_d²) x`. -/
theorem eval_rescaledJensen_eq_zero_iff (d : ℕ) (hd : 1 ≤ d) (x : ℝ) :
    (rescaledJensen d).eval x = 0 ↔
      (reciprocalJensen d).eval (((d : ℝ) / (scaleT d) ^ 2) * x) = 0 := by
  rw [eval_rescaledJensen]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero d
    (div_ne_zero (pow_ne_zero 2 (scaleT_pos d hd).ne') hd0)))

/-- For `0 < q`, if `J_d` has degree `d`, then `-q` is a zero of `rescaledJensen d` iff
`-T_d² / (d q)` is a zero of `jensenPolynomial d`. -/
theorem rescaledJensen_neg_zero_iff (d : ℕ) (hd : 1 ≤ d)
    (hdeg : (jensenPolynomial d).natDegree = d) {q : ℝ} (hq : 0 < q) :
    (rescaledJensen d).eval (-q) = 0 ↔
      (jensenPolynomial d).eval (-(scaleT d) ^ 2 / ((d : ℝ) * q)) = 0 := by
  rw [eval_rescaledJensen_eq_zero_iff d hd, reciprocalJensen, Polynomial.reverse, hdeg]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hT0 : scaleT d ≠ 0 := (scaleT_pos d hd).ne'
  let x : ℝ := -((scaleT d) ^ 2 / ((d : ℝ) * q))
  let : Invertible x := invertibleOfNonzero
    (neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 hT0) (mul_ne_zero hd0 hq.ne')))
  have hinvOf : ⅟ x = ((d : ℝ) / (scaleT d) ^ 2) * (-q) := by
    rw [invOf_eq_inv]
    dsimp [x]
    field_simp
  simpa only [Polynomial.eval₂_id, hinvOf, x, neg_div] using
    Polynomial.eval₂_reflect_eq_zero_iff (RingHom.id ℝ) x d (jensenPolynomial d) (by rw [hdeg])

end RiemannJensen
