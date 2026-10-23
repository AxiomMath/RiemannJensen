module

public import RiemannJensen.Analysis.SaddleDefinitions
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The radial saddle equation

This file isolates the elementary one-dimensional fact behind the radial
saddle parameter.  The analytic equation is written in the normal form
`A / r + B - log r = 0`.  When `A ≥ 0`, it is continuous and strictly
decreasing on the positive half-line, so any sign-changing bracket contains
a unique root.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- Normal form of the radial saddle equation. -/
noncomputable def radialEquation (A B r : ℝ) : ℝ :=
  A / r + B - Real.log r

/-- The radial equation is continuous away from the origin. -/
theorem continuousOn_radialEquation (A B : ℝ) :
    ContinuousOn (radialEquation A B) (Set.Ioi 0) := fun _ hr =>
  (((continuousAt_const.div continuousAt_id hr.ne').add continuousAt_const).sub
    (Real.continuousAt_log hr.ne')).continuousWithinAt

/-- For a nonnegative reciprocal coefficient, the radial equation is strictly
 decreasing on the positive half-line. -/
theorem radialEquation_strictAntiOn {A B : ℝ} (hA : 0 ≤ A) :
    StrictAntiOn (radialEquation A B) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hinv : A / y ≤ A / x := div_le_div_of_nonneg_left hA hx hxy.le
  have hlog : Real.log x < Real.log y := Real.strictMonoOn_log hx hy hxy
  unfold radialEquation
  linarith

/-- A sign-changing positive bracket contains a radial root. -/
theorem exists_radialEquation_eq_zero_of_bracket {A B a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hleft : 0 ≤ radialEquation A B a)
    (hright : radialEquation A B b ≤ 0) :
    ∃ r ∈ Set.Icc a b, radialEquation A B r = 0 :=
  intermediate_value_Icc' hab
    ((continuousOn_radialEquation A B).mono fun _ hr => ha.trans_le hr.1) ⟨hright, hleft⟩

/-- A nonnegative reciprocal coefficient makes a radial root unique. -/
theorem radialEquation_eq_zero_unique {A B x y : ℝ} (hA : 0 ≤ A)
    (hx : 0 < x) (hy : 0 < y)
    (hex : radialEquation A B x = 0)
    (hey : radialEquation A B y = 0) : x = y :=
  (radialEquation_strictAntiOn hA).injOn hx hy (hex.trans hey.symm)

/-- A sign-changing bracket contains exactly one positive radial root. -/
theorem existsUnique_radialEquation_of_bracket {A B a b : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b)
    (hleft : 0 ≤ radialEquation A B a)
    (hright : radialEquation A B b ≤ 0) :
    ∃! r : ℝ, 0 < r ∧ radialEquation A B r = 0 := by
  obtain ⟨r, hr, her⟩ := exists_radialEquation_eq_zero_of_bracket ha hab hleft hright
  exact ⟨r, ⟨ha.trans_le hr.1, her⟩, fun y hy =>
    radialEquation_eq_zero_unique hA hy.1 (ha.trans_le hr.1) hy.2 her⟩

/-- An explicit point near zero lies on the nonnegative side of the radial
equation.  This is a quantitative substitute for the limit at `0⁺`. -/
theorem radialEquation_exp_neg_abs_nonneg {A B : ℝ} (hA : 0 ≤ A) :
    0 ≤ radialEquation A B (Real.exp (-(|B| + 1))) := by
  rw [radialEquation, Real.log_exp]
  have hdiv : 0 ≤ A / Real.exp (-(|B| + 1)) :=
    div_nonneg hA (Real.exp_pos _).le
  nlinarith [neg_le_abs B]

/-- An explicit large point lies on the nonpositive side of the radial
equation.  This is a quantitative substitute for the limit at `+∞`. -/
theorem radialEquation_exp_add_abs_nonpos {A B : ℝ} (hA : 0 ≤ A) :
    radialEquation A B (Real.exp (A + |B| + 1)) ≤ 0 := by
  rw [radialEquation, Real.log_exp]
  have hb1 : 1 ≤ Real.exp (A + |B| + 1) :=
    Real.one_le_exp (by nlinarith [abs_nonneg B])
  have hdiv : A / Real.exp (A + |B| + 1) ≤ A := div_le_self hA hb1
  nlinarith [le_abs_self B]

/-- The radial equation always has a unique positive root when its reciprocal
coefficient is nonnegative. -/
theorem existsUnique_radialEquation {A B : ℝ} (hA : 0 ≤ A) :
    ∃! r : ℝ, 0 < r ∧ radialEquation A B r = 0 :=
  existsUnique_radialEquation_of_bracket hA (Real.exp_pos _)
    (Real.exp_monotone (by linarith [abs_nonneg B]))
    (radialEquation_exp_neg_abs_nonneg hA) (radialEquation_exp_add_abs_nonpos hA)

/-- Increasing either coefficient can only move the unique positive root to
the right. -/
theorem radialEquation_root_mono {A₁ A₂ B₁ B₂ r₁ r₂ : ℝ}
    (hA₂ : 0 ≤ A₂) (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (heq₁ : radialEquation A₁ B₁ r₁ = 0)
    (heq₂ : radialEquation A₂ B₂ r₂ = 0) :
    r₁ ≤ r₂ := by
  by_contra hle
  have hdiv : A₁ / r₁ ≤ A₂ / r₁ := div_le_div_of_nonneg_right hA hr₁.le
  have hanti := radialEquation_strictAntiOn (B := B₂) hA₂ hr₂ hr₁ (not_le.1 hle)
  unfold radialEquation at *
  linarith

/-- The coefficient of `1 / r` occurring in the paper's radial equation. -/
noncomputable def saddleRadialCoeff (d : ℕ) (α : ℝ) : ℝ :=
  scaleLambda d * Real.cos α / (Real.pi / 2)

/-- The constant term occurring in the paper's radial equation. -/
noncomputable def saddleRadialConst (d : ℕ) (α : ℝ) : ℝ :=
  alphaCot α - scaleLambda d / 2 - 1

/-- The inequality in the infimum definition of `saddleRadius` is precisely
nonpositivity of the normal-form radial equation. -/
theorem saddleRadius_set_eq (d : ℕ) (α : ℝ) :
    {r : ℝ | 0 < r ∧
      scaleLambda d * Real.cos α / ((Real.pi / 2) * r) + alphaCot α ≤
        scaleLambda d / 2 + 1 + Real.log r} =
    {r : ℝ | 0 < r ∧ radialEquation (saddleRadialCoeff d α)
      (saddleRadialConst d α) r ≤ 0} := by
  ext r
  simp only [Set.mem_ofPred_eq, radialEquation, saddleRadialCoeff, saddleRadialConst, div_div]
  constructor <;> rintro ⟨hr, h⟩ <;> exact ⟨hr, by linarith⟩

/-- On the saddle-angle range the reciprocal coefficient is nonnegative. -/
theorem saddleRadialCoeff_nonneg (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ saddleRadialCoeff d α :=
  div_nonneg (mul_nonneg (scaleLambda_pos d hd).le (Real.cos_nonneg_of_mem_Icc hα))
    (by positivity)

/-- The paper's radial equation has a unique positive solution throughout the
closed saddle-angle range. -/
theorem existsUnique_saddleRadial (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ∃! r : ℝ, 0 < r ∧ radialEquation (saddleRadialCoeff d α)
      (saddleRadialConst d α) r = 0 :=
  existsUnique_radialEquation (saddleRadialCoeff_nonneg d hd hα)

/-- Any positive solution of the radial equation agrees with the infimum
chosen in `saddleRadius`. -/
theorem saddleRadius_eq_of_radialEquation (d : ℕ) {α r : ℝ}
    (hcoeff : 0 ≤ saddleRadialCoeff d α) (hr : 0 < r)
    (heq : radialEquation (saddleRadialCoeff d α)
      (saddleRadialConst d α) r = 0) :
    saddleRadius d α = r := by
  rw [saddleRadius, saddleRadius_set_eq]
  have hset :
      {x : ℝ | 0 < x ∧ radialEquation (saddleRadialCoeff d α)
        (saddleRadialConst d α) x ≤ 0} = Set.Ici r := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    refine ⟨fun ⟨hx, hxeq⟩ => not_lt.1 fun hxr => ?_, fun hrx => ⟨hr.trans_le hrx, ?_⟩⟩
    · linarith [radialEquation_strictAntiOn (B := saddleRadialConst d α) hcoeff hx hr hxr]
    · exact heq ▸ (radialEquation_strictAntiOn hcoeff).antitoneOn hr (hr.trans_le hrx) hrx
  rw [hset, csInf_Ici]

/-- Consequently `saddleRadius` is the unique positive radial solution on the
saddle-angle range. -/
theorem saddleRadius_pos_and_eq (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    0 < saddleRadius d α ∧
      radialEquation (saddleRadialCoeff d α) (saddleRadialConst d α)
        (saddleRadius d α) = 0 := by
  obtain ⟨r, hr, -⟩ := existsUnique_saddleRadial d hd hα
  rwa [saddleRadius_eq_of_radialEquation d (saddleRadialCoeff_nonneg d hd hα) hr.1 hr.2]

/-- The infimum-defined radius satisfies the paper's original radial equality,
not merely its defining inequality. -/
theorem saddleRadius_characterization (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    scaleLambda d * Real.cos α /
        ((Real.pi / 2) * saddleRadius d α) + alphaCot α =
      scaleLambda d / 2 + 1 + Real.log (saddleRadius d α) := by
  have heq := (saddleRadius_pos_and_eq d hd hα).2
  rw [radialEquation, saddleRadialCoeff, saddleRadialConst, div_div] at heq
  linarith

/-- If both radial coefficients at `α` are at most those at `β`, then the saddle radius at
`α` is at most that at `β`. -/
theorem saddleRadius_le_of_coeff_le (d : ℕ) (hd : 1 ≤ d) {α β : ℝ}
    (hα : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hβ : β ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hcoeff : saddleRadialCoeff d α ≤ saddleRadialCoeff d β)
    (hconst : saddleRadialConst d α ≤ saddleRadialConst d β) :
    saddleRadius d α ≤ saddleRadius d β := by
  have hαeq := saddleRadius_pos_and_eq d hd hα
  have hβeq := saddleRadius_pos_and_eq d hd hβ
  exact radialEquation_root_mono (saddleRadialCoeff_nonneg d hd hβ)
    hcoeff hconst hαeq.1 hβeq.1 hαeq.2 hβeq.2

end RiemannJensen
