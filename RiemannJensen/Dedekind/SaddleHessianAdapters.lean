module

public import RiemannJensen.Dedekind.SaddleGeometryLemmas
public import RiemannJensen.Analysis.HessianNormBounds
public import RiemannJensen.Analysis.CircleGapIntegration
public import RiemannJensen.Analysis.EdgeQuadratic

/-!
# Saddle bounds, circle gap and Hessian bounds at an abstract scale `Λ`

The uniform saddle bounds, the edge separation, the circle gap and the Hessian bounds, stated
for an arbitrary logarithmic scale `Λ` through `saddleRadiusAtLambda`, `saddleQAtLambda`,
`edgeQAtLambda` and `saddlePhaseAtLambda`, with every lower bound on `Λ` an explicit
hypothesis, and specialized to the Dedekind scale `dedekindScaleLambda K d`.

The saddle branch is parametrized by its angle `α`: the level is `saddleQAtLambda Λ α` and the
saddle point is `saddlePointAtLambda Λ α`.

## Main definitions

* `saddlePointAtLambda`: the lower saddle point of angle `α` at scale `Λ`.
* `saddleHessianAtLambda`: the Hessian `u² h''(u)` at that saddle point.
* `explicitSaddleHessianAtLambda`: the explicit value of `u² h''(u)` at `u = r² e^{-2iα}`.

## Main results

* `saddleRadiusAtLambda_le_two`: the radius is at most `2`.
* `saddleRadiusAtLambda_level_comparison`: `1 / √q ≤ r ≤ √2 / √q`.
* `saddleCosAtLambda_radius_comparison`: `π r / 16 ≤ cos α ≤ π r / 2`.
* `saddleQAtLambda_sub_edge_lower`, `saddleQAtLambda_sub_edge_upper`: the level is
  quadratically separated from the edge level.
* `saddlePhaseAtLambda_circle_quadratic_gap`: the quadratic gap on the saddle circle.
* `saddleHessianAtLambda_eq_explicit`: the explicit Hessian formula.
* `saddleHessianAtLambda_re_bounds`, `saddleHessianAtLambda_norm_bounds`: bounds on the
  Hessian.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Filter
open scoped Topology

/-! ### The radius at scale `Λ` as a root of the radial equation -/

/-- For `r > 0`, the radial function at scale `Λ` is the normal-form radial equation with
coefficients `Λ cos α / κ` and `cot α - Λ / 2 - 1`. -/
theorem saddleRadialAtLambda_eq_radialEquation (Λ α r : ℝ) (hr : 0 < r) :
    saddleRadialAtLambda Λ α r =
      radialEquation (Λ * Real.cos α / saddleKappa) (alphaCot α - Λ / 2 - 1) r := by
  rw [saddleRadialAtLambda, radialEquation]
  field_simp [hr.ne']
  ring

/-- For `Λ ≥ 0` and `|α| ≤ π/2`, the coefficient `Λ cos α / κ` is nonnegative. -/
theorem saddleRadialCoeffAtLambda_nonneg {Λ α : ℝ} (hΛ : 0 ≤ Λ)
    (hα : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ Λ * Real.cos α / saddleKappa :=
  div_nonneg (mul_nonneg hΛ (Real.cos_nonneg_of_mem_Icc hα))
    (by rw [saddleKappa_eq]; positivity)

/-- For `Λ ≥ 0` and `|α| ≤ π/2`, the radius at scale `Λ` is positive and is a zero of the
radial function. -/
theorem saddleRadiusAtLambda_pos_and_saddleRadialAtLambda_eq_zero {Λ α : ℝ} (hΛ : 0 ≤ Λ)
    (hα : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    0 < saddleRadiusAtLambda Λ α ∧
      saddleRadialAtLambda Λ α (saddleRadiusAtLambda Λ α) = 0 := by
  let A := Λ * Real.cos α / saddleKappa
  let B := alphaCot α - Λ / 2 - 1
  have hA : 0 ≤ A := saddleRadialCoeffAtLambda_nonneg hΛ hα
  rcases existsUnique_radialEquation hA with ⟨r, hr, _⟩
  have heq : saddleRadialAtLambda Λ α r = 0 :=
    (saddleRadialAtLambda_eq_radialEquation Λ α r hr.1).trans hr.2
  have hset : {x : ℝ | 0 < x ∧ saddleRadialAtLambda Λ α x ≤ 0} = Set.Ici r := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    constructor
    · rintro ⟨hx, hxeq⟩
      by_contra! hxr
      have hanti := radialEquation_strictAntiOn (B := B) hA hx hr.1 hxr
      rw [saddleRadialAtLambda_eq_radialEquation Λ α x hx] at hxeq
      linarith [hr.2]
    · intro hrx
      have hx : 0 < x := lt_of_lt_of_le hr.1 hrx
      refine ⟨hx, ?_⟩
      rcases hrx.eq_or_lt with h | h
      · simpa [h] using heq.le
      · rw [saddleRadialAtLambda_eq_radialEquation Λ α x hx]
        exact (radialEquation_strictAntiOn (B := B) hA hr.1 hx h).le.trans_eq hr.2
  rw [saddleRadiusAtLambda, hset, csInf_Ici]
  exact ⟨hr.1, heq⟩

/-- The radius `r` at scale `Λ` satisfies `Λ cos α / (κ r) + cot α = Λ / 2 + 1 + log r`. -/
theorem saddleRadiusAtLambda_characterization {Λ α : ℝ} (hΛ : 0 ≤ Λ)
    (hα : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    Λ * Real.cos α / (saddleKappa * saddleRadiusAtLambda Λ α) + alphaCot α =
      Λ / 2 + 1 + Real.log (saddleRadiusAtLambda Λ α) := by
  have h := (saddleRadiusAtLambda_pos_and_saddleRadialAtLambda_eq_zero hΛ hα).2
  rw [saddleRadialAtLambda] at h
  linarith

/-! ### Elementary facts about the radius and level at scale `Λ` -/

section Basic

/-- `2 κ / Λ = π / Λ`. -/
theorem two_mul_saddleKappa_div (Λ : ℝ) : 2 * saddleKappa / Λ = Real.pi / Λ := by
  simp only [saddleKappa_eq]
  ring

/-- The level at scale `Λ` is `q = r⁻² + (π / Λ) (α / sin α) r⁻¹`. -/
theorem saddleQAtLambda_eq (Λ α : ℝ) :
    saddleQAtLambda Λ α =
      (saddleRadiusAtLambda Λ α)⁻¹ ^ 2 +
        (Real.pi / Λ) * sinRatio α * (saddleRadiusAtLambda Λ α)⁻¹ := by
  rw [saddleQAtLambda, two_mul_saddleKappa_div]

/-- An angle in `[0, π/2]` lies in `[-π/2, π/2]`. -/
theorem mem_Icc_neg_pi_div_two_of_mem_Icc_zero {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩

/-- For `Λ ≥ 0` and `α ∈ [0, π/2]`, the radius at scale `Λ` is positive. -/
theorem saddleRadiusAtLambda_pos {Λ α : ℝ} (hΛ : 0 ≤ Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) : 0 < saddleRadiusAtLambda Λ α :=
  (saddleRadiusAtLambda_pos_and_saddleRadialAtLambda_eq_zero hΛ
    (mem_Icc_neg_pi_div_two_of_mem_Icc_zero hα)).1

/-- The radius at scale `Λ` is a root of the normal-form radial equation. -/
theorem saddleRadiusAtLambda_radialEquation {Λ α : ℝ} (hΛ : 0 ≤ Λ)
    (hα : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    radialEquation (Λ * Real.cos α / saddleKappa) (alphaCot α - Λ / 2 - 1)
      (saddleRadiusAtLambda Λ α) = 0 := by
  obtain ⟨hr, h0⟩ := saddleRadiusAtLambda_pos_and_saddleRadialAtLambda_eq_zero hΛ hα
  exact (saddleRadialAtLambda_eq_radialEquation Λ α _ hr).symm.trans h0

/-- The saddle radius at scale `Λ` strictly decreases with the angle. -/
theorem saddleRadiusAtLambda_strictAntiOn {Λ : ℝ} (hΛ : 0 < Λ) :
    StrictAntiOn (saddleRadiusAtLambda Λ) (Set.Icc 0 (Real.pi / 2)) := by
  intro α hα β hβ hαβ
  have hαfull := mem_Icc_neg_pi_div_two_of_mem_Icc_zero hα
  have hβfull := mem_Icc_neg_pi_div_two_of_mem_Icc_zero hβ
  have hκ : 0 < saddleKappa := by rw [saddleKappa_eq]; positivity
  have hcoeff : Λ * Real.cos β / saddleKappa < Λ * Real.cos α / saddleKappa :=
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (cos_strictAntiOn_saddle hα hβ hαβ) hΛ) hκ
  have hconst : alphaCot β - Λ / 2 - 1 < alphaCot α - Λ / 2 - 1 := by
    linarith [alphaCot_strictAntiOn hα hβ hαβ]
  have hrα := saddleRadiusAtLambda_pos hΛ.le hα
  have hrβ := saddleRadiusAtLambda_pos hΛ.le hβ
  have heqα := saddleRadiusAtLambda_radialEquation hΛ.le hαfull
  have heqβ := saddleRadiusAtLambda_radialEquation hΛ.le hβfull
  have hle : saddleRadiusAtLambda Λ β ≤ saddleRadiusAtLambda Λ α :=
    radialEquation_root_mono (saddleRadialCoeffAtLambda_nonneg hΛ.le hαfull)
      hcoeff.le hconst.le hrβ hrα heqβ heqα
  refine lt_of_le_of_ne hle fun heqr => ?_
  rw [heqr] at heqβ
  have hdiv : Λ * Real.cos β / saddleKappa / saddleRadiusAtLambda Λ α <
      Λ * Real.cos α / saddleKappa / saddleRadiusAtLambda Λ α :=
    (div_lt_div_iff_of_pos_right hrα).2 hcoeff
  unfold radialEquation at heqα heqβ
  linarith

/-- The inverse saddle radius at scale `Λ` strictly increases with the angle. -/
theorem saddleRadiusAtLambda_inv_strictMonoOn {Λ : ℝ} (hΛ : 0 < Λ) :
    StrictMonoOn (fun α => (saddleRadiusAtLambda Λ α)⁻¹)
      (Set.Icc 0 (Real.pi / 2)) := fun _ hα _ hβ hαβ =>
  (inv_lt_inv₀ (saddleRadiusAtLambda_pos hΛ.le hα) (saddleRadiusAtLambda_pos hΛ.le hβ)).2
    (saddleRadiusAtLambda_strictAntiOn hΛ hα hβ hαβ)

/-- Exact identity `q r² = 1 + (π / Λ) (α / sin α) r` at scale `Λ`. -/
theorem saddleQAtLambda_mul_radius_sq {Λ α : ℝ} (hΛ : 0 < Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 =
      1 + (Real.pi / Λ) * sinRatio α * saddleRadiusAtLambda Λ α := by
  have hrne := (saddleRadiusAtLambda_pos hΛ.le hα).ne'
  rw [saddleQAtLambda_eq]
  field_simp [hrne, hΛ.ne']

/-- The real saddle relation at scale `Λ`. -/
theorem saddle_real_relation_atLambda {Λ α : ℝ} (hΛ : 0 < Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    Real.pi * saddleRadiusAtLambda Λ α *
        (1 + 2 * Real.log (saddleRadiusAtLambda Λ α) / Λ) =
      2 * (saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 + 1) * Real.cos α -
        2 * Real.pi * saddleRadiusAtLambda Λ α / Λ := by
  have hr := saddleRadiusAtLambda_pos hΛ.le hα
  have hchar := saddleRadiusAtLambda_characterization hΛ.le
    (mem_Icc_neg_pi_div_two_of_mem_Icc_zero hα)
  have hq := saddleQAtLambda_mul_radius_sq hΛ hα
  rw [saddleKappa_eq, alphaCot_eq_sinRatio_mul_cos] at hchar
  rw [hq]
  field_simp [hΛ.ne', hr.ne', Real.pi_ne_zero] at hchar ⊢
  nlinarith

end Basic

/-! ### The radius is at most two -/

section RadiusLeTwo

/-- For `Λ ≥ 0` and `α ∈ [0, π/2]`, the radial equation at scale `Λ` is nonpositive at
`2 / (α / sin α)`. -/
theorem radialEquationAtLambda_two_div_sinRatio_nonpos {Λ α : ℝ} (hΛ : 0 ≤ Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    radialEquation (Λ * Real.cos α / saddleKappa) (alphaCot α - Λ / 2 - 1)
      (2 / sinRatio α) ≤ 0 := by
  have hs : 0 < sinRatio α := sinRatio_pos_of_mem hα
  have hsle : sinRatio α ≤ 2 := sinRatio_le_two hα
  have hlog : 0 ≤ Real.log (2 / sinRatio α) :=
    Real.log_nonneg ((le_div_iff₀ hs).2 (by simpa using hsle))
  have hcot : alphaCot α ≤ 1 := alphaCot_le_one_of_mem hα
  have hfrac : alphaCot α / Real.pi ≤ (1 : ℝ) / 2 :=
    (div_le_div_of_nonneg_right hcot Real.pi_pos.le).trans
      ((div_le_div_iff_of_pos_left zero_lt_one Real.pi_pos (by norm_num)).2 Real.two_le_pi)
  have hterm :
      Λ * Real.cos α / saddleKappa / (2 / sinRatio α) =
        Λ * alphaCot α / Real.pi := by
    rw [saddleKappa_eq, ← cos_mul_sinRatio α]
    field_simp [hs.ne', Real.pi_ne_zero]
  rw [radialEquation, hterm]
  have hmain : Λ * (alphaCot α / Real.pi - 1 / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hΛ (sub_nonpos.2 hfrac)
  calc
    Λ * alphaCot α / Real.pi + (alphaCot α - Λ / 2 - 1) -
        Real.log (2 / sinRatio α) =
      Λ * (alphaCot α / Real.pi - 1 / 2) +
          (alphaCot α - 1) - Real.log (2 / sinRatio α) := by ring
    _ ≤ 0 := by linarith

/-- For `Λ ≥ 0` and `α ∈ [0, π/2]`, the radius at scale `Λ` satisfies `r (α / sin α) ≤ 2`. -/
theorem saddleRadiusAtLambda_mul_sinRatio_le_two {Λ α : ℝ} (hΛ : 0 ≤ Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    saddleRadiusAtLambda Λ α * sinRatio α ≤ 2 := by
  have hαfull := mem_Icc_neg_pi_div_two_of_mem_Icc_zero hα
  have hcoeff := saddleRadialCoeffAtLambda_nonneg hΛ hαfull
  have hr := saddleRadiusAtLambda_pos hΛ hα
  have hreq := saddleRadiusAtLambda_radialEquation hΛ hαfull
  have hcand : 0 < 2 / sinRatio α := two_div_sinRatio_pos hα
  have hcandE := radialEquationAtLambda_two_div_sinRatio_nonpos hΛ hα
  have hrle : saddleRadiusAtLambda Λ α ≤ 2 / sinRatio α := by
    by_contra! hlt
    have hanti := radialEquation_strictAntiOn
      (B := alphaCot α - Λ / 2 - 1) hcoeff hcand hr hlt
    linarith
  exact (le_div_iff₀ (sinRatio_pos_of_mem hα)).1 hrle

/-- For `Λ ≥ 0` and `α ∈ [0, π/2]`, the radius at scale `Λ` satisfies `r_Λ(α) ≤ 2`. -/
theorem saddleRadiusAtLambda_le_two {Λ α : ℝ} (hΛ : 0 ≤ Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) : saddleRadiusAtLambda Λ α ≤ 2 := by
  have hsone := one_le_sinRatio_of_mem hα
  have hrprod := saddleRadiusAtLambda_mul_sinRatio_le_two hΛ hα
  have hr0 := (saddleRadiusAtLambda_pos hΛ hα).le
  nlinarith [mul_le_mul_of_nonneg_left hsone hr0]

end RadiusLeTwo

/-! ### Bounds on `q r²` -/

section ProductBounds

/-- For `Λ > 0` and `α ∈ [0, π/2]`, `1 ≤ q_Λ(α) r_Λ(α)²`. -/
theorem one_le_saddleQAtLambda_mul_radius_sq {Λ α : ℝ} (hΛ : 0 < Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    1 ≤ saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 := by
  rw [saddleQAtLambda_mul_radius_sq hΛ hα]
  have hc : 0 ≤ Real.pi / Λ := (div_pos Real.pi_pos hΛ).le
  have hs : 0 ≤ sinRatio α := (sinRatio_pos_of_mem hα).le
  have hr : 0 ≤ saddleRadiusAtLambda Λ α := (saddleRadiusAtLambda_pos hΛ.le hα).le
  nlinarith [mul_nonneg (mul_nonneg hc hs) hr]

/-- For `Λ > 0` and `α ∈ [0, π/2]`, `q_Λ(α) r_Λ(α)² ≤ 1 + 2π / Λ`. -/
theorem saddleQAtLambda_mul_radius_sq_le {Λ α : ℝ} (hΛ : 0 < Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 ≤ 1 + 2 * Real.pi / Λ := by
  rw [saddleQAtLambda_mul_radius_sq hΛ hα]
  have hc : 0 ≤ Real.pi / Λ := (div_pos Real.pi_pos hΛ).le
  have hrad := saddleRadiusAtLambda_mul_sinRatio_le_two hΛ.le hα
  calc
    1 + Real.pi / Λ * sinRatio α * saddleRadiusAtLambda Λ α =
        1 + (Real.pi / Λ) * (sinRatio α * saddleRadiusAtLambda Λ α) := by ring
    _ ≤ 1 + (Real.pi / Λ) * 2 :=
      (add_le_add_iff_left 1).2 (mul_le_mul_of_nonneg_left (by simpa [mul_comm] using hrad) hc)
    _ = 1 + 2 * Real.pi / Λ := by ring

end ProductBounds

/-! ### Comparison of the radius with the level -/

section RadiusLevel

/-- For `Λ ≥ 2π` and `α ∈ [0, π/2]`, the radius and the level `q = q_Λ(α)` satisfy
`1 / √q ≤ r_Λ(α) ≤ √2 / √q`. -/
theorem saddleRadiusAtLambda_level_comparison {Λ α : ℝ} (hΛ : 2 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    1 / Real.sqrt (saddleQAtLambda Λ α) ≤ saddleRadiusAtLambda Λ α ∧
      saddleRadiusAtLambda Λ α ≤ Real.sqrt 2 / Real.sqrt (saddleQAtLambda Λ α) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  have hr := saddleRadiusAtLambda_pos hΛ0.le hα
  have hp := one_le_saddleQAtLambda_mul_radius_sq hΛ0 hα
  have hu := saddleQAtLambda_mul_radius_sq_le hΛ0 hα
  set q := saddleQAtLambda Λ α
  set r := saddleRadiusAtLambda Λ α
  have hq0 : 0 < q := by
    by_contra! hn
    have := mul_nonpos_of_nonpos_of_nonneg hn (sq_nonneg r)
    linarith
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hs2 : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0.le
  have hupper : q * r ^ 2 ≤ 2 := by
    have hfrac : 2 * Real.pi / Λ ≤ 1 := (div_le_one hΛ0).2 hΛ
    linarith
  have h22 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · have hprod2 : 1 ≤ (r * Real.sqrt q) ^ 2 := by
      calc
        1 ≤ q * r ^ 2 := hp
        _ = _ := by rw [mul_pow, hs2]; ring
    apply (div_le_iff₀ hs).2
    nlinarith [mul_nonneg hr.le hs.le]
  · apply (le_div_iff₀ hs).2
    nlinarith [Real.sqrt_nonneg 2, mul_nonneg hr.le hs.le]

end RadiusLevel

/-! ### Comparison of `cos α` with the radius -/

section CosRadius

/-- If the level at scale `Λ > 0` is at most `T > 0`, where `log T ≤ 3Λ / 4`, then
`-3Λ / 8 ≤ log r_Λ(α)`. -/
theorem saddleRadiusAtLambda_log_lower {Λ T α : ℝ} (hΛ : 0 < Λ) (hT : 0 < T)
    (hlogT : Real.log T ≤ 3 * Λ / 4) (hα : α ∈ Set.Icc 0 (Real.pi / 2))
    (hqT : saddleQAtLambda Λ α ≤ T) :
    -(3 * Λ / 8) ≤ Real.log (saddleRadiusAtLambda Λ α) := by
  have hr := saddleRadiusAtLambda_pos hΛ.le hα
  have hp := one_le_saddleQAtLambda_mul_radius_sq hΛ hα
  have hTr2 : 1 ≤ T * saddleRadiusAtLambda Λ α ^ 2 := by
    nlinarith [sq_nonneg (saddleRadiusAtLambda Λ α)]
  have hlogprod := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hTr2
  rw [Real.log_one, Real.log_mul hT.ne' (pow_ne_zero 2 hr.ne'), Real.log_pow] at hlogprod
  norm_num at hlogprod
  linarith

/-- If the level at scale `Λ > 0` is at most `T > 0`, where `log T ≤ 3Λ / 4`, then
`π r_Λ(α) / 16 ≤ cos α`. -/
theorem pi_mul_saddleRadiusAtLambda_div_sixteen_le_cos {Λ T α : ℝ} (hΛ : 0 < Λ) (hT : 0 < T)
    (hlogT : Real.log T ≤ 3 * Λ / 4) (hα : α ∈ Set.Icc 0 (Real.pi / 2))
    (hqT : saddleQAtLambda Λ α ≤ T) :
    Real.pi * saddleRadiusAtLambda Λ α / 16 ≤ Real.cos α := by
  have hr := saddleRadiusAtLambda_pos hΛ.le hα
  have hlog := saddleRadiusAtLambda_log_lower hΛ hT hlogT hα hqT
  have hcot := alphaCot_le_one_of_mem hα
  have hchar := saddleRadiusAtLambda_characterization hΛ.le
    (mem_Icc_neg_pi_div_two_of_mem_Icc_zero hα)
  rw [saddleKappa_eq] at hchar
  have hterm : Λ / 8 ≤
      Λ * Real.cos α / ((Real.pi / 2) * saddleRadiusAtLambda Λ α) := by
    linarith
  have hden : 0 < (Real.pi / 2) * saddleRadiusAtLambda Λ α := mul_pos (by positivity) hr
  have hmul := (le_div_iff₀ hden).1 hterm
  nlinarith [mul_pos hΛ Real.pi_pos]

/-- For `Λ ≥ 2 (1 + log 2)` and `α ∈ [0, π/2]`, `cos α ≤ π r_Λ(α) / 2`. -/
theorem cos_le_pi_mul_saddleRadiusAtLambda_div_two {Λ α : ℝ}
    (hΛ : 2 * (1 + Real.log 2) ≤ Λ) (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    Real.cos α ≤ Real.pi * saddleRadiusAtLambda Λ α / 2 := by
  have hΛ0 : 0 < Λ := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hr := saddleRadiusAtLambda_pos hΛ0.le hα
  have hr2 := saddleRadiusAtLambda_le_two hΛ0.le hα
  have hlog : Real.log (saddleRadiusAtLambda Λ α) ≤ Real.log 2 := Real.log_le_log hr hr2
  have hcot0 : 0 ≤ alphaCot α := by
    rw [← cos_mul_sinRatio]
    exact mul_nonneg (Real.cos_nonneg_of_mem_Icc (mem_Icc_neg_pi_div_two_of_mem_Icc_zero hα))
      (sinRatio_pos_of_mem hα).le
  have hchar := saddleRadiusAtLambda_characterization hΛ0.le
    (mem_Icc_neg_pi_div_two_of_mem_Icc_zero hα)
  rw [saddleKappa_eq] at hchar
  have hterm :
      Λ * Real.cos α / ((Real.pi / 2) * saddleRadiusAtLambda Λ α) ≤ Λ := by
    linarith
  have hden : 0 < (Real.pi / 2) * saddleRadiusAtLambda Λ α := mul_pos (by positivity) hr
  have hmul := (div_le_iff₀ hden).1 hterm
  nlinarith [mul_pos hΛ0 Real.pi_pos]

/-- For `Λ ≥ 2 (1 + log 2)`, if the level at scale `Λ` is at most `T > 0`, where
`log T ≤ 3Λ / 4`, then `π r_Λ(α) / 16 ≤ cos α ≤ π r_Λ(α) / 2`. -/
theorem saddleCosAtLambda_radius_comparison {Λ T α : ℝ}
    (hΛ : 2 * (1 + Real.log 2) ≤ Λ) (hT : 0 < T) (hlogT : Real.log T ≤ 3 * Λ / 4)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) (hqT : saddleQAtLambda Λ α ≤ T) :
    Real.pi * saddleRadiusAtLambda Λ α / 16 ≤ Real.cos α ∧
      Real.cos α ≤ Real.pi * saddleRadiusAtLambda Λ α / 2 :=
  ⟨pi_mul_saddleRadiusAtLambda_div_sixteen_le_cos
      (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]) hT hlogT hα hqT,
    cos_le_pi_mul_saddleRadiusAtLambda_div_two hΛ hα⟩

end CosRadius

/-! ### The edge level -/

section EdgeLevel

/-- At scale `Λ > 0` the edge radius lies outside the unit circle. -/
theorem one_le_saddleRadiusAtLambda_zero {Λ : ℝ} (hΛ : 0 < Λ) :
    1 ≤ saddleRadiusAtLambda Λ 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hr := saddleRadiusAtLambda_pos hΛ.le h0
  have hchar := saddleRadiusAtLambda_characterization hΛ.le
    (mem_Icc_neg_pi_div_two_of_mem_Icc_zero h0)
  rw [saddleKappa_eq, Real.cos_zero, alphaCot_zero, mul_one] at hchar
  by_contra! hrlt
  have hlog : Real.log (saddleRadiusAtLambda Λ 0) < 0 := Real.log_neg hr hrlt
  have hden : (Real.pi / 2) * saddleRadiusAtLambda Λ 0 < 2 := by
    calc
      (Real.pi / 2) * saddleRadiusAtLambda Λ 0 < (Real.pi / 2) * 1 :=
        mul_lt_mul_of_pos_left hrlt (by positivity)
      _ ≤ 2 := by simpa using Real.pi_div_two_le_two
  have hleft : Λ / 2 < Λ / ((Real.pi / 2) * saddleRadiusAtLambda Λ 0) :=
    div_lt_div_of_pos_left hΛ (mul_pos (by positivity) hr) hden
  linarith

/-- For `Λ ≥ 2π`, the edge level at scale `Λ` satisfies `q_{e,Λ} ≤ 2`. -/
theorem edgeQAtLambda_le_two {Λ : ℝ} (hΛ : 2 * Real.pi ≤ Λ) : edgeQAtLambda Λ ≤ 2 := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hrpos := saddleRadiusAtLambda_pos hΛpos.le h0
  have hr1 := one_le_saddleRadiusAtLambda_zero hΛpos
  have hinv0 : 0 ≤ (saddleRadiusAtLambda Λ 0)⁻¹ := (inv_pos.2 hrpos).le
  have hinv1 : (saddleRadiusAtLambda Λ 0)⁻¹ ≤ 1 := (inv_le_one₀ hrpos).2 hr1
  have hfrac : Real.pi / Λ ≤ 1 / 2 := by
    apply (div_le_iff₀ hΛpos).2
    nlinarith
  rw [edgeQAtLambda, saddleQAtLambda_eq, sinRatio_zero]
  nlinarith [sq_nonneg ((saddleRadiusAtLambda Λ 0)⁻¹),
    mul_le_mul hinv1 hfrac (div_nonneg Real.pi_pos.le hΛpos.le) (by norm_num : (0 : ℝ) ≤ 1)]

/-- For `Λ ≥ 0`, the reciprocal edge radius at scale `Λ` is at least `1/2`. -/
theorem half_le_saddleRadiusAtLambda_zero_inv {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    1 / 2 ≤ (saddleRadiusAtLambda Λ 0)⁻¹ := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hr0 := saddleRadiusAtLambda_pos hΛ h0
  have hr0two := saddleRadiusAtLambda_le_two hΛ h0
  rw [inv_eq_one_div]
  exact (le_div_iff₀ hr0).2 (by nlinarith)

/-- For `Λ > 0`, the reciprocal edge radius at scale `Λ` is at most `1`. -/
theorem saddleRadiusAtLambda_zero_inv_le_one {Λ : ℝ} (hΛ : 0 < Λ) :
    (saddleRadiusAtLambda Λ 0)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_saddleRadiusAtLambda_zero hΛ)

end EdgeLevel

/-! ### Quadratic separation of the level from the edge level -/

section EdgeQuadratic

/-- The difference of the radial equations at `α` and at the edge `α = 0`, written in the
reciprocal radius. -/
theorem saddleRadiusAtLambda_inv_radial_difference {Λ α : ℝ} (hΛ : 0 < Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    (2 * Λ / Real.pi) *
        ((saddleRadiusAtLambda Λ α)⁻¹ * Real.cos α - (saddleRadiusAtLambda Λ 0)⁻¹) +
      (alphaCot α - 1) +
      Real.log ((saddleRadiusAtLambda Λ α)⁻¹ / (saddleRadiusAtLambda Λ 0)⁻¹) = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hrα := saddleRadiusAtLambda_pos hΛ.le hα
  have hr0 := saddleRadiusAtLambda_pos hΛ.le h0
  have hcα := saddleRadiusAtLambda_characterization hΛ.le
    (mem_Icc_neg_pi_div_two_of_mem_Icc_zero hα)
  have hc0 := saddleRadiusAtLambda_characterization hΛ.le
    (mem_Icc_neg_pi_div_two_of_mem_Icc_zero h0)
  rw [saddleKappa_eq] at hcα hc0
  rw [Real.cos_zero, alphaCot_zero] at hc0
  have hlog :
      Real.log ((saddleRadiusAtLambda Λ α)⁻¹ / (saddleRadiusAtLambda Λ 0)⁻¹) =
        -Real.log (saddleRadiusAtLambda Λ α) + Real.log (saddleRadiusAtLambda Λ 0) := by
    rw [Real.log_div (inv_ne_zero hrα.ne') (inv_ne_zero hr0.ne'), Real.log_inv, Real.log_inv]
    ring
  have eα : Λ * Real.cos α / ((Real.pi / 2) * saddleRadiusAtLambda Λ α) =
      (2 * Λ / Real.pi) * ((saddleRadiusAtLambda Λ α)⁻¹ * Real.cos α) := by
    field_simp [Real.pi_ne_zero, hrα.ne']
  have e0 : Λ * 1 / ((Real.pi / 2) * saddleRadiusAtLambda Λ 0) =
      (2 * Λ / Real.pi) * (saddleRadiusAtLambda Λ 0)⁻¹ := by
    field_simp [Real.pi_ne_zero, hr0.ne']
  rw [hlog]
  rw [eα] at hcα
  rw [e0] at hc0
  linarith

/-- For `Λ ≥ 24π` and `α ∈ [0, π/2]`, `α² / 50 ≤ r_Λ(α)⁻¹ - r_Λ(0)⁻¹`. -/
theorem saddleRadiusAtLambda_inv_sub_edge_lower {Λ α : ℝ} (hΛ : 24 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    α ^ 2 / 50 ≤ (saddleRadiusAtLambda Λ α)⁻¹ - (saddleRadiusAtLambda Λ 0)⁻¹ := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hid := saddleRadiusAtLambda_inv_radial_difference hΛ0 hα
  have hx := inv_pos.2 (saddleRadiusAtLambda_pos hΛ0.le hα)
  have hx0 := inv_pos.2 (saddleRadiusAtLambda_pos hΛ0.le h0)
  have hxx0 : (saddleRadiusAtLambda Λ 0)⁻¹ ≤ (saddleRadiusAtLambda Λ α)⁻¹ :=
    (saddleRadiusAtLambda_inv_strictMonoOn hΛ0).monotoneOn h0 hα hα.1
  have hcot : alphaCot α ≤ 1 := alphaCot_le_one_of_mem hα
  set x := (saddleRadiusAtLambda Λ α)⁻¹
  set x₀ := (saddleRadiusAtLambda Λ 0)⁻¹
  set a := 2 * Λ / Real.pi
  have hdx : 0 ≤ x - x₀ := sub_nonneg.mpr hxx0
  have ha48 : 48 ≤ a := (le_div_iff₀ Real.pi_pos).2 (by linarith)
  have ha : 0 < a := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hx0)
  have hratio_sub : x / x₀ - 1 = (x - x₀) / x₀ := by
    field_simp [hx0.ne']
  rw [hratio_sub] at hlog
  have hlog' : Real.log (x / x₀) ≤ x₀⁻¹ * (x - x₀) := by
    simpa [div_eq_mul_inv, mul_comm] using hlog
  have hmain : a * x₀ * (1 - Real.cos α) ≤ (a + x₀⁻¹) * (x - x₀) := by
    have hleft : a * Real.cos α * (x - x₀) + Real.log (x / x₀) =
        a * x₀ * (1 - Real.cos α) + (1 - alphaCot α) := by
      linarith
    have hupper : a * Real.cos α * (x - x₀) + Real.log (x / x₀) ≤
        (a + x₀⁻¹) * (x - x₀) := by
      have := mul_le_mul_of_nonneg_left (Real.cos_le_one α) (mul_nonneg ha.le hdx)
      nlinarith
    nlinarith
  exact sq_div_fifty_le_of_mul_one_sub_cos_le ha48
    (half_le_saddleRadiusAtLambda_zero_inv hΛ0.le) hxx0 hα hmain

/-- For `Λ ≥ 24π` and `α ∈ [0, π/2]`, `α² / 50 ≤ q_Λ(α) - q_{e,Λ}`. -/
theorem saddleQAtLambda_sub_edge_lower {Λ α : ℝ} (hΛ : 24 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    α ^ 2 / 50 ≤ saddleQAtLambda Λ α - edgeQAtLambda Λ := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hx0 := inv_pos.2 (saddleRadiusAtLambda_pos hΛ0.le h0)
  have hxx0 : (saddleRadiusAtLambda Λ 0)⁻¹ ≤ (saddleRadiusAtLambda Λ α)⁻¹ :=
    (saddleRadiusAtLambda_inv_strictMonoOn hΛ0).monotoneOn h0 hα hα.1
  have hx0half := half_le_saddleRadiusAtLambda_zero_inv hΛ0.le
  have hlowr := saddleRadiusAtLambda_inv_sub_edge_lower hΛ hα
  rw [edgeQAtLambda, saddleQAtLambda_eq, saddleQAtLambda_eq, sinRatio_zero]
  set x := (saddleRadiusAtLambda Λ α)⁻¹
  set x₀ := (saddleRadiusAtLambda Λ 0)⁻¹
  have hprod : x₀ ≤ sinRatio α * x := (one_mul x₀).ge.trans
    (mul_le_mul (one_le_sinRatio_of_mem hα) hxx0 hx0.le (sinRatio_pos_of_mem hα).le)
  have hcoef : 0 ≤ Real.pi / Λ := (div_pos Real.pi_pos hΛ0).le
  have hsq : x - x₀ ≤ x ^ 2 - x₀ ^ 2 := by
    have hsum : 1 ≤ x + x₀ := by linarith
    have hdx : 0 ≤ x - x₀ := sub_nonneg.mpr hxx0
    nlinarith [mul_nonneg hdx (sub_nonneg.mpr hsum)]
  nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hprod)]

/-- For `Λ ≥ 24π` and `α ∈ [0, 1/2]`, `r_Λ(α)⁻¹ - r_Λ(0)⁻¹ ≤ 2 α²`. -/
theorem saddleRadiusAtLambda_inv_sub_edge_upper {Λ α : ℝ} (hΛ : 24 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    (saddleRadiusAtLambda Λ α)⁻¹ - (saddleRadiusAtLambda Λ 0)⁻¹ ≤ 2 * α ^ 2 := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  have hαpi : α ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨hα.1, hα.2.trans (by nlinarith [Real.two_le_pi])⟩
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hid := saddleRadiusAtLambda_inv_radial_difference hΛ0 hαpi
  have hx0 := inv_pos.2 (saddleRadiusAtLambda_pos hΛ0.le h0)
  have hx0one := saddleRadiusAtLambda_zero_inv_le_one hΛ0
  have hxx0 : (saddleRadiusAtLambda Λ 0)⁻¹ ≤ (saddleRadiusAtLambda Λ α)⁻¹ :=
    (saddleRadiusAtLambda_inv_strictMonoOn hΛ0).monotoneOn h0 hαpi hα.1
  set x := (saddleRadiusAtLambda Λ α)⁻¹
  set x₀ := (saddleRadiusAtLambda Λ 0)⁻¹
  set a := 2 * Λ / Real.pi
  have hdx : 0 ≤ x - x₀ := sub_nonneg.mpr hxx0
  have ha48 : 48 ≤ a := (le_div_iff₀ Real.pi_pos).2 (by linarith)
  have ha : 0 < a := by linarith
  have hcoslo := half_le_cos_of_mem_Icc hα
  have hcosloss : 1 - Real.cos α ≤ α ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hcotloss := one_sub_alphaCot_le_sq_div_two hα
  have hlog0 : 0 ≤ Real.log (x / x₀) :=
    Real.log_nonneg ((le_div_iff₀ hx0).2 (by simpa using hxx0))
  have hleft :
      a * Real.cos α * (x - x₀) + Real.log (x / x₀) =
        a * x₀ * (1 - Real.cos α) + (1 - alphaCot α) := by
    linarith
  have hlower :
      a * (1 / 2 : ℝ) * (x - x₀) ≤ a * Real.cos α * (x - x₀) + Real.log (x / x₀) := by
    have hc := mul_le_mul_of_nonneg_right hcoslo hdx
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hc)]
  have hupper :
      a * x₀ * (1 - Real.cos α) + (1 - alphaCot α) ≤ (a + 1) * (α ^ 2 / 2) := by
    have hfirst := mul_le_mul hcosloss hx0one hx0.le (by positivity : 0 ≤ α ^ 2 / 2)
    have hfirst' := mul_le_mul_of_nonneg_left hfirst ha.le
    nlinarith
  have hcoef := mul_le_mul_of_nonneg_right
    (show a + 1 ≤ (49 / 48 : ℝ) * a by linarith) (by positivity : 0 ≤ α ^ 2 / 2)
  have hraw : a * ((x - x₀) / 2) ≤ a * ((49 / 48 : ℝ) * α ^ 2 / 2) := by linarith
  have hcancel : (x - x₀) / 2 ≤ (49 / 48 : ℝ) * α ^ 2 / 2 := le_of_mul_le_mul_left hraw ha
  nlinarith [sq_nonneg α]

/-- For `Λ ≥ 24π` and `α ∈ [0, 1/2]`, `q_Λ(α) - q_{e,Λ} ≤ 6 α²`. -/
theorem saddleQAtLambda_sub_edge_upper {Λ α : ℝ} (hΛ : 24 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    saddleQAtLambda Λ α - edgeQAtLambda Λ ≤ 6 * α ^ 2 := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  have hαpi : α ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨hα.1, hα.2.trans (by nlinarith [Real.two_le_pi])⟩
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hx0 := inv_pos.2 (saddleRadiusAtLambda_pos hΛ0.le h0)
  have hx0one := saddleRadiusAtLambda_zero_inv_le_one hΛ0
  have hxx0 : (saddleRadiusAtLambda Λ 0)⁻¹ ≤ (saddleRadiusAtLambda Λ α)⁻¹ :=
    (saddleRadiusAtLambda_inv_strictMonoOn hΛ0).monotoneOn h0 hαpi hα.1
  have hdx : (saddleRadiusAtLambda Λ α)⁻¹ - (saddleRadiusAtLambda Λ 0)⁻¹ ≤ 2 * α ^ 2 :=
    saddleRadiusAtLambda_inv_sub_edge_upper hΛ hα
  rw [edgeQAtLambda, saddleQAtLambda_eq, saddleQAtLambda_eq, sinRatio_zero]
  set x := (saddleRadiusAtLambda Λ α)⁻¹
  set x₀ := (saddleRadiusAtLambda Λ 0)⁻¹
  have hdx0 : 0 ≤ x - x₀ := sub_nonneg.mpr hxx0
  have hsqα : α ^ 2 ≤ 1 / 4 := by nlinarith [hα.1, hα.2]
  have hx : x ≤ 3 / 2 := by nlinarith
  have hs : sinRatio α ≤ 1 + α ^ 2 := sinRatio_le_one_add_sq hα
  have hs0 : 0 ≤ sinRatio α := (sinRatio_pos_of_mem hαpi).le
  have hsone := one_le_sinRatio_of_mem hαpi
  have hsqdiff : x ^ 2 - x₀ ^ 2 ≤ 5 * α ^ 2 := by
    have hsum : x + x₀ ≤ 5 / 2 := by nlinarith
    have hm := mul_le_mul hdx hsum (by nlinarith [hx0]) (by positivity : 0 ≤ 2 * α ^ 2)
    nlinarith [sq_nonneg (x - x₀)]
  have hproddiff : sinRatio α * x - x₀ ≤ 4 * α ^ 2 := by
    have hsone' : sinRatio α - 1 ≤ α ^ 2 := by linarith
    have hsexpand :
        sinRatio α * x - x₀ = sinRatio α * (x - x₀) + (sinRatio α - 1) * x₀ := by ring
    have hfirst := mul_le_mul hs hdx hdx0 (by positivity : 0 ≤ 1 + α ^ 2)
    have hsecond := mul_le_mul hsone' hx0one hx0.le (sq_nonneg α)
    rw [hsexpand]
    nlinarith [mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hsqα)]
  have hcoef : Real.pi / Λ ≤ 1 / 24 :=
    (div_le_iff₀ hΛ0).2 (by nlinarith [Real.pi_pos])
  have hcoef0 : 0 ≤ Real.pi / Λ := (div_pos Real.pi_pos hΛ0).le
  have hterm := mul_le_mul hcoef hproddiff
    (by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hxx0),
        mul_nonneg (sub_nonneg.mpr hsone) hx0.le])
    (by norm_num : (0 : ℝ) ≤ 1 / 24)
  nlinarith

end EdgeQuadratic

/-! ### Curvature and quadratic gap on the saddle circle -/

section CircleGap

/-- The real part of the scale-`Λ` phase on the saddle circle of angle `α`, in
the coordinate `z = cos β`. -/
noncomputable def circleRealPhaseZAtLambda (Λ α z : ℝ) : ℝ :=
  -saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 * (2 * z ^ 2 - 1) +
    Real.pi * saddleRadiusAtLambda Λ α *
      (1 + 2 * Real.log (saddleRadiusAtLambda Λ α) / Λ) * z -
    (2 * Real.pi * saddleRadiusAtLambda Λ α / Λ) * circleArc z -
    2 * Real.log (saddleRadiusAtLambda Λ α)

/-- First `z`-derivative of `circleRealPhaseZAtLambda`. -/
noncomputable def circleRealPhaseZDerivAtLambda (Λ α z : ℝ) : ℝ :=
  -4 * saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 * z +
    Real.pi * saddleRadiusAtLambda Λ α *
      (1 + 2 * Real.log (saddleRadiusAtLambda Λ α) / Λ) -
    (2 * Real.pi * saddleRadiusAtLambda Λ α / Λ) * circleArcDeriv z

/-- Second `z`-derivative of `circleRealPhaseZAtLambda`. -/
noncomputable def circleRealPhaseZSecondAtLambda (Λ α z : ℝ) : ℝ :=
  -4 * saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 -
    (2 * Real.pi * saddleRadiusAtLambda Λ α / Λ) * circleArcSecond z

/-- At the Riemann scale the circle phase is the Riemann one. -/
theorem circleRealPhaseZAtLambda_scaleLambda (d : ℕ) (α z : ℝ) :
    circleRealPhaseZAtLambda (scaleLambda d) α z = circleRealPhaseZ d α z := by
  simp only [circleRealPhaseZAtLambda, circleRealPhaseZ,
    saddleRadiusAtLambda_scaleLambda, saddleQAtLambda_scaleLambda]

/-- At the Riemann scale the second `z`-derivative of the circle phase is the Riemann one. -/
theorem circleRealPhaseZSecondAtLambda_scaleLambda (d : ℕ) (α z : ℝ) :
    circleRealPhaseZSecondAtLambda (scaleLambda d) α z = circleRealPhaseZSecond d α z := by
  simp only [circleRealPhaseZSecondAtLambda, circleRealPhaseZSecond,
    saddleRadiusAtLambda_scaleLambda, saddleQAtLambda_scaleLambda]

/-- On `-1 < z < 1`, `circleRealPhaseZAtLambda Λ α` has derivative
`circleRealPhaseZDerivAtLambda Λ α z`. -/
theorem hasDerivAt_circleRealPhaseZAtLambda (Λ α : ℝ) {z : ℝ} (hz : z ∈ Set.Ioo (-1) 1) :
    HasDerivAt (circleRealPhaseZAtLambda Λ α) (circleRealPhaseZDerivAtLambda Λ α z) z := by
  have harc := hasDerivAt_circleArc hz
  have h := ((((hasDerivAt_const z
      (-saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2)).mul
        ((((hasDerivAt_id z).pow 2).const_mul 2).sub_const 1)).add
      ((hasDerivAt_id z).const_mul
        (Real.pi * saddleRadiusAtLambda Λ α *
          (1 + 2 * Real.log (saddleRadiusAtLambda Λ α) / Λ)))).sub
      (harc.const_mul (2 * Real.pi * saddleRadiusAtLambda Λ α / Λ))).sub_const
        (2 * Real.log (saddleRadiusAtLambda Λ α))
  refine h.congr_deriv ?_
  simp only [circleRealPhaseZDerivAtLambda, id]
  push_cast
  ring

/-- On `-1 < z < 1`, `circleRealPhaseZDerivAtLambda Λ α` has derivative
`circleRealPhaseZSecondAtLambda Λ α z`. -/
theorem hasDerivAt_circleRealPhaseZDerivAtLambda (Λ α : ℝ) {z : ℝ}
    (hz : z ∈ Set.Ioo (-1) 1) :
    HasDerivAt (circleRealPhaseZDerivAtLambda Λ α)
      (circleRealPhaseZSecondAtLambda Λ α z) z := by
  have harc := hasDerivAt_circleArcDeriv hz
  have h := (((hasDerivAt_id z).const_mul
      (-4 * saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2)).add_const
        (Real.pi * saddleRadiusAtLambda Λ α *
          (1 + 2 * Real.log (saddleRadiusAtLambda Λ α) / Λ))).sub
      (harc.const_mul (2 * Real.pi * saddleRadiusAtLambda Λ α / Λ))
  refine h.congr_deriv ?_
  simp only [circleRealPhaseZSecondAtLambda]
  ring

/-- The circle phase `circleRealPhaseZAtLambda Λ α` is continuous in `z`. -/
theorem continuous_circleRealPhaseZAtLambda (Λ α : ℝ) :
    Continuous (circleRealPhaseZAtLambda Λ α) := by
  have harc : Continuous circleArc :=
    Real.continuous_arccos.mul
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))
  unfold circleRealPhaseZAtLambda
  fun_prop

/-- At `z = cos β` the second derivative is the explicit model curvature. -/
theorem circleRealPhaseZSecondAtLambda_cos (Λ α : ℝ) {β : ℝ}
    (hβ : β ∈ Set.Ioc 0 (Real.pi / 2)) :
    circleRealPhaseZSecondAtLambda Λ α (Real.cos β) =
      -4 * saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 +
        (2 * Real.pi * saddleRadiusAtLambda Λ α / Λ) * circleCurvatureQuotient β := by
  have hβcc : β ∈ Set.Icc 0 (Real.pi / 2) := ⟨hβ.1.le, hβ.2⟩
  have harccos : Real.arccos (Real.cos β) = β :=
    Real.arccos_cos hβ.1.le (hβ.2.trans (by linarith [Real.pi_pos]))
  have hsqrt := sqrt_one_sub_cos_sq hβcc
  rw [circleRealPhaseZSecondAtLambda, circleArcSecond, harccos, hsqrt,
    circleCurvatureQuotient, ite_eq_right hβ.1.ne']
  ring

/-- For `Λ ≥ 24π` and `α ∈ [0, π/2]`, the second `z`-derivative of the real phase on the
saddle circle of angle `α` is at most `-3` throughout `0 < z < 1`. -/
theorem circleRealPhaseZSecondAtLambda_le_neg_three {Λ α z : ℝ} (hΛ : 24 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) (hz : z ∈ Set.Ioo 0 1) :
    circleRealPhaseZSecondAtLambda Λ α z ≤ -3 := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  let β := Real.arccos z
  have hβ : β ∈ Set.Ioc 0 (Real.pi / 2) :=
    ⟨Real.arccos_pos.2 hz.2, (Real.arccos_lt_pi_div_two.2 hz.1).le⟩
  have hcos : Real.cos β = z := Real.cos_arccos (by linarith [hz.1]) hz.2.le
  rw [← hcos, circleRealPhaseZSecondAtLambda_cos Λ α hβ]
  have hq := one_le_saddleQAtLambda_mul_radius_sq hΛpos hα
  have hr0 := (saddleRadiusAtLambda_pos hΛpos.le hα).le
  have hr := saddleRadiusAtLambda_le_two hΛpos.le hα
  have hquot := circleCurvatureQuotient_bounds (β := β) ⟨hβ.1.le, hβ.2⟩
  have hrq : saddleRadiusAtLambda Λ α * circleCurvatureQuotient β ≤ 12 :=
    (mul_le_mul hr hquot.2 hquot.1 (by norm_num)).trans (by norm_num)
  have hcorr :
      (2 * Real.pi * saddleRadiusAtLambda Λ α / Λ) * circleCurvatureQuotient β ≤ 1 := by
    have hnum : 2 * Real.pi * saddleRadiusAtLambda Λ α * circleCurvatureQuotient β ≤ Λ := by
      nlinarith [Real.pi_pos]
    rw [div_mul_eq_mul_div]
    exact (div_le_one hΛpos).2 hnum
  nlinarith

/-- The circle phase is stationary at the saddle coordinate `z = cos α`. -/
theorem circleRealPhaseZDerivAtLambda_cos_eq_zero {Λ α : ℝ} (hΛ : 0 < Λ)
    (hα : α ∈ Set.Ioc 0 (Real.pi / 2)) :
    circleRealPhaseZDerivAtLambda Λ α (Real.cos α) = 0 := by
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2⟩
  have hrpos := saddleRadiusAtLambda_pos hΛ.le hαcc
  have hs : Real.sin α ≠ 0 := by
    have hpi : α < Real.pi := lt_of_le_of_lt hα.2 (by linarith [Real.pi_pos])
    exact (Real.sin_pos_of_pos_of_lt_pi hα.1 hpi).ne'
  have harccos : Real.arccos (Real.cos α) = α :=
    Real.arccos_cos hα.1.le (hα.2.trans (by linarith [Real.pi_pos]))
  have hsqrt := sqrt_one_sub_cos_sq hαcc
  have hrad := saddleRadiusAtLambda_characterization hΛ.le
    (mem_Icc_neg_pi_div_two_of_mem_Icc_zero hαcc)
  rw [saddleKappa_eq] at hrad
  have hq := saddleQAtLambda_mul_radius_sq hΛ hαcc
  rw [circleRealPhaseZDerivAtLambda, circleArcDeriv, harccos, hsqrt]
  rw [show -4 * saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 * Real.cos α =
      -4 * (saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2) * Real.cos α by ring, hq]
  rw [alphaCot_of_ne hα.1.ne'] at hrad
  rw [sinRatio_of_ne hα.1.ne']
  field_simp [hrpos.ne', hΛ.ne', Real.pi_ne_zero, hs] at hrad ⊢
  linear_combination (-1 : ℝ) * hrad

/-- The real-coordinate model is the real part of the scale-`Λ` phase on the
closed lower saddle semicircle. -/
theorem circleRealPhaseZAtLambda_cos_eq_phase_re {Λ α β : ℝ} (hΛ : 0 ≤ Λ)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) (hβ : β ∈ Set.Icc 0 (Real.pi / 2)) :
    circleRealPhaseZAtLambda Λ α (Real.cos β) =
      (saddlePhaseAtLambda Λ (saddleQAtLambda Λ α)
        ((((saddleRadiusAtLambda Λ α) ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((-2 * β : ℝ) : ℂ))))).re := by
  have hr := saddleRadiusAtLambda_pos hΛ hα
  have hθlower : -Real.pi ≤ -2 * β := by linarith [hβ.2]
  have hθupper : -2 * β ≤ 0 := by linarith [hβ.1]
  rw [saddlePhaseAtLambda, saddleKappa,
    lowerSqrt_sq_mul_exp_I_mul hr hθlower hθupper,
    lowerLog_sq_mul_exp_I_mul hr hθlower hθupper]
  have hexp_arg :
      Complex.I * ((-2 * β : ℝ) : ℂ) / 2 = ((-β : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hexp_two :
      Complex.I * ((-2 * β : ℝ) : ℂ) = ((-2 * β : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hk : (2 * (Real.pi / 2) : ℝ) = Real.pi := by ring
  rw [hexp_arg, hexp_two, hk]
  simp only [Complex.add_im, Complex.add_re, Complex.sub_re,
    Complex.neg_im, Complex.neg_re, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  rw [circleRealPhaseZAtLambda, circleArc,
    Real.arccos_cos hβ.1 (hβ.2.trans (by linarith [Real.pi_pos])), sqrt_one_sub_cos_sq hβ,
    show -2 * β = -(2 * β) by ring, Real.cos_neg, Real.sin_neg, Real.cos_two_mul β]
  ring

/-- The explicit circle gap in the `z = cos β` coordinate at scale `Λ ≥ 24π`. -/
theorem circleRealPhaseZAtLambda_quadratic_gap {Λ α z : ℝ} (hΛ : 24 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Ioc 0 (Real.pi / 2)) (hz : z ∈ Set.Icc 0 1) :
    (3 / 2 : ℝ) * (z - Real.cos α) ^ 2 ≤
      circleRealPhaseZAtLambda Λ α (Real.cos α) - circleRealPhaseZAtLambda Λ α z := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  let a := Real.cos α
  let G := circleRealPhaseZAtLambda Λ α
  let F : ℝ → ℝ := fun y => G y + (3 / 2 : ℝ) * (y - a) ^ 2
  let F' : ℝ → ℝ := fun y => circleRealPhaseZDerivAtLambda Λ α y + 3 * (y - a)
  let F'' : ℝ → ℝ := fun y => circleRealPhaseZSecondAtLambda Λ α y + 3
  have ha : a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩, Real.cos_le_one α⟩
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
    ((continuous_circleRealPhaseZAtLambda Λ α).add
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 2))).continuousOn
  have hderiv : ∀ y ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt F (F' y) (interior (Set.Icc (0 : ℝ) 1)) y := by
    intro y hy
    rw [interior_Icc] at hy ⊢
    have hG := hasDerivAt_circleRealPhaseZAtLambda Λ α (z := y) ⟨by linarith [hy.1], hy.2⟩
    have hquad : HasDerivAt (fun t : ℝ => (3 / 2 : ℝ) * (t - a) ^ 2) (3 * (y - a)) y :=
      ((((hasDerivAt_id y).sub_const a).pow 2).const_mul (3 / 2 : ℝ)).congr_deriv
        (by simp only [id]; push_cast; ring)
    exact (hG.add hquad).hasDerivWithinAt
  have hderiv2 : ∀ y ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt F' (F'' y) (interior (Set.Icc (0 : ℝ) 1)) y := by
    intro y hy
    rw [interior_Icc] at hy ⊢
    have hG := hasDerivAt_circleRealPhaseZDerivAtLambda Λ α (z := y)
      ⟨by linarith [hy.1], hy.2⟩
    have hlin : HasDerivAt (fun t : ℝ => 3 * (t - a)) 3 y :=
      (((hasDerivAt_id y).sub_const a).const_mul 3).congr_deriv (by ring)
    exact (hG.add hlin).hasDerivWithinAt
  have hnonpos : ∀ y ∈ interior (Set.Icc (0 : ℝ) 1), F'' y ≤ 0 := by
    intro y hy
    rw [interior_Icc] at hy
    dsimp [F'']
    have hcurv := circleRealPhaseZSecondAtLambda_le_neg_three hΛ ⟨hα.1.le, hα.2⟩ hy
    linarith
  have hstat : HasDerivAt G 0 a := by
    have hbase := hasDerivAt_circleRealPhaseZAtLambda Λ α (z := a)
      ⟨by linarith [ha.1], by
        simpa using Real.strictAntiOn_cos
          (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by simp [Real.pi_pos.le])
          (show α ∈ Set.Icc 0 Real.pi from
            ⟨hα.1.le, hα.2.trans (by linarith [Real.pi_pos])⟩) hα.1⟩
    rwa [circleRealPhaseZDerivAtLambda_cos_eq_zero hΛpos hα] at hbase
  exact quadratic_gap_of_second_deriv_nonpos (convex_Icc 0 1)
    hcont hderiv hderiv2 hnonpos (fun _ _ => rfl) ha hz hstat

/-- For `Λ ≥ 24π`, on the saddle circle of angle `α ∈ (0, π/2]`,
`Re h(r² e^{-2iα}) - Re h(r² e^{-2iβ}) ≥ (3/2) (cos β - cos α)²` for every `β ∈ [0, π/2]`. -/
theorem saddlePhaseAtLambda_circle_quadratic_gap {Λ α β : ℝ} (hΛ : 24 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Ioc 0 (Real.pi / 2)) (hβ : β ∈ Set.Icc 0 (Real.pi / 2)) :
    (3 / 2 : ℝ) * (Real.cos β - Real.cos α) ^ 2 ≤
      (saddlePhaseAtLambda Λ (saddleQAtLambda Λ α)
        ((((saddleRadiusAtLambda Λ α) ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((-2 * α : ℝ) : ℂ))))).re -
      (saddlePhaseAtLambda Λ (saddleQAtLambda Λ α)
        ((((saddleRadiusAtLambda Λ α) ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((-2 * β : ℝ) : ℂ))))).re := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2⟩
  have hz : Real.cos β ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hβ.1, Real.pi_pos], hβ.2⟩,
      Real.cos_le_one β⟩
  have hgap := circleRealPhaseZAtLambda_quadratic_gap hΛ hα hz
  rwa [circleRealPhaseZAtLambda_cos_eq_phase_re hΛpos.le hαcc hβ,
    circleRealPhaseZAtLambda_cos_eq_phase_re hΛpos.le hαcc hαcc] at hgap

end CircleGap

/-! ### The Hessian at the saddle point

The saddle point and the Hessian `D = u² h''(u)` at the angle `α` and scale `Λ`, and its
explicit value. At `Λ = scaleLambda d` they agree with the Riemann definitions
(`saddleHessianAtLambda_scaleLambda`). -/

section HessianFormula

/-- The lower saddle point of angle `α` at scale `Λ`. -/
noncomputable def saddlePointAtLambda (Λ α : ℝ) : ℂ :=
  ((saddleRadiusAtLambda Λ α ^ 2 : ℝ) : ℂ) * Complex.exp (-2 * Complex.I * (α : ℂ))

/-- The Hessian `u² h''(u)` at the saddle point of angle `α`, scale `Λ`. -/
noncomputable def saddleHessianAtLambda (Λ α : ℝ) : ℂ :=
  saddlePointAtLambda Λ α ^ 2 *
    iteratedDeriv 2 (saddlePhaseAtLambda Λ (saddleQAtLambda Λ α)) (saddlePointAtLambda Λ α)

/-- The explicit value of `u² h''(u)` at `u = r² exp (-2 i α)`, scale `Λ`. -/
noncomputable def explicitSaddleHessianAtLambda (Λ r α : ℝ) : ℂ :=
  1 - (((Real.pi * r / 4 : ℝ) : ℂ) *
    Complex.exp (((-α : ℝ) : ℂ) * Complex.I) *
    (1 + (((2 * Real.log r / Λ : ℝ) : ℂ) - ((2 * α / Λ : ℝ) : ℂ) * Complex.I)))

/-- At the Riemann scale the Hessian is the Riemann Hessian at `q = q_d(α)`. -/
theorem saddleHessianAtLambda_scaleLambda (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    saddleHessianAtLambda (scaleLambda d) α = saddleHessian d (saddleQ d α) := by
  have hphase : saddlePhaseAtLambda (scaleLambda d) (saddleQ d α) = phase d (saddleQ d α) :=
    funext (saddlePhaseAtLambda_scaleLambda d (saddleQ d α))
  rw [saddleHessian, saddle, saddleAngle_saddleQ d hd hα, saddleHessianAtLambda,
    saddlePointAtLambda, saddleQAtLambda_scaleLambda, saddleRadiusAtLambda_scaleLambda, hphase]

/-- The real part of the explicit Hessian is
`1 - (π r / 4) ((1 + 2 log r / Λ) cos α - (2 α / Λ) sin α)`. -/
theorem explicitSaddleHessianAtLambda_re (Λ r α : ℝ) :
    (explicitSaddleHessianAtLambda Λ r α).re =
      1 - Real.pi * r / 4 *
        ((1 + 2 * Real.log r / Λ) * Real.cos α - 2 * α / Λ * Real.sin α) := by
  rw [explicitSaddleHessianAtLambda, Complex.exp_ofReal_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

/-- The imaginary part of the explicit Hessian is
`(π r / 4) ((1 + 2 log r / Λ) sin α + 2 α cos α / Λ)`. -/
theorem explicitSaddleHessianAtLambda_im (Λ r α : ℝ) :
    (explicitSaddleHessianAtLambda Λ r α).im =
      Real.pi * r / 4 *
        ((1 + 2 * Real.log r / Λ) * Real.sin α + 2 * α * Real.cos α / Λ) := by
  rw [explicitSaddleHessianAtLambda, Complex.exp_ofReal_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

/-- On the slit plane, `analyticLowerSqrt` has derivative `analyticLowerSqrt u / (2 u)`. -/
theorem hasDerivAt_analyticLowerSqrt_atLambda {u : ℂ} (hu : u ∈ Complex.slitPlane) :
    HasDerivAt analyticLowerSqrt (analyticLowerSqrt u / (2 * u)) u := by
  have hdiv : HasDerivAt (fun z : ℂ => Complex.log z / 2) (u⁻¹ / 2) u :=
    (Complex.hasDerivAt_log hu).div_const 2
  have hcomp := (Complex.hasDerivAt_exp (Complex.log u / 2)).comp u hdiv
  have heq : Complex.exp (Complex.log u / 2) * (u⁻¹ / 2) =
      Complex.exp (Complex.log u / 2) / (2 * u) := by
    field_simp [Complex.slitPlane_ne_zero hu]
  unfold analyticLowerSqrt
  change HasDerivAt (Complex.exp ∘ fun z : ℂ => Complex.log z / 2)
    (Complex.exp (Complex.log u / 2) / (2 * u)) u
  exact hcomp.congr_deriv heq

/-- The holomorphic phase with coefficients `a` (of `√u`) and `b` (of `√u log u`). -/
noncomputable def analyticPhaseCoeff (q : ℝ) (a b : ℂ) (u : ℂ) : ℂ :=
  -(q : ℂ) * u + a * analyticLowerSqrt u + b * analyticLowerSqrt u * Complex.log u -
    Complex.log u

/-- The first derivative of `analyticPhaseCoeff q a b`. -/
noncomputable def analyticPhaseCoeffDeriv (q : ℝ) (a b : ℂ) (u : ℂ) : ℂ :=
  -(q : ℂ) + a * (analyticLowerSqrt u / (2 * u)) +
    b * ((analyticLowerSqrt u / (2 * u)) * Complex.log u + analyticLowerSqrt u / u) - 1 / u

/-- The second derivative of `analyticPhaseCoeff q a b`, which does not depend on `q`. -/
noncomputable def analyticPhaseCoeffDeriv2 (a b : ℂ) (u : ℂ) : ℂ :=
  (1 - a * analyticLowerSqrt u / 4 - b * analyticLowerSqrt u * Complex.log u / 4) / u ^ 2

/-- On the slit plane, `analyticPhaseCoeff q a b` has derivative
`analyticPhaseCoeffDeriv q a b u`. -/
theorem hasDerivAt_analyticPhaseCoeff {q : ℝ} {a b u : ℂ} (hu : u ∈ Complex.slitPlane) :
    HasDerivAt (analyticPhaseCoeff q a b) (analyticPhaseCoeffDeriv q a b u) u := by
  have hs := hasDerivAt_analyticLowerSqrt_atLambda hu
  have hl := Complex.hasDerivAt_log hu
  have hraw := ((((hasDerivAt_id u).const_mul (-(q : ℂ))).add
      (hs.const_mul a)).add ((hs.mul hl).const_mul b)).sub hl
  have heq : (-(q : ℂ) * 1 + a * (analyticLowerSqrt u / (2 * u)) +
      b * ((analyticLowerSqrt u / (2 * u)) * Complex.log u + analyticLowerSqrt u * u⁻¹) -
        u⁻¹) = analyticPhaseCoeffDeriv q a b u := by
    dsimp [analyticPhaseCoeffDeriv]
    field_simp [Complex.slitPlane_ne_zero hu]
  apply (hraw.congr_of_eventuallyEq ?_).congr_deriv heq
  filter_upwards [] with z
  dsimp [analyticPhaseCoeff]
  ring

/-- On the slit plane, `analyticPhaseCoeffDeriv q a b` has derivative
`analyticPhaseCoeffDeriv2 a b u`. -/
theorem hasDerivAt_analyticPhaseCoeffDeriv {q : ℝ} {a b u : ℂ}
    (hu : u ∈ Complex.slitPlane) :
    HasDerivAt (analyticPhaseCoeffDeriv q a b) (analyticPhaseCoeffDeriv2 a b u) u := by
  have hu0 := Complex.slitPlane_ne_zero hu
  have hs := hasDerivAt_analyticLowerSqrt_atLambda hu
  have hl := Complex.hasDerivAt_log hu
  have hA : HasDerivAt (fun z : ℂ => analyticLowerSqrt z / (2 * z))
      (-analyticLowerSqrt u / (4 * u ^ 2)) u := by
    have hraw := hs.div ((hasDerivAt_id u).const_mul (2 : ℂ)) (by simpa using hu0)
    have heq : (analyticLowerSqrt u / (2 * u) * (2 * u) -
        analyticLowerSqrt u * (2 * 1)) / (2 * u) ^ 2 =
        -analyticLowerSqrt u / (4 * u ^ 2) := by
      field_simp [hu0]
      ring
    change HasDerivAt (analyticLowerSqrt / fun z : ℂ => 2 * z)
      (-analyticLowerSqrt u / (4 * u ^ 2)) u
    exact hraw.congr_deriv heq
  have hB : HasDerivAt (fun z : ℂ => analyticLowerSqrt z / z)
      (-analyticLowerSqrt u / (2 * u ^ 2)) u := by
    have hraw := hs.div (hasDerivAt_id u) hu0
    have heq : (analyticLowerSqrt u / (2 * u) * u - analyticLowerSqrt u * 1) / u ^ 2 =
        -analyticLowerSqrt u / (2 * u ^ 2) := by
      field_simp [hu0]
      ring
    change HasDerivAt (analyticLowerSqrt / id) (-analyticLowerSqrt u / (2 * u ^ 2)) u
    exact hraw.congr_deriv heq
  have hInv : HasDerivAt (fun z : ℂ => 1 / z) (-1 / u ^ 2) u := by
    have hraw := (hasDerivAt_const u (1 : ℂ)).div (hasDerivAt_id u) hu0
    have heq : (0 * u - 1 * 1) / u ^ 2 = (-1 / u ^ 2 : ℂ) := by ring
    change HasDerivAt ((fun _ : ℂ => (1 : ℂ)) / id) (-1 / u ^ 2) u
    exact hraw.congr_deriv heq
  have hraw := (((hasDerivAt_const u (-(q : ℂ))).add (hA.const_mul a)).add
      (((hA.mul hl).add hB).const_mul b)).sub hInv
  apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
  · dsimp [analyticPhaseCoeffDeriv2]
    field_simp [hu0]
    ring_nf
  · filter_upwards [] with z
    dsimp [analyticPhaseCoeffDeriv]

/-- On the slit plane, the second derivative of `analyticPhaseCoeff q a b` is
`analyticPhaseCoeffDeriv2 a b u`. -/
theorem iteratedDeriv_two_analyticPhaseCoeff {q : ℝ} {a b u : ℂ}
    (hu : u ∈ Complex.slitPlane) :
    iteratedDeriv 2 (analyticPhaseCoeff q a b) u = analyticPhaseCoeffDeriv2 a b u := by
  have hderiv : deriv (analyticPhaseCoeff q a b) =ᶠ[𝓝 u] analyticPhaseCoeffDeriv q a b := by
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds hu] with z hz
    exact (hasDerivAt_analyticPhaseCoeff hz).deriv
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one, hderiv.deriv_eq]
  exact (hasDerivAt_analyticPhaseCoeffDeriv hu).deriv

/-- In the open lower half-plane the scale-`Λ` phase is the holomorphic
phase with coefficients `π` and `π / Λ`. -/
theorem saddlePhaseAtLambda_eq_analytic_of_im_neg (Λ q : ℝ) {u : ℂ} (hu : u.im < 0) :
    saddlePhaseAtLambda Λ q u =
      analyticPhaseCoeff q (Real.pi : ℂ) ((Real.pi / Λ : ℝ) : ℂ) u := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  rw [saddlePhaseAtLambda, analyticPhaseCoeff, lowerLog_eq_log_of_im_neg hu,
    lowerSqrt_eq_sqrt_of_im_neg hu, sqrt_eq_exp hu0, two_mul_saddleKappa_div]
  simp only [saddleKappa_eq, analyticLowerSqrt]
  push_cast
  ring

/-- In the open lower half-plane, the second derivative of the scale-`Λ` phase is
`analyticPhaseCoeffDeriv2 π (π / Λ) u`. -/
theorem iteratedDeriv_two_saddlePhaseAtLambda_of_im_neg (Λ q : ℝ) {u : ℂ} (hu : u.im < 0) :
    iteratedDeriv 2 (saddlePhaseAtLambda Λ q) u =
      analyticPhaseCoeffDeriv2 (Real.pi : ℂ) ((Real.pi / Λ : ℝ) : ℂ) u := by
  have hslit : u ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr hu.ne)
  have heq : saddlePhaseAtLambda Λ q =ᶠ[𝓝 u]
      analyticPhaseCoeff q (Real.pi : ℂ) ((Real.pi / Λ : ℝ) : ℂ) := by
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hu] with z hz
    exact saddlePhaseAtLambda_eq_analytic_of_im_neg Λ q hz
  rw [heq.iteratedDeriv_eq 2]
  exact iteratedDeriv_two_analyticPhaseCoeff hslit

/-- For `r > 0` and `0 < α < π/2`, the point `r² e^{-2iα}` lies in the open lower
half-plane. -/
theorem im_ofReal_sq_mul_exp_neg_two_mul_I_neg {r α : ℝ} (hr : 0 < r)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))).im < 0 := by
  rcases hα with ⟨hα0, hαtop⟩
  have hsin : 0 < Real.sin (2 * α) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsneg : Real.sin (-2 * α) = -Real.sin (2 * α) := by
    rw [show -2 * α = -(2 * α) by ring, Real.sin_neg]
  have hexp : Complex.I * ((-2 * α : ℝ) : ℂ) = ((-2 * α : ℝ) : ℂ) * Complex.I := by ring
  rw [hexp]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [hsneg]
  nlinarith [mul_pos (sq_pos_of_pos hr) hsin]

/-- Exact `u² h''(u)` at an open lower-circle point, scale `Λ`. -/
theorem saddlePhaseAtLambda_hessian_sq_exp_neg_two_mul_I (Λ q : ℝ) {r α : ℝ} (hr : 0 < r)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))) ^ 2 *
        iteratedDeriv 2 (saddlePhaseAtLambda Λ q)
          (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))) =
      explicitSaddleHessianAtLambda Λ r α := by
  set u : ℂ := ((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ)) with hu
  have huim : u.im < 0 := im_ofReal_sq_mul_exp_neg_two_mul_I_neg hr hα
  have hu0 : u ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hr.ne')) (Complex.exp_ne_zero _)
  have hs : analyticLowerSqrt u =
      (r : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ) / 2) := by
    rw [analyticLowerSqrt, ← sqrt_eq_exp hu0, ← lowerSqrt_eq_sqrt_of_im_neg huim]
    exact lowerSqrt_sq_mul_exp_I_mul hr (by linarith [hα.2]) (by linarith [hα.1])
  have hl : Complex.log u =
      ((2 * Real.log r : ℝ) : ℂ) + Complex.I * ((-2 * α : ℝ) : ℂ) := by
    rw [← lowerLog_eq_log_of_im_neg huim]
    exact lowerLog_sq_mul_exp_I_mul hr (by linarith [hα.2]) (by linarith [hα.1])
  rw [iteratedDeriv_two_saddlePhaseAtLambda_of_im_neg Λ q huim, analyticPhaseCoeffDeriv2]
  field_simp [hu0]
  rw [hs, hl, explicitSaddleHessianAtLambda]
  have hexp : Complex.I * ((-2 * α : ℝ) : ℂ) / 2 = ((-α : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp]
  push_cast
  ring_nf

/-- For `Λ ≥ 0`, on the open branch `0 < α < π/2`, the Hessian at the saddle point is
`D = 1 - (π r e^{-iα} / 4) (1 + (2 log r - 2 i α) / Λ)`. -/
theorem saddleHessianAtLambda_eq_explicit {Λ α : ℝ} (hΛ : 0 ≤ Λ)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    saddleHessianAtLambda Λ α =
      explicitSaddleHessianAtLambda Λ (saddleRadiusAtLambda Λ α) α := by
  have hr := saddleRadiusAtLambda_pos hΛ ⟨hα.1.le, hα.2.le⟩
  have hpt : saddlePointAtLambda Λ α =
      ((saddleRadiusAtLambda Λ α ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ)) := by
    rw [saddlePointAtLambda]
    congr 2
    push_cast
    ring
  rw [saddleHessianAtLambda, hpt]
  exact saddlePhaseAtLambda_hessian_sq_exp_neg_two_mul_I Λ _ hr hα

/-- Exact real part of the Hessian on the open branch, scale `Λ > 0`. -/
theorem saddleHessianAtLambda_re {Λ α : ℝ} (hΛ : 0 < Λ)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (saddleHessianAtLambda Λ α).re =
      Real.sin α ^ 2 + Real.pi * saddleRadiusAtLambda Λ α / (2 * Λ) *
        (Real.cos α - α * Real.cos (2 * α) / Real.sin α) := by
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  rw [saddleHessianAtLambda_eq_explicit hΛ.le hα, explicitSaddleHessianAtLambda_re]
  exact hessian_real_algebra Λ (saddleQAtLambda Λ α) _ _ hΛ.ne'
    (Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))).ne'
    (saddle_real_relation_atLambda hΛ hαcc)
    (by rw [saddleQAtLambda_mul_radius_sq hΛ hαcc, sinRatio_of_ne hα.1.ne'])

/-- Exact imaginary part of the Hessian on the open branch, scale `Λ ≥ 0`. -/
theorem saddleHessianAtLambda_im {Λ α : ℝ} (hΛ : 0 ≤ Λ)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (saddleHessianAtLambda Λ α).im =
      Real.pi * saddleRadiusAtLambda Λ α / 4 *
        ((1 + 2 * Real.log (saddleRadiusAtLambda Λ α) / Λ) * Real.sin α +
          2 * α * Real.cos α / Λ) := by
  rw [saddleHessianAtLambda_eq_explicit hΛ hα, explicitSaddleHessianAtLambda_im]

end HessianFormula

/-! ### Bounds on the Hessian -/

section HessianBounds

/-- For `Λ ≥ 4π`, on the open branch `0 < α < π/2`, `sin² α ≤ Re D ≤ 2 sin² α`. -/
theorem saddleHessianAtLambda_re_bounds {Λ α : ℝ} (hΛ : 4 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin α ^ 2 ≤ (saddleHessianAtLambda Λ α).re ∧
      (saddleHessianAtLambda Λ α).re ≤ 2 * Real.sin α ^ 2 := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hspos : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  have hr0 := (saddleRadiusAtLambda_pos hΛpos.le hαcc).le
  have hr2 := saddleRadiusAtLambda_le_two hΛpos.le hαcc
  have hn0 := hessianCorrectionNumerator_nonneg hαcc
  have hn4 := hessianCorrectionNumerator_le hαcc
  have heq : Real.cos α - α * Real.cos (2 * α) / Real.sin α =
      (Real.sin α * Real.cos α - α * Real.cos (2 * α)) / Real.sin α := by
    field_simp [hspos.ne']
  have hcorr0 : 0 ≤ Real.pi * saddleRadiusAtLambda Λ α / (2 * Λ) *
      (Real.cos α - α * Real.cos (2 * α) / Real.sin α) := by
    have hbracket : 0 ≤ Real.cos α - α * Real.cos (2 * α) / Real.sin α := by
      rw [heq]
      exact div_nonneg hn0 hspos.le
    positivity
  have hcorrle : Real.pi * saddleRadiusAtLambda Λ α / (2 * Λ) *
      (Real.cos α - α * Real.cos (2 * α) / Real.sin α) ≤ Real.sin α ^ 2 := by
    have hbracket : Real.cos α - α * Real.cos (2 * α) / Real.sin α ≤
        4 * Real.sin α ^ 2 := by
      rw [heq]
      apply (div_le_iff₀ hspos).2
      nlinarith
    have hcoef : Real.pi * saddleRadiusAtLambda Λ α / (2 * Λ) ≤ 1 / 4 := by
      apply (div_le_iff₀ (show 0 < 2 * Λ by positivity)).2
      nlinarith [Real.pi_pos]
    calc
      _ ≤ (Real.pi * saddleRadiusAtLambda Λ α / (2 * Λ)) * (4 * Real.sin α ^ 2) :=
        mul_le_mul_of_nonneg_left hbracket (by positivity)
      _ ≤ (1 / 4 : ℝ) * (4 * Real.sin α ^ 2) := by gcongr
      _ = Real.sin α ^ 2 := by ring
  rw [saddleHessianAtLambda_re hΛpos hα]
  constructor <;> nlinarith

/-- Imaginary Hessian formula with `log r` eliminated by the real saddle
relation, scale `Λ > 0`. -/
theorem saddleHessianAtLambda_im_rearranged {Λ α : ℝ} (hΛ : 0 < Λ)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (saddleHessianAtLambda Λ α).im =
      (saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 + 1) / 2 *
          Real.sin α * Real.cos α +
        (Real.pi * saddleRadiusAtLambda Λ α / (2 * Λ)) * (α * Real.cos α - Real.sin α) := by
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hre := saddle_real_relation_atLambda hΛ hαcc
  have hr := saddleRadiusAtLambda_pos hΛ.le hαcc
  have hA :
      1 + 2 * Real.log (saddleRadiusAtLambda Λ α) / Λ =
          2 * (saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 + 1) * Real.cos α /
            (Real.pi * saddleRadiusAtLambda Λ α) - 2 / Λ := by
    field_simp [hΛ.ne', hr.ne', Real.pi_ne_zero] at hre ⊢
    nlinarith
  rw [saddleHessianAtLambda_im hΛ.le hα, hA]
  field_simp [hΛ.ne', hr.ne', Real.pi_ne_zero]
  ring

/-- For `Λ ≥ 24π` and `0 < α < π/2`, the correction term of `Im D` is at most `sin α / 8`
in absolute value. -/
theorem abs_saddleHessianAtLambda_im_correction_le {Λ α : ℝ} (hΛ : 24 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Real.pi * saddleRadiusAtLambda Λ α / (2 * Λ) * (α * Real.cos α - Real.sin α)| ≤
      (1 / 8 : ℝ) * Real.sin α := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hs : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  have hc0 : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩
  have hc1 := Real.cos_le_one α
  have ha : α ≤ 2 * Real.sin α := by
    have := half_mul_le_sin hαcc
    linarith
  have hr0 := (saddleRadiusAtLambda_pos hΛpos.le hαcc).le
  have hr2 := saddleRadiusAtLambda_le_two hΛpos.le hαcc
  have hcoef : Real.pi * saddleRadiusAtLambda Λ α / (2 * Λ) ≤ 1 / 24 := by
    apply (div_le_iff₀ (show 0 < 2 * Λ by positivity)).2
    nlinarith [Real.pi_pos]
  have hcoef0 : 0 ≤ Real.pi * saddleRadiusAtLambda Λ α / (2 * Λ) := by positivity
  have hinner : |α * Real.cos α - Real.sin α| ≤ 3 * Real.sin α := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hα.1.le hc0, mul_le_mul_of_nonneg_left hc1 hα.1.le]
  rw [abs_mul, abs_of_nonneg hcoef0]
  exact (mul_le_mul hcoef hinner (abs_nonneg _) (by norm_num)).trans_eq (by ring)

/-- `|Im D| ≤ 2 sin α` on the open branch, scale `Λ ≥ 24π`. -/
theorem abs_saddleHessianAtLambda_im_le_two_sin {Λ α : ℝ} (hΛ : 24 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    |(saddleHessianAtLambda Λ α).im| ≤ 2 * Real.sin α := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hs : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  have hc0 : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩
  have hc1 := Real.cos_le_one α
  have hqr1 := one_le_saddleQAtLambda_mul_radius_sq hΛpos hαcc
  have hqr2' := saddleQAtLambda_mul_radius_sq_le hΛpos hαcc
  have hfrac : 2 * Real.pi / Λ ≤ 1 := (div_le_one hΛpos).2 (by linarith [Real.pi_pos])
  have hqr2 : saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 ≤ 2 := by linarith
  set A := (saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 + 1) / 2 *
      Real.sin α * Real.cos α with hAdef
  set B := Real.pi * saddleRadiusAtLambda Λ α / (2 * Λ) *
      (α * Real.cos α - Real.sin α)
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg (by linarith) hs.le) hc0
  have hAle : A ≤ (3 / 2 : ℝ) * Real.sin α := by
    rw [hAdef]
    nlinarith [mul_nonneg hs.le hc0, mul_le_mul_of_nonneg_left hc1 hs.le]
  have hB : |B| ≤ (1 / 8 : ℝ) * Real.sin α := abs_saddleHessianAtLambda_im_correction_le hΛ hα
  rw [saddleHessianAtLambda_im_rearranged hΛpos hα]
  calc
    |A + B| ≤ |A| + |B| := abs_add_le A B
    _ = A + |B| := by rw [abs_of_nonneg hA0]
    _ ≤ (3 / 2 : ℝ) * Real.sin α + (1 / 8 : ℝ) * Real.sin α := add_le_add hAle hB
    _ ≤ 2 * Real.sin α := by linarith

/-- For `Λ ≥ 24π`, on the open branch `0 < α < π/2`, `(3/8) sin α ≤ |D| ≤ 4 sin α`. -/
theorem saddleHessianAtLambda_norm_bounds {Λ α : ℝ} (hΛ : 24 * Real.pi ≤ Λ)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (3 / 8 : ℝ) * Real.sin α ≤ ‖saddleHessianAtLambda Λ α‖ ∧
      ‖saddleHessianAtLambda Λ α‖ ≤ 4 * Real.sin α := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  set D := saddleHessianAtLambda Λ α with hD
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hs : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  have hs1 := Real.sin_le_one α
  have hc0 : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩
  have hre := saddleHessianAtLambda_re_bounds (by linarith [Real.pi_pos] : 4 * Real.pi ≤ Λ) hα
  have himabs := abs_saddleHessianAtLambda_im_le_two_sin hΛ hα
  constructor
  · by_cases hsmall : Real.sin α < 1 / 2
    · have htrig := Real.sin_sq_add_cos_sq α
      have hc : 1 / 2 ≤ Real.cos α := by nlinarith [sq_nonneg (Real.cos α)]
      have hqr := one_le_saddleQAtLambda_mul_radius_sq hΛpos hαcc
      have hcorr := (abs_le.1 (abs_saddleHessianAtLambda_im_correction_le hΛ hα)).1
      have him : (3 / 8 : ℝ) * Real.sin α ≤ D.im := by
        rw [hD, saddleHessianAtLambda_im_rearranged hΛpos hα]
        have hmain : (1 / 2 : ℝ) * Real.sin α ≤
            (saddleQAtLambda Λ α * saddleRadiusAtLambda Λ α ^ 2 + 1) / 2 *
              Real.sin α * Real.cos α := by
          nlinarith [mul_nonneg hs.le hc0]
        nlinarith
      exact him.trans (Complex.im_le_norm D)
    · have hlarge : 1 / 2 ≤ Real.sin α := le_of_not_gt hsmall
      have hrenorm := Complex.re_le_norm D
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hlarge)]
  · have hnorm := Complex.norm_le_abs_re_add_abs_im D
    have hre0 : 0 ≤ D.re := le_trans (sq_nonneg _) hre.1
    rw [abs_of_nonneg hre0] at hnorm
    have hresin : D.re ≤ 2 * Real.sin α := by
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs1)]
    linarith

end HessianBounds

/-! ### Dedekind-scale specializations -/

section DedekindSpecialization

variable (K : Type) [Field K] [NumberField K]

/-- For every sufficiently large degree `d`, `24π ≤ dedekindScaleLambda K d`. -/
theorem eventually_twentyfour_pi_le_dedekindScaleLambda :
    ∃ D : ℕ, ∀ d ≥ D, 24 * Real.pi ≤ dedekindScaleLambda K d := by
  rcases eventually_log_le_dedekindScaleLambda K with ⟨D₁, hD₁⟩
  obtain ⟨D₂, hD₂⟩ := exists_nat_ge (Real.exp (24 * Real.pi))
  refine ⟨max D₁ D₂, fun d hd => ?_⟩
  have hexp : Real.exp (24 * Real.pi) ≤ (d : ℝ) :=
    hD₂.trans (by exact_mod_cast (le_max_right _ _).trans hd)
  exact ((Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hexp)).2 hexp).trans
    (hD₁ d ((le_max_left _ _).trans hd))

/-- The Dedekind saddle radius is at most `2`. -/
theorem dedekindSaddleRadius_le_two (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) : dedekindSaddleRadius K d α ≤ 2 := by
  simpa [dedekindSaddleRadius] using
    saddleRadiusAtLambda_le_two (dedekindScaleLambda_pos K d hd).le hα

/-- The Dedekind saddle level and radius satisfy `1 ≤ q r²`. -/
theorem one_le_dedekindSaddleQ_mul_radius_sq (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    1 ≤ dedekindSaddleQ K d α * dedekindSaddleRadius K d α ^ 2 := by
  simpa [dedekindSaddleQ, dedekindSaddleRadius] using
    one_le_saddleQAtLambda_mul_radius_sq (dedekindScaleLambda_pos K d hd) hα

/-- The Dedekind saddle level and radius satisfy `q r² ≤ 1 + 2π / Λ` at the Dedekind
scale `Λ`. -/
theorem dedekindSaddleQ_mul_radius_sq_le (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    dedekindSaddleQ K d α * dedekindSaddleRadius K d α ^ 2 ≤
      1 + 2 * Real.pi / dedekindScaleLambda K d := by
  simpa [dedekindSaddleQ, dedekindSaddleRadius] using
    saddleQAtLambda_mul_radius_sq_le (dedekindScaleLambda_pos K d hd) hα

/-- If the Dedekind scale is at least `2π`, the Dedekind saddle radius and level satisfy
`1 / √q ≤ r ≤ √2 / √q`. -/
theorem dedekindSaddleRadius_level_comparison (d : ℕ)
    (hΛ : 2 * Real.pi ≤ dedekindScaleLambda K d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    1 / Real.sqrt (dedekindSaddleQ K d α) ≤ dedekindSaddleRadius K d α ∧
      dedekindSaddleRadius K d α ≤
        Real.sqrt 2 / Real.sqrt (dedekindSaddleQ K d α) := by
  simpa [dedekindSaddleQ, dedekindSaddleRadius] using
    saddleRadiusAtLambda_level_comparison hΛ hα

/-- If the Dedekind scale `Λ` is at least `2 (1 + log 2)` and the Dedekind saddle level is at
most `T > 0`, where `log T ≤ 3Λ / 4`, then `π r / 16 ≤ cos α ≤ π r / 2`. -/
theorem dedekindSaddleCos_radius_comparison (d : ℕ) {T α : ℝ}
    (hΛ : 2 * (1 + Real.log 2) ≤ dedekindScaleLambda K d)
    (hT : 0 < T) (hlogT : Real.log T ≤ 3 * dedekindScaleLambda K d / 4)
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) (hqT : dedekindSaddleQ K d α ≤ T) :
    Real.pi * dedekindSaddleRadius K d α / 16 ≤ Real.cos α ∧
      Real.cos α ≤ Real.pi * dedekindSaddleRadius K d α / 2 := by
  simpa [dedekindSaddleQ, dedekindSaddleRadius] using
    saddleCosAtLambda_radius_comparison hΛ hT hlogT hα hqT

/-- If the Dedekind scale is at least `2π`, the Dedekind edge level is at most `2`. -/
theorem dedekindEdgeQ_le_two (d : ℕ)
    (hΛ : 2 * Real.pi ≤ dedekindScaleLambda K d) : dedekindEdgeQ K d ≤ 2 := by
  simpa [dedekindEdgeQ, dedekindSaddleQ, edgeQAtLambda] using
    edgeQAtLambda_le_two hΛ

/-- If the Dedekind scale is at least `24π`, then `α² / 50 ≤ q(α) - q_e` for the Dedekind
saddle and edge levels. -/
theorem dedekindSaddleQ_sub_edge_lower (d : ℕ)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    α ^ 2 / 50 ≤ dedekindSaddleQ K d α - dedekindEdgeQ K d := by
  simpa [dedekindSaddleQ, dedekindEdgeQ, edgeQAtLambda] using
    saddleQAtLambda_sub_edge_lower hΛ hα

/-- If the Dedekind scale is at least `24π`, then `q(α) - q_e ≤ 6 α²` for `α ∈ [0, 1/2]`,
for the Dedekind saddle and edge levels. -/
theorem dedekindSaddleQ_sub_edge_upper (d : ℕ)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    dedekindSaddleQ K d α - dedekindEdgeQ K d ≤ 6 * α ^ 2 := by
  simpa [dedekindSaddleQ, dedekindEdgeQ, edgeQAtLambda] using
    saddleQAtLambda_sub_edge_upper hΛ hα

/-- If the Dedekind scale is at least `24π`, the second `z`-derivative of the real phase on
each saddle circle is at most `-3` throughout `0 < z < 1`. -/
theorem dedekindCircleRealPhaseZSecond_le_neg_three (d : ℕ)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d) {α z : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) (hz : z ∈ Set.Ioo 0 1) :
    circleRealPhaseZSecondAtLambda (dedekindScaleLambda K d) α z ≤ -3 :=
  circleRealPhaseZSecondAtLambda_le_neg_three hΛ hα hz

/-- If the Dedekind scale is at least `24π`, the real part of the Dedekind phase on the saddle
circle of angle `α ∈ (0, π/2]` drops by at least `(3/2) (cos β - cos α)²` at angle `β`. -/
theorem dedekindSaddlePhase_circle_quadratic_gap (d : ℕ)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d) {α β : ℝ}
    (hα : α ∈ Set.Ioc 0 (Real.pi / 2)) (hβ : β ∈ Set.Icc 0 (Real.pi / 2)) :
    (3 / 2 : ℝ) * (Real.cos β - Real.cos α) ^ 2 ≤
      (dedekindSaddlePhase K d (dedekindSaddleQ K d α)
        ((((dedekindSaddleRadius K d α) ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((-2 * α : ℝ) : ℂ))))).re -
      (dedekindSaddlePhase K d (dedekindSaddleQ K d α)
        ((((dedekindSaddleRadius K d α) ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((-2 * β : ℝ) : ℂ))))).re := by
  simpa [dedekindSaddlePhase, dedekindSaddleQ, dedekindSaddleRadius] using
    saddlePhaseAtLambda_circle_quadratic_gap hΛ hα hβ

/-- At an angle-parametrized Dedekind saddle, the field-indexed Hessian is
exactly the abstract Hessian at the Dedekind logarithmic scale. -/
theorem dedekindSaddleHessian_saddleQ (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    dedekindSaddleHessian K d (dedekindSaddleQ K d α) =
      saddleHessianAtLambda (dedekindScaleLambda K d) α := by
  rw [dedekindSaddleHessian, dedekindSaddle, dedekindSaddleAngle_saddleQ K d hd hα]
  rfl

/-- On the open branch `0 < α < π/2`, the Dedekind Hessian at the level of angle `α` is the
explicit Hessian at the Dedekind scale and radius. -/
theorem dedekindSaddleHessian_eq_explicit (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    dedekindSaddleHessian K d (dedekindSaddleQ K d α) =
      explicitSaddleHessianAtLambda (dedekindScaleLambda K d)
        (dedekindSaddleRadius K d α) α := by
  rw [dedekindSaddleHessian_saddleQ K d hd ⟨hα.1.le, hα.2.le⟩]
  simpa [dedekindSaddleRadius] using
    saddleHessianAtLambda_eq_explicit (dedekindScaleLambda_pos K d hd).le hα

/-- If the Dedekind scale is at least `4π`, on the open branch the Dedekind Hessian satisfies
`sin² α ≤ Re D ≤ 2 sin² α`. -/
theorem dedekindSaddleHessian_re_bounds (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 4 * Real.pi ≤ dedekindScaleLambda K d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin α ^ 2 ≤
        (dedekindSaddleHessian K d (dedekindSaddleQ K d α)).re ∧
      (dedekindSaddleHessian K d (dedekindSaddleQ K d α)).re ≤
        2 * Real.sin α ^ 2 := by
  rw [dedekindSaddleHessian_saddleQ K d hd ⟨hα.1.le, hα.2.le⟩]
  exact saddleHessianAtLambda_re_bounds hΛ hα

/-- If the Dedekind scale is at least `24π`, on the open branch the Dedekind Hessian satisfies
`(3/8) sin α ≤ |D| ≤ 4 sin α`. -/
theorem dedekindSaddleHessian_norm_bounds (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (3 / 8 : ℝ) * Real.sin α ≤
        ‖dedekindSaddleHessian K d (dedekindSaddleQ K d α)‖ ∧
      ‖dedekindSaddleHessian K d (dedekindSaddleQ K d α)‖ ≤
        4 * Real.sin α := by
  rw [dedekindSaddleHessian_saddleQ K d hd ⟨hα.1.le, hα.2.le⟩]
  exact saddleHessianAtLambda_norm_bounds hΛ hα

end DedekindSpecialization

/-! ### The cosine-comparison hypothesis at the Riemann scale -/

/-- If `4 (1 + log (2π)) ≤ scaleLambda d`, then `log (scaleT d) ≤ 3 scaleLambda d / 4`. -/
theorem log_scaleT_le_three_mul_scaleLambda_div_four (d : ℕ) (hd : 1 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d) :
    Real.log (scaleT d) ≤ 3 * scaleLambda d / 4 := by
  have hT : 0 < scaleT d := lt_trans (by positivity) (scaleT_gt_base d hd)
  have hcoord := scaleLambda_div_two d
  rw [Real.log_div hT.ne' (by positivity)] at hcoord
  linarith

end RiemannJensen
