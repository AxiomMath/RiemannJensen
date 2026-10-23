module

public import RiemannJensen.Analysis.SaddleGeometry
public import RiemannJensen.Analysis.SaddleBounds
public import RiemannJensen.Analysis.SaddleInverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Quadratic separation of the saddle coordinate from the edge -/

@[expose] public section

namespace RiemannJensen

/-- Exact identity relating the reciprocal saddle radius at angle `α` to its
value at the edge, in the reciprocal-radius coordinate. -/
theorem saddleRadius_inv_radial_difference (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    let x := (saddleRadius d α)⁻¹
    let x₀ := (saddleRadius d 0)⁻¹
    (2 * scaleLambda d / Real.pi) * (x * Real.cos α - x₀) +
        (alphaCot α - 1) + Real.log (x / x₀) = 0 := by
  dsimp only
  have hαfull : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  have h0full : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by positivity⟩
  have hrα := saddleRadius_pos_and_eq d hd hαfull
  have hr0 := saddleRadius_pos_and_eq d hd h0full
  have hlog :
      Real.log ((saddleRadius d α)⁻¹ / (saddleRadius d 0)⁻¹) =
        -Real.log (saddleRadius d α) + Real.log (saddleRadius d 0) := by
    rw [Real.log_div (inv_ne_zero hrα.1.ne') (inv_ne_zero hr0.1.ne'),
      Real.log_inv, Real.log_inv]
    ring
  rw [radialEquation, saddleRadialCoeff, saddleRadialConst] at hrα hr0
  rw [hlog]
  simp only [Real.cos_zero, alphaCot_zero] at hr0
  field_simp [Real.pi_ne_zero, hrα.1.ne', hr0.1.ne'] at hrα hr0 ⊢
  nlinarith [hrα.2, hr0.2]

/-- At the edge, the radial saddle lies outside the unit circle. -/
theorem one_le_saddleRadius_zero (d : ℕ) (hd : 1 ≤ d) : 1 ≤ saddleRadius d 0 := by
  have h0full : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by positivity⟩
  have hr := saddleRadius_pos_and_eq d hd h0full
  rw [radialEquation, saddleRadialCoeff, saddleRadialConst,
    Real.cos_zero, alphaCot_zero] at hr
  by_contra! hrlt
  have hlog : Real.log (saddleRadius d 0) < 0 :=
    Real.log_neg hr.1 hrlt
  have hΛ := scaleLambda_pos d hd
  have hden : (Real.pi / 2) * saddleRadius d 0 < 2 := by
    calc
      (Real.pi / 2) * saddleRadius d 0 <
          (Real.pi / 2) * 1 :=
        mul_lt_mul_of_pos_left hrlt (by positivity)
      _ ≤ 2 := by simpa using Real.pi_div_two_le_two
  have hleft :
      scaleLambda d / 2 <
        scaleLambda d / ((Real.pi / 2) * saddleRadius d 0) :=
    div_lt_div_of_pos_left hΛ (mul_pos (by positivity) hr.1) hden
  have heq :
      scaleLambda d / ((Real.pi / 2) * saddleRadius d 0) =
        scaleLambda d / 2 + Real.log (saddleRadius d 0) := by
    calc
      _ = scaleLambda d * 1 / (Real.pi / 2) /
          saddleRadius d 0 := by
            field_simp [Real.pi_ne_zero, hr.1.ne']
      _ = _ := by nlinarith [hr.2]
  nlinarith

/-- The reciprocal edge radius is at least one half. -/
theorem half_le_saddleRadius_zero_inv (d : ℕ) (hd : 1 ≤ d) :
    1 / 2 ≤ (saddleRadius d 0)⁻¹ := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hr0 := saddleRadius_pos_of_mem_Icc d hd h0
  have hr0two : saddleRadius d 0 ≤ 2 := by
    simpa using saddleRadius_mul_sinRatio_le_two d hd h0
  rw [inv_eq_one_div]
  exact (le_div_iff₀ hr0).2 (by nlinarith)

/-- The reciprocal edge radius is at most one. -/
theorem saddleRadius_zero_inv_le_one (d : ℕ) (hd : 1 ≤ d) :
    (saddleRadius d 0)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_saddleRadius_zero d hd)

/-- The sine ratio is at least one on `[0, π / 2]`. -/
theorem one_le_sinRatio_of_mem {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    1 ≤ sinRatio α := by
  rcases hα.1.eq_or_lt with rfl | hpos
  · simp
  · exact (one_lt_sinRatio hpos hα.2).le

/-- A scaled cosine-defect bound in the reciprocal-radius coordinate forces a
quadratic separation. -/
theorem sq_div_fifty_le_of_mul_one_sub_cos_le {a x x₀ α : ℝ} (ha48 : 48 ≤ a)
    (hx0half : 1 / 2 ≤ x₀) (hxx0 : x₀ ≤ x) (hα : α ∈ Set.Icc 0 (Real.pi / 2))
    (hmain : a * x₀ * (1 - Real.cos α) ≤ (a + x₀⁻¹) * (x - x₀)) :
    α ^ 2 / 50 ≤ x - x₀ := by
  have ha : 0 < a := by linarith
  have hx0 : 0 < x₀ := by linarith
  have hx0inv : x₀⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hx0 (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hden : a + x₀⁻¹ ≤ (25 / 24 : ℝ) * a := by
    nlinarith
  have hupper := mul_le_mul_of_nonneg_right hden (sub_nonneg.mpr hxx0)
  have hcosquad := Real.cos_le_one_sub_mul_cos_sq
    ((abs_of_nonneg hα.1).le.trans (by linarith [hα.2, Real.pi_pos]))
  have hquad : (2 / Real.pi ^ 2) * α ^ 2 ≤ 1 - Real.cos α := by
    linarith
  have hlow1 := mul_le_mul_of_nonneg_left hx0half
    (mul_nonneg ha.le (sub_nonneg.mpr (Real.cos_le_one α)))
  have hlow2 := mul_le_mul_of_nonneg_left hquad
    (mul_nonneg ha.le (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hpi2 : Real.pi ^ 2 ≤ 16 := by
    nlinarith [Real.pi_pos, Real.pi_le_four]
  have hcombine :
      a / Real.pi ^ 2 * α ^ 2 ≤ (25 / 24 : ℝ) * a * (x - x₀) := by
    calc
      a / Real.pi ^ 2 * α ^ 2 =
          a * (1 / 2 : ℝ) * ((2 / Real.pi ^ 2) * α ^ 2) := by ring
      _ ≤ a * (1 / 2 : ℝ) * (1 - Real.cos α) := hlow2
      _ ≤ a * x₀ * (1 - Real.cos α) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hlow1
      _ ≤ (a + x₀⁻¹) * (x - x₀) := hmain
      _ ≤ (25 / 24 : ℝ) * a * (x - x₀) := hupper
  have hcancel : α ^ 2 / Real.pi ^ 2 ≤
      (25 / 24 : ℝ) * (x - x₀) := by
    apply le_of_mul_le_mul_left _ ha
    calc
      a * (α ^ 2 / Real.pi ^ 2) =
          a / Real.pi ^ 2 * α ^ 2 := by ring
      _ ≤ (25 / 24 : ℝ) * a * (x - x₀) := hcombine
      _ = a * ((25 / 24 : ℝ) * (x - x₀)) := by ring
  have hweak : α ^ 2 / 16 ≤ α ^ 2 / Real.pi ^ 2 := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 16) (by positivity)).2
    exact mul_le_mul_of_nonneg_left hpi2 (sq_nonneg α)
  nlinarith

/-- The reciprocal saddle radius is smallest at the edge `α = 0`. -/
theorem saddleRadius_zero_inv_le_inv (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    (saddleRadius d 0)⁻¹ ≤ (saddleRadius d α)⁻¹ :=
  (saddleRadius_inv_strictMonoOn d hd).monotoneOn ⟨le_rfl, by positivity⟩ hα hα.1

/-- The reciprocal saddle radius moves at least quadratically away from its
edge value, uniformly in the scale. -/
theorem saddleRadius_inv_sub_edge_lower (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d) {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    α ^ 2 / 50 ≤ (saddleRadius d α)⁻¹ - (saddleRadius d 0)⁻¹ := by
  let x := (saddleRadius d α)⁻¹
  let x₀ := (saddleRadius d 0)⁻¹
  let a := 2 * scaleLambda d / Real.pi
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hx : 0 < x := inv_pos.2 (saddleRadius_pos_of_mem_Icc d hd hα)
  have hx0 : 0 < x₀ := inv_pos.2 (saddleRadius_pos_of_mem_Icc d hd h0)
  have hxx0 : x₀ ≤ x := saddleRadius_zero_inv_le_inv d hd hα
  have hdx : 0 ≤ x - x₀ := sub_nonneg.mpr hxx0
  have ha48 : 48 ≤ a := (le_div_iff₀ Real.pi_pos).2 (by linarith)
  have ha : 0 < a := by linarith
  have hcot : alphaCot α ≤ 1 := alphaCot_le_one_of_mem hα
  have hid := saddleRadius_inv_radial_difference d hd hα
  dsimp [x, x₀, a] at hid ⊢
  have hlog' : Real.log (x / x₀) ≤ x₀⁻¹ * (x - x₀) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx hx0)
    rwa [div_sub_one hx0.ne', div_eq_inv_mul (x - x₀)] at h
  have hmain : a * x₀ * (1 - Real.cos α) ≤
      (a + x₀⁻¹) * (x - x₀) := by
    have hleft : a * Real.cos α * (x - x₀) + Real.log (x / x₀) =
        a * x₀ * (1 - Real.cos α) + (1 - alphaCot α) := by
      dsimp [a, x, x₀] at *
      nlinarith
    have hupper : a * Real.cos α * (x - x₀) + Real.log (x / x₀) ≤
        (a + x₀⁻¹) * (x - x₀) := by
      have := mul_le_mul_of_nonneg_left (Real.cos_le_one α) (mul_nonneg ha.le hdx)
      nlinarith
    nlinarith
  exact sq_div_fifty_le_of_mul_one_sub_cos_le ha48
    (half_le_saddleRadius_zero_inv d hd) hxx0 hα hmain

/-- Uniform quadratic lower separation of the saddle level from the edge. -/
theorem saddleQ_sub_edge_lower (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    α ^ 2 / 50 ≤ saddleQ d α - edgeQ d := by
  let x := (saddleRadius d α)⁻¹
  let x₀ := (saddleRadius d 0)⁻¹
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hx0 : 0 < x₀ := inv_pos.2 (saddleRadius_pos_of_mem_Icc d hd h0)
  have hxx0 : x₀ ≤ x := saddleRadius_zero_inv_le_inv d hd hα
  have hx0half : (1 / 2 : ℝ) ≤ x₀ := half_le_saddleRadius_zero_inv d hd
  have hprod : x₀ ≤ sinRatio α * x := (one_mul x₀).ge.trans
    (mul_le_mul (one_le_sinRatio_of_mem hα) hxx0 hx0.le (sinRatio_pos_of_mem hα).le)
  have hcoef : 0 ≤ Real.pi / scaleLambda d :=
    (div_pos Real.pi_pos (scaleLambda_pos d hd)).le
  have hsq : x - x₀ ≤ x ^ 2 - x₀ ^ 2 := by
    have hsum : 1 ≤ x + x₀ := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hxx0) (sub_nonneg.mpr hsum)]
  have hlevel : x ^ 2 - x₀ ^ 2 ≤ saddleQ d α - edgeQ d := by
    rw [edgeQ, saddleQ, saddleQ]
    simp only [sinRatio_zero]
    dsimp [x, x₀] at *
    nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hprod)]
  exact (saddleRadius_inv_sub_edge_lower d hd hΛ hα).trans
    (hsq.trans hlevel)

/-- On `[0, 1 / 2]`, the cosine is at least one half. -/
theorem half_le_cos_of_mem_Icc {α : ℝ} (hα : α ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    1 / 2 ≤ Real.cos α := by
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := α), hα.1, hα.2]

/-- A point of `[0, 1 / 2]` lies in `[0, π / 2]`. -/
theorem mem_Icc_pi_div_two_of_mem_Icc_half {α : ℝ} (hα : α ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    α ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨hα.1, hα.2.trans (by linarith [Real.two_le_pi])⟩

/-- On `[0, 1 / 2]`, the cotangent ratio falls short of one by at most `α ^ 2 / 2`. -/
theorem one_sub_alphaCot_le_sq_div_two {α : ℝ} (hα : α ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    1 - alphaCot α ≤ α ^ 2 / 2 := by
  have hαpi := mem_Icc_pi_div_two_of_mem_Icc_half hα
  have hcos0 : 0 ≤ Real.cos α := by linarith [half_le_cos_of_mem_Icc hα]
  have hcotlo : Real.cos α ≤ alphaCot α := by
    rw [← cos_mul_sinRatio]
    nlinarith [mul_nonneg hcos0 (sub_nonneg.mpr (one_le_sinRatio_of_mem hαpi))]
  linarith [Real.one_sub_sq_div_two_le_cos (x := α)]

/-- On `[0, 1 / 2]`, the reciprocal radius moves at most quadratically away
from its edge value. -/
theorem saddleRadius_inv_sub_edge_upper (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d) {α : ℝ} (hα : α ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    (saddleRadius d α)⁻¹ - (saddleRadius d 0)⁻¹ ≤ 2 * α ^ 2 := by
  let x := (saddleRadius d α)⁻¹
  let x₀ := (saddleRadius d 0)⁻¹
  let a := 2 * scaleLambda d / Real.pi
  have hαpi := mem_Icc_pi_div_two_of_mem_Icc_half hα
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hx0 : 0 < x₀ := inv_pos.2 (saddleRadius_pos_of_mem_Icc d hd h0)
  have hxx0 : x₀ ≤ x := saddleRadius_zero_inv_le_inv d hd hαpi
  have hdx : 0 ≤ x - x₀ := sub_nonneg.mpr hxx0
  have hx0one : x₀ ≤ 1 := saddleRadius_zero_inv_le_one d hd
  have ha48 : 48 ≤ a := (le_div_iff₀ Real.pi_pos).2 (by linarith)
  have ha : 0 < a := by linarith
  have hcoslo := half_le_cos_of_mem_Icc hα
  have hcosloss : 1 - Real.cos α ≤ α ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hcotloss := one_sub_alphaCot_le_sq_div_two hα
  have hid := saddleRadius_inv_radial_difference d hd hαpi
  have hlog0 : 0 ≤ Real.log (x / x₀) :=
    Real.log_nonneg ((le_div_iff₀ hx0).2 (by simpa using hxx0))
  have hleft :
      a * Real.cos α * (x - x₀) + Real.log (x / x₀) =
        a * x₀ * (1 - Real.cos α) + (1 - alphaCot α) := by
    dsimp [a, x, x₀] at hid ⊢
    nlinarith
  have hlower :
      a * (1 / 2 : ℝ) * (x - x₀) ≤
        a * Real.cos α * (x - x₀) + Real.log (x / x₀) := by
    have hc := mul_le_mul_of_nonneg_right hcoslo hdx
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hc)]
  have hupper :
      a * x₀ * (1 - Real.cos α) + (1 - alphaCot α) ≤
        (a + 1) * (α ^ 2 / 2) := by
    have hfirst := mul_le_mul hcosloss hx0one
      hx0.le (by positivity : 0 ≤ α ^ 2 / 2)
    have hfirst' := mul_le_mul_of_nonneg_left hfirst ha.le
    nlinarith
  have hcoef := mul_le_mul_of_nonneg_right
    (show a + 1 ≤ (49 / 48 : ℝ) * a by linarith) (by positivity : 0 ≤ α ^ 2 / 2)
  have hcancel :
      (x - x₀) / 2 ≤ (49 / 48 : ℝ) * α ^ 2 / 2 :=
    le_of_mul_le_mul_left (by linarith) ha
  dsimp [x, x₀] at hcancel ⊢
  nlinarith [sq_nonneg α]

/-- On `[0, 1 / 2]`, the sine ratio is at most `1 + α ^ 2`. -/
theorem sinRatio_le_one_add_sq {α : ℝ} (hα : α ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    sinRatio α ≤ 1 + α ^ 2 := by
  rcases hα.1.eq_or_lt with rfl | hpos
  · norm_num
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hpos
    (hα.2.trans_lt (by linarith [Real.two_le_pi]))
  rw [sinRatio_of_ne hpos.ne', div_le_iff₀ hsin]
  have hsq : α ^ 2 ≤ 1 / 4 := by nlinarith [hα.1, hα.2]
  have hfac : α ≤ (1 + α ^ 2) * (α - α ^ 3 / 6) := by
    nlinarith [mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hsq)]
  exact hfac.trans (mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hα.1) (by positivity))

/-- Uniform quadratic upper separation of the saddle level from the edge on
`[0, 1 / 2]`. -/
theorem saddleQ_sub_edge_upper (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α : ℝ} (hα : α ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    saddleQ d α - edgeQ d ≤ 6 * α ^ 2 := by
  let x := (saddleRadius d α)⁻¹
  let x₀ := (saddleRadius d 0)⁻¹
  have hαpi := mem_Icc_pi_div_two_of_mem_Icc_half hα
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hx0 : 0 < x₀ := inv_pos.2 (saddleRadius_pos_of_mem_Icc d hd h0)
  have hxx0 : x₀ ≤ x := saddleRadius_zero_inv_le_inv d hd hαpi
  have hx0one : x₀ ≤ 1 := saddleRadius_zero_inv_le_one d hd
  have hdx : x - x₀ ≤ 2 * α ^ 2 :=
    saddleRadius_inv_sub_edge_upper d hd hΛ hα
  have hdx0 : 0 ≤ x - x₀ := sub_nonneg.mpr hxx0
  have hsqα : α ^ 2 ≤ 1 / 4 := by nlinarith [hα.1, hα.2]
  have hx : x ≤ 3 / 2 := by nlinarith
  have hs : sinRatio α ≤ 1 + α ^ 2 := sinRatio_le_one_add_sq hα
  have hs0 : 0 ≤ sinRatio α := (sinRatio_pos_of_mem hαpi).le
  have hsqdiff : x ^ 2 - x₀ ^ 2 ≤ 5 * α ^ 2 := by
    have hsum : x + x₀ ≤ 5 / 2 := by nlinarith
    have hm := mul_le_mul hdx hsum
      (by nlinarith [hx0]) (by positivity : 0 ≤ 2 * α ^ 2)
    nlinarith [sq_nonneg (x - x₀)]
  have hproddiff : sinRatio α * x - x₀ ≤ 4 * α ^ 2 := by
    have hsone : sinRatio α - 1 ≤ α ^ 2 := by linarith
    have hsexpand :
        sinRatio α * x - x₀ =
          sinRatio α * (x - x₀) + (sinRatio α - 1) * x₀ := by ring
    have hfirst := mul_le_mul hs hdx hdx0
      (by positivity : 0 ≤ 1 + α ^ 2)
    have hsecond := mul_le_mul hsone hx0one hx0.le (sq_nonneg α)
    rw [hsexpand]
    nlinarith [mul_nonneg (sq_nonneg α)
      (sub_nonneg.mpr hsqα)]
  have hcoef : Real.pi / scaleLambda d ≤ 1 / 24 :=
    (div_le_iff₀ (scaleLambda_pos d hd)).2 (by nlinarith [Real.pi_pos])
  have hcoef0 : 0 ≤ Real.pi / scaleLambda d :=
    (div_pos Real.pi_pos (scaleLambda_pos d hd)).le
  rw [edgeQ, saddleQ, saddleQ]
  simp only [sinRatio_zero]
  have hsone := one_le_sinRatio_of_mem hαpi
  dsimp [x, x₀] at *
  have hterm := mul_le_mul hcoef hproddiff
    (by
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hxx0),
        mul_nonneg (sub_nonneg.mpr hsone) hx0.le])
    (by norm_num : (0 : ℝ) ≤ 1 / 24)
  nlinarith

/-- On the inverse saddle branch, the angle is bounded by the square root of
the displacement from the edge. -/
theorem saddleAngle_le_sqrt_edge_displacement (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d) {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    saddleAngle d q ≤ Real.sqrt (50 * (q - edgeQ d)) := by
  obtain ⟨hα0, hαtop, hinv⟩ := saddle_inverse_on_scale_window d hd hq
  have hedge := saddleQ_sub_edge_lower d hd hΛ ⟨hα0.le, hαtop.le⟩
  rw [hinv] at hedge
  exact Real.le_sqrt_of_sq_le (by linarith)

end RiemannJensen
