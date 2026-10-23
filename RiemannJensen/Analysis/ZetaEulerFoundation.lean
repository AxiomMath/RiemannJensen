module

public import Mathlib

/-!
# The first-order Euler–Maclaurin formula and the continuation of `ζ`

The first-order Euler–Maclaurin formula expresses a sum `∑ k ∈ (⌊a⌋₊, ⌊b⌋₊], f k` through the
integral of `f` and an integral of `f'` against the periodic function `B1 x = x - ⌊x⌋₊ - 1 / 2`.
Applied to `n ↦ n ^ (-s)`, it gives for each `N ≥ 1` a function `riemannZeta0 N` that is
holomorphic on `{s | s ≠ 1 ∧ 0 < s.re}` and agrees there with `riemannZeta`.

## Main definitions

* `B1`: The function `x ↦ x - ⌊x⌋₊ - 1 / 2`.
* `riemannZeta0`: The Euler–Maclaurin expression
  `∑ n ≤ N, n ^ (-s) - N ^ (1 - s) / (1 - s) - N ^ (-s) / 2 + s ∫_N^∞ (⌊x⌋ + 1/2 - x) x^(-s-1) dx`.
* `ζ₀'`: The derivative of `riemannZeta0 N` in `s`.

## Main results

* `sum_eq_integral_add_integral_deriv`: The first-order Euler–Maclaurin formula.
* `ZetaSum_aux1`: The Euler–Maclaurin formula for `∑ n ∈ (a, b], n ^ (-s)`.
* `hasDerivAt_riemannZeta0`: `riemannZeta0 N` has derivative `ζ₀' N s` at `s` when `0 < s.re`
  and `s ≠ 1`.
* `riemannZeta0_eq_riemannZeta`: `riemannZeta0 N s = riemannZeta s` when `0 < s.re` and `s ≠ 1`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Topology Filter Interval Set Asymptotics MeasureTheory

/-- A complex function differentiable at a real point is differentiable along the real line
there. -/
lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The function `x ↦ x - ⌊x⌋₊ - 1 / 2`, the first periodic Bernoulli function on `[0, ∞)`. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

/-- `B1` is almost everywhere strongly measurable. -/
@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

/-- For `0 ≤ x`, `|B1 x| ≤ 1 / 2`. -/
lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

/-- Integration by parts: `∫_a^b (t + c) f'(t) dt = (b + c) f(b) - (a + c) f(a) - ∫_a^b f`. -/
lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b)
    (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t =
      (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

/-- If `f'` is continuous on `[a, b]` with `0 ≤ a ≤ b`, then `f' * B1` is interval integrable
on `[a, b]`. -/
lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

/-- The integral `∫_a^b f'(t) (⌊t⌋₊ + 1) dt` equals
`(b + 1/2) f(b) - (a + 1/2) f(a) - ∫_a^b f - ∫_a^b f' B1`. -/
lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) =
      (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) -
        ∫ t in a..b, deriv f t * B1 t := by
  calc
    _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) - deriv f t * B1 t) := by
      congr
      ext
      simp only [B1]
      push_cast
      ring
    _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) -
        ∫ t in a..b, deriv f t * B1 t :=
      intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop))
        (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
    _ = _ := by
      conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
      rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

/-- **First-order Euler–Maclaurin formula**: for `0 ≤ a ≤ b` and `f` differentiable on `[a, b]`
with continuous derivative, `∑ k ∈ (⌊a⌋₊, ⌊b⌋₊], f k` equals
`f(a) B1(a) - f(b) B1(b) + ∫_a^b f + ∫_a^b f' B1`. -/
theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) +
        ∫ t in a..b, deriv f t * B1 t := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff
    (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, Finset.sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab,
    integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring

/-- For complex numbers, `a / x ^ s = a * x ^ (-s)`. -/
lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]

/-- For complex numbers, `1 / x ^ s = x ^ (-s)`. -/
lemma one_div_cpow_eq_cpow_neg (x s : ℂ) : 1 / x ^ s = x ^ (-s) := by
  convert div_cpow_eq_cpow_neg 1 x s using 1; simp

/-- For real `0 ≤ x`, `a / x ^ s = a * x ^ (-s)`. -/
lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]

/-- The Euler–Maclaurin expression for the Riemann zeta function truncated at `N`:
`∑_{n ≤ N} 1 / n ^ s - N ^ (1 - s) / (1 - s) - N ^ (-s) / 2 + s ∫_N^∞ (⌊x⌋ + 1/2 - x) / x^(s+1)`.
-/
noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

/-- `ζ₀` denotes `riemannZeta0`. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

/-- `riemannZeta0 N s` with the quotients by powers written as negative powers. -/
lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring

/-- For `0 < x`, the function `t ↦ (t : ℂ) ^ s` is real-differentiable at `x`. -/
lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])

/-- The first-order Euler–Maclaurin formula for a complex-valued `φ` on `[a, b]`, `0 ≤ a < b`,
with the sawtooth `⌊x⌋ + 1/2 - x`. -/
lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le
    (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x =
      -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring

/-- For naturals `0 < a < b`, every point of `[a, b]` is positive. -/
lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]

/-- For naturals `0 < a < b` and `s ≠ 1`,
`∫_a^b 1 / x ^ s dx = (b ^ (1 - s) - a ^ (1 - s)) / (1 - s)`. -/
lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · exact intervalIntegral.integral_congr fun x _ ↦ one_div_cpow_eq_cpow_neg _ _
  · norm_cast; ring_nf
  · exact .inr ⟨by grind, fun hx ↦ lt_irrefl 0 (xpos_of_uIcc ha hx)⟩

/-- For `0 < x`, the function `t ↦ 1 / (t : ℂ) ^ s` has a derivative at `x`. -/
lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x :=
  hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])

/-- For `s ≠ 0` and `0 < x`, the derivative of `t ↦ 1 / (t : ℂ) ^ s` at `x` is
`-s * x ^ (-(s + 1))`. -/
lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf

/-- For `s ≠ 0` and naturals `0 < a < b`, the derivative of `t ↦ 1 / (t : ℂ) ^ s` is
continuous on `[a, b]`. -/
lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx

set_option backward.isDefEq.respectTransparency false in
/-- The Euler–Maclaurin formula for `∑ n ∈ (a, b], 1 / n ^ s` with naturals `0 < a < b` and
`s ∉ {0, 1}`. -/
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ s) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf

/-- For `0 < a < b`, every point of `[a, b]` is positive. -/
lemma ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x :=
  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1

/-- For `0 < a < b` and `c ≠ 0`, `∫_a^b 1 / x ^ (c + 1) dx = (a ^ (-c) - b ^ (-c)) / c`. -/
lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (hc : c ≠ 0) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  rw [(by ring : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c))]
  have := integral_rpow (a := a) (b := b) (r := -c-1)
    (Or.inr ⟨by simp [hc], fun h ↦ lt_irrefl 0 (ZetaSum_aux1_1 apos a_lt_b h)⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have : 0 ≤ x := (ZetaSum_aux1_1 apos a_lt_b hx).le
  simp [div_rpow_eq_rpow_neg _ _ _ this, sub_eq_add_neg, add_comm]

/-- The sawtooth `⌊x⌋ + 1/2 - x` has norm at most `1 / 2`. -/
lemma ZetaSum_aux1_3 (x : ℝ) : ‖⌊x⌋ + 1 / 2 - x‖ ≤ 1 / 2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩

/-- For `0 < x`, `‖(⌊x⌋ + 1/2 - x) / x ^ (s + 1)‖ = ‖⌊x⌋ + 1/2 - x‖ / x ^ (s + 1).re`. -/
lemma ZetaSum_aux1_4' (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  simp_rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp

/-- For `0 < a < b`, the integral over `[a, b]` of `‖(⌊x⌋ + 1/2 - x) / x ^ (s + 1)‖` equals
that of `|⌊x⌋ + 1/2 - x| / x ^ (s + 1).re`. -/
lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
    ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re :=
  intervalIntegral.integral_congr fun x hx ↦ ZetaSum_aux1_4' x (ZetaSum_aux1_1 apos a_lt_b hx) s

/-- For `0 < a` and `x ∈ Icc a b`,
`|⌊x⌋ + 1/2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1)`. -/
lemma ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
    (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) :=
  div_le_div_of_nonneg_right ((ZetaSum_aux1_3 x).trans (by norm_num))
    (Real.rpow_nonneg (apos.trans_le h.1).le _)

/-- For `0 < a < b`, `u ↦ 1 / u ^ (s.re + 1)` is interval integrable on `[a, b]`. -/
lemma ZetaSum_aux1_5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
    IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) volume a b := by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt <| apos.trans_le hx.1)
  · exact fun x hx ↦ (Real.rpow_pos_of_pos (apos.trans_le hx.1) _).ne'

/-- The sawtooth `u ↦ ⌊u⌋ + 1/2 - u` is measurable. -/
lemma measurable_floor_add_half_sub : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor

/-- The function `u ↦ |⌊u⌋ + 1/2 - u| / u ^ (s.re + 1)` is almost everywhere strongly
measurable on `Ι a b`. -/
lemma ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    AEStronglyMeasurable (fun u : ℝ ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
      (Measure.restrict volume (Ι a b)) := by
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp measurable_floor_add_half_sub

/-- For `0 < a < b`, `u ↦ |⌊u⌋ + 1/2 - u| / u ^ (s.re + 1)` is interval integrable on
`[a, b]`. -/
lemma ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
    IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) volume a b := by
  apply ZetaSum_aux1_5b apos a_lt_b (s := s) |>.mono_fun ZetaSum_aux1_5c ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_div, norm_inv, abs_div, _root_.abs_abs]
  conv => rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x ^ (s.re + 1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (ZetaSum_aux1_3 x) <| by norm_num

/-- For `0 < a < b`, the integral over `[a, b]` of `|⌊x⌋ + 1/2 - x| / x ^ (s.re + 1)` is at
most that of `1 / x ^ (s.re + 1)`. -/
lemma ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
      ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) :=
  intervalIntegral.integral_mono_on a_lt_b.le (ZetaSum_aux1_5d apos a_lt_b)
    (ZetaSum_aux1_5b apos a_lt_b) (ZetaSum_aux1_5a apos)

/-- For `0 < a < b` and `0 < s.re`, the integral over `[a, b]` of
`‖(⌊x⌋ + 1/2 - x) / x ^ (s + 1)‖` is at most `(a ^ (-s.re) - b ^ (-s.re)) / s.re`. -/
lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x ^ (s+1).re := ZetaSum_aux1_4 apos a_lt_b
    _ ≤ ∫ x in a..b, 1 / x ^ (s.re + 1) := ZetaSum_aux1_5 apos a_lt_b
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := ZetaSum_aux1_2 apos a_lt_b σpos.ne'

/-- For summable `f`, the partial sums `∑ n ∈ Ico N k, f n` tend to `∑' n, f (n + N)` as
`k → ∞`. -/
lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith

/-- For `1 < s.re`, `n ^ (1 - s) → 0` as the natural number `n → ∞`. -/
lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]

/-- For `0 < s.re`, `(n ^ s)⁻¹ → 0` as the natural number `n → ∞`. -/
lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  exact ((tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop

/-- For `1 < s.re`, `∑ n ∈ (N, k], 1 / n ^ s` tends to `∑' n, 1 / (n + N + 1) ^ s` as
`k → ∞`. -/
lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr s_re_gt
  simp_rw [← Finset.Ico_add_one_add_one_eq_Ioc]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]

/-- For `0 < N` and `0 < s.re`, `x ↦ (⌊x⌋ + 1/2 - x) * x ^ (-(s + 1))` is integrable on
`Ioi N`. -/
lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N) volume := by
  have hc := ZetaSum_aux1_3
  apply MeasureTheory.Integrable.bdd_mul (c := 1 / 2) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc
    simp only [← Complex.norm_real]
    simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor

/-- For `0 < N` and `1 < s.re`, the tail `∑' n, 1 / (n + N + 1) ^ s` equals
`-N ^ (1 - s) / (1 - s) - N ^ (-s) / 2 + s ∫_N^∞ (⌊x⌋ + 1/2 - x) x ^ (-(s + 1)) dx`. -/
lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · exact (ZetaSum_aux3 s_re_gt).congr' <| Filter.eventually_atTop.mpr
      ⟨N + 1, fun k hk ↦ ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩⟩
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply Complex.cpow_tendsto s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| Complex.cpow_inv_tendsto (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]
      exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (integrableOn_of_Zeta0_fun N_pos <| by positivity) tendsto_natCast_atTop_atTop

/-- For `1 ≤ N` and `0 < σ`,
`‖∫_N^∞ (⌊x⌋ + 1/2 - x) / x ^ (σ + t i + 1) dx‖ ≤ N ^ (-σ) / σ`. -/
lemma ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  apply le_trans (norm_integral_le_integral_norm _)
  apply le_of_tendsto (x := atTop (α := ℝ)) (f := fun (t : ℝ) ↦ ∫ (x : ℝ) in N..t,
    ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id)
      (f := fun (x : ℝ) ↦ ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N : ℝ))]
      intro u hu
      simp only [id_eq, intervalIntegral.integral_of_le hu, norm_div]
      apply setIntegral_congr_fun (by simp)
      intro x hx
      beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert! integrableOn_of_Zeta0_fun (s := σ + t * I) Npos (by simp [σpos]) using 1
      simp_rw [div_eq_mul_inv, cpow_neg]
    · exact fun ⦃_⦄ a ↦ a
  · filter_upwards [mem_atTop (N + 1 : ℝ)] with t ht
    have : (N ^ (-σ) - t ^ (-σ)) / σ ≤ N ^ (-σ) / σ :=
      div_le_div_iff_of_pos_right σpos |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert! ZetaBnd_aux1a (a := N) (b := t) (by positivity) (by linarith) ?_ <;> simp [σpos]

/-- For `1 ≤ N`, `σ ∈ (0, 2]` and `2 ≤ |t|`, with `s = σ + t i`,
`‖s ∫_N^∞ (⌊x⌋ + 1/2 - x) / x ^ (s + 1) dx‖ ≤ 2 |t| N ^ (-σ) / σ`. -/
lemma ZetaBnd_aux1 (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ 2 * |t| * N ^ (-σ) / σ := by
  rw [norm_mul, mul_div_assoc]
  rw [Set.mem_Ioc] at hσ
  apply mul_le_mul ?_ (ZetaBnd_aux1b N Npos hσ.1) (norm_nonneg _) (by positivity)
  refine le_trans (by apply norm_add_le) ?_
  simp only [Complex.norm_of_nonneg hσ.1.le, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_I,
    mul_one]
  linarith [hσ.2]

/-- For `1 ≤ N` and `σ ∈ (0, 2]`, with `s = σ + t i`,
`‖s ∫_N^∞ (⌊x⌋ + 1/2 - x) / x ^ (s + 1) dx‖ = O(|t| N ^ (-σ) / σ)` on `{t | 2 ≤ |t|}`. -/
lemma ZetaBnd_aux1p (N : ℕ) (Npos : 1 ≤ N) {σ : ℝ} (hσ : σ ∈ Ioc 0 2) :
    (fun (t : ℝ) ↦
      ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖)
    =O[Filter.principal {t | 2 ≤ |t|}] fun t ↦ |t| * N ^ (-σ) / σ := by
  rw [Asymptotics.IsBigO_def]
  use 2
  rw [Asymptotics.isBigOWith_principal]
  intro t ht
  simp only [mem_ofPred_eq] at ht
  rw [norm_norm]
  refine (ZetaBnd_aux1 N Npos hσ ht).trans_eq ?_
  rw [Real.norm_of_nonneg (div_nonneg (by positivity) hσ.1.le)]
  ring

/-- For `r < 0` and `0 < N`, `x ↦ ‖x ^ (r - 1)‖ * ‖log x‖` is integrable on `Ioi N`. -/
lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx
      left
      contrapose! Npos with h
      exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx
      simp only [id_eq]
      contrapose! Npos with h
      exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hh
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have := hx₀ y (by linarith)
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1

/-- For `0 < N` and `0 < s.re`, `x ↦ (⌊x⌋ + 1/2 - x) * x ^ (-(s + 1)) * (-log x)` is
integrable on `Ioi N`. -/
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  have hc := ZetaSum_aux1_3
  apply Integrable.bdd_mul (c := 1 / 2) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]
          linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx
        simp only [id_eq]
        linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      apply (integrable_log_over_pow (r := -s.re) (by linarith) Npos).congr_fun ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x
    simp only [← Complex.norm_real]
    simp

/-- For `1 < x` and `z` within `s.re / 2` of `s`, the `z`-derivative of the integrand of
`hasDerivAt_Zeta0Integral` is bounded by `|x ^ (-s.re / 2 - 1)| * |log x|`. -/
lemma norm_cpow_neg_sub_one_mul_log_le {s z : ℂ} {x : ℝ} (hx : 1 < x)
    (hz : z ∈ Metric.ball s (s.re / 2)) :
    ‖(x : ℂ) ^ (-z - 1) * (-Real.log x) * ((⌊x⌋ : ℂ) + 1 / 2 - x)‖ ≤
      |x ^ (-s.re / 2 - 1)| * |Real.log x| := by
  calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
          simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
            ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
            Complex.norm_real]
       _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
       _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
       _ ≤ _ := ?_
  · congr! 2
    simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
      sub_re, neg_re, one_re]
    apply abs_eq_self.mpr ?_ |>.symm
    positivity
  · rw [mul_comm, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
    simp only [Metric.mem_ball, Complex.dist_eq] at hz
    apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
    · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3 _) (by norm_num)) <| abs_nonneg _
    · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
      apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (.inl hx.le)
      have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
      simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
      linarith [this.1]

/-- For `1 < x` and `z` within `s.re / 2` of `s`, `w ↦ x ^ (-w - 1) * c` has derivative
`x ^ (-z - 1) * (-log x) * c` at `z`. -/
lemma hasDerivAt_cpow_neg_sub_one_mul {s z : ℂ} {x : ℝ} (one_lt_x : 1 < x)
    (hz : z ∈ Metric.ball s (s.re / 2)) (c : ℂ) :
    HasDerivAt (fun w : ℂ ↦ (x : ℂ) ^ (-w - 1) * c) ((x : ℂ) ^ (-z - 1) * (-Real.log x) * c) z := by
  refine HasDerivAt.mul_const ?_ c
  convert! HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
    (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
  · simp only [mul_neg, mul_one]; congr! 2
  · convert! HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
      (hasDerivAt_id _) ?_ using 1
    · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
      left
      rw [Complex.ofReal_log]
      linarith
    · right
      intro h
      simp only [Metric.mem_ball, Complex.dist_eq,
        neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
      have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
      simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
      linarith [norm_nonneg (-1 - s)]
  · apply hasDerivAt_id _ |>.neg |>.sub_const

/-- For `0 < N` and `0 < s.re`, the function `z ↦ ∫_N^∞ (⌊x⌋ + 1/2 - x) x ^ (-z - 1) dx` has
derivative `∫_N^∞ (⌊x⌋ + 1/2 - x) x ^ (-s - 1) (-log x) dx` at `s`. -/
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
      (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [this] with z hz
    convert! integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]
    ext x
    ring_nf
  have hF_int : Integrable (F s) μ := by
    convert! integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    simp only [F, f]
    ext x
    ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert! integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]
    ext x
    ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
    fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    exact fun z hz ↦ norm_cpow_neg_sub_one_mul_log_le hx hz
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert! integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x one_lt_x
    exact fun z hz ↦ hasDerivAt_cpow_neg_sub_one_mul one_lt_x hz _
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f]; ring_nf

/-- The derivative in `s` of `riemannZeta0 N s`, computed term by term. -/
noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))

/-- For `0 < N`, `z ↦ -N ^ (-z) / 2` has derivative `-(-log N * N ^ (-s)) / 2` at `s`. -/
lemma hasDerivAt_neg_natCast_cpow_neg_div_two {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert! hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]

/-- For `z ≠ 0`, `w ↦ -N ^ w / w` has derivative `N ^ z / z ^ 2 - log N * N ^ z / z` at `z`. -/
lemma hasDerivAt_neg_natCast_cpow_div_self (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero

/-- For `0 < N`, `0 < s.re` and `s ≠ 1`, `riemannZeta0 N` has derivative `ζ₀' N s` at `s`. -/
lemma hasDerivAt_riemannZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re)
    (s_ne_one : s ≠ 1) :
    HasDerivAt (ζ₀ N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1
    · ring_nf
    · exact hasDerivAt_neg_natCast_cpow_div_self N (sub_ne_zero.mpr s_ne_one.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1
      simp
  · convert! hasDerivAt_neg_natCast_cpow_neg_div_two Npos s using 1
    simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| hasDerivAt_Zeta0Integral Npos reS_pos using 1

/-- For `0 < N`, `riemannZeta0 N` is holomorphic on `{s | s ≠ 1 ∧ 0 < s.re}`. -/
lemma differentiableOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    DifferentiableOn ℂ (ζ₀ N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (hasDerivAt_riemannZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt

/-- A point `w ≠ 1` on the positive real axis is joined to `2` within
`{z | z ≠ 1 ∧ 0 < z.re}`, through `1 + I`. -/
lemma joinedIn_two_of_im_eq_zero {w : ℂ} (hw : w ≠ 1 ∧ 0 < w.re) (w_im : w.im = 0) :
    JoinedIn {z : ℂ | z ≠ 1 ∧ 0 < z.re} 2 w := by
  apply JoinedIn.trans (y := 1 + I)
  · let f : ℝ → ℂ := fun t ↦ (1 + I) * t + 2 * (1 - t)
    have cont : Continuous f := by fun_prop
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re, one_re,
      I_re, add_zero, ofReal_re, one_mul, add_im, one_im, I_im, zero_add, ofReal_im, mul_zero,
      sub_zero, re_ofNat, sub_re, im_ofNat, sub_im, sub_self, f]
    intro x hx
    simp only [mem_Icc] at hx
    refine ⟨fun h ↦ ?_, by linarith⟩
    rw [Complex.ext_iff] at h
    simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
  · let f : ℝ → ℂ := fun t ↦ w * t + (1 + I) * (1 - t)
    have cont : Continuous f := by fun_prop
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re,
      ofReal_re, ofReal_im, mul_zero, sub_zero, one_re, I_re, add_zero, sub_re, one_mul, add_im,
      one_im, I_im, zero_add, sub_im, sub_self, f]
    intro x hx
    simp only [mem_Icc] at hx
    simp only [mem_ofPred_eq]
    refine ⟨fun h ↦ hw.1 ?_, ?_⟩
    · rw [Complex.ext_iff] at h
      have : x = 1 := by linarith [(by apply And.right; simpa [w_im] using h : 1 - x = 0)]
      rw [Complex.ext_iff, one_re, one_im]
      exact ⟨by simpa [this, w_im] using h, w_im⟩
    · rcases hx.1.eq_or_lt with rfl | hpos
      · linarith
      · have : 0 ≤ 1 - x := by linarith
        have := hw.2
        positivity

/-- A point `w` off the real axis with `0 < w.re` is joined to `2` within
`{z | z ≠ 1 ∧ 0 < z.re}` by a line segment. -/
lemma joinedIn_two_of_im_ne_zero {w : ℂ} (hw : w ≠ 1 ∧ 0 < w.re) (w_im : w.im ≠ 0) :
    JoinedIn {z : ℂ | z ≠ 1 ∧ 0 < z.re} 2 w := by
  let f : ℝ → ℂ := fun t ↦ w * t + 2 * (1 - t)
  have cont : Continuous f := by fun_prop
  apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
  simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re, ofReal_re,
    ofReal_im, mul_zero, sub_zero, re_ofNat, sub_re, one_re, im_ofNat, sub_im, one_im, sub_self,
    f]
  intro x hx
  simp only [mem_Icc] at hx
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [Complex.ext_iff] at h
    simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
  · rcases hx.1.eq_or_lt with rfl | hpos
    · linarith
    · have : 0 ≤ 1 - x := by linarith
      have := hw.2
      positivity

/-- The set `{z | z ≠ 1 ∧ 0 < z.re}` is path connected. -/
lemma isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine ⟨2, by simp, fun w hw ↦ ?_⟩
  simp only [ne_eq, mem_ofPred_eq] at hw
  by_cases w_im : w.im = 0
  exacts [joinedIn_two_of_im_eq_zero hw w_im, joinedIn_two_of_im_ne_zero hw w_im]

/-- For `0 < N`, `0 < s.re` and `s ≠ 1`, `riemannZeta0 N s = riemannZeta s`. -/
lemma riemannZeta0_eq_riemannZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re)
    (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s := by
  let f := riemannZeta
  let g := ζ₀ N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U :=
    (DifferentiableOn.analyticOnNhd
      (fun _ hz ↦ (differentiableAt_riemannZeta hz).differentiableWithinAt) isOpen_ne).mono
      fun _ h ↦ h.1
  have g_an : AnalyticOnNhd ℂ g U := (differentiableOn_riemannZeta0 N_pos).analyticOnNhd
    (isOpen_ne.inter (isOpen_lt continuous_const Complex.continuous_re))
  have preconU : IsPreconnected U := isPathConnected_aux.isConnected.isPreconnected
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  filter_upwards [u_mem] with z hz
  simp only [f, g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast

end RiemannJensen
