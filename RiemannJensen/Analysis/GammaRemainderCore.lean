module

public import RiemannJensen.Analysis.StirlingNative

/-!
# The Stirling remainder of `Γ(w/2 + 1/4)`

We study the quotient `gammaCoreRemainder w = Γ(w/2 + 1/4) / (√(2π) (w/2)^(w/2 - 1/4) e^(-w/2))` on
the open domain `grDomain = {w | -1/2 < Re w, 3 < ‖w‖}`. It is the exponential of the explicit
holomorphic function `gammaCoreLog`, it tends to `1` like `O(1/‖w‖)`, and its logarithmic
derivative is `O(1/‖w‖²)` on `{Re w ≥ 0, ‖w‖ ≥ 4}`.

## Main definitions

* `gammaCoreRemainder`: The quotient of `Γ(w/2 + 1/4)` by its Stirling approximation.
* `gammaCoreLog`: An explicit holomorphic logarithm of `gammaCoreRemainder`.
* `gammaCoreLogDeriv`: The derivative of `gammaCoreLog`.
* `grDomain`: The open set `{w | -1/2 < Re w, 3 < ‖w‖}`.
* `stirDomain`: The open set `{z | 0 < Re z, 1 < ‖z‖}`.
* `stirDd`: The explicit derivative of `stirD`.

## Main results

* `gammaCoreRemainder_eq_exp`: `gammaCoreRemainder = exp ∘ gammaCoreLog` on `grDomain`.
* `norm_gammaCoreRemainder_sub_one_le`: `‖gammaCoreRemainder w - 1‖ ≤ 64/‖w‖` for
  `Re w ≥ 0`, `‖w‖ ≥ 4`.
* `differentiableOn_gammaCoreRemainder`: `gammaCoreRemainder` is holomorphic on `grDomain`.
* `gammaCoreRemainder_ne_zero`: `gammaCoreRemainder` does not vanish on `grDomain`.
* `norm_logDeriv_gammaCoreRemainder_le`: `‖logDeriv gammaCoreRemainder w‖ ≤ 13/‖w‖²` for
  `Re w ≥ 0`, `‖w‖ ≥ 4`.
* `logDeriv_gammaCoreRemainder_eq_digamma`: the logarithmic derivative of
  `gammaCoreRemainder` in terms of the logarithmic derivative of `Γ`.
-/

@[expose] public section

open Complex Filter Topology Finset

namespace RiemannJensen

namespace GammaCore

open StirlingScratch

/-- `log (z + a) = log z + log (1 + a / z)` for `Re z ≥ 0`, `z ≠ 0`, real `a > 0`. -/
lemma log_add_real_eq {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) {a : ℝ} (ha : 0 < a) :
    Complex.log (z + a) = Complex.log z + Complex.log (1 + a / z) := by
  have hre : 0 < (1 + (a : ℂ) / z).re := by
    rw [add_re, one_re, div_eq_mul_inv, re_ofReal_mul, inv_re]
    have : 0 ≤ a * (z.re / normSq z) := mul_nonneg ha.le (div_nonneg hz (normSq_nonneg z))
    linarith
  have hw0 : (1 + (a : ℂ) / z) ≠ 0 := fun h => by simp [h] at hre
  have h1 : |arg z| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_iff.mpr hz
  have h2 : |arg (1 + (a : ℂ) / z)| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  rw [← show z * (1 + (a : ℂ) / z) = z + a by field_simp]
  refine log_mul hz0 hw0 ?_
  rw [abs_le] at h1
  rw [abs_lt] at h2
  constructor <;> linarith [Real.pi_pos]

/-- `‖z‖ ≤ ‖z + a‖` for `Re z ≥ 0` and real `a ≥ 0`. -/
lemma norm_le_norm_add_real {z : ℂ} (hz : 0 ≤ z.re) {a : ℝ} (ha : 0 ≤ a) : ‖z‖ ≤ ‖z + a‖ := by
  have : ‖z‖ ^ 2 ≤ ‖z + a‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
    nlinarith [mul_nonneg hz ha]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- The quotient `Γ(w/2+1/4) / (√(2π) (w/2)^(w/2-1/4) e^(-w/2))`. -/
noncomputable def gammaCoreRemainder (w : ℂ) : ℂ :=
  Complex.Gamma (w/2 + 1/4) /
    ((Real.sqrt (2*Real.pi) : ℂ) * (w/2) ^ (w/2 - 1/4) * Complex.exp (-w/2))

/-- An explicit holomorphic logarithm of `gammaCoreRemainder`. -/
noncomputable def gammaCoreLog (w : ℂ) : ℂ :=
  stirR (w/2 + 1/4) + (w/2 - 1/4) * (Complex.log (w/2 + 1/4) - Complex.log (w/2)) - 1/4

/-- The open set `{w | -1/2 < Re w, 3 < ‖w‖}`. -/
def grDomain : Set ℂ := {w | -1/2 < w.re ∧ 3 < ‖w‖}

/-- The open set `{z | 0 < Re z, 1 < ‖z‖}`. -/
def stirDomain : Set ℂ := {z | 0 < z.re ∧ 1 < ‖z‖}

/-- `grDomain` is open. -/
lemma isOpen_grDomain : IsOpen grDomain :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_norm)

/-- `stirDomain` is open. -/
lemma isOpen_stirDomain : IsOpen stirDomain :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_norm)

/-- Every `w` with `Re w ≥ 0` and `‖w‖ ≥ 4` lies in `grDomain`. -/
lemma subset_grDomain {w : ℂ} (hw : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) : w ∈ grDomain :=
  ⟨by linarith, by linarith⟩

/-- For `w ∈ grDomain`, `w/2 + 1/4 ∈ stirDomain`, `w/2 ≠ 0`, and `w/2` lies in the slit plane. -/
lemma grDomain_props {w : ℂ} (hw : w ∈ grDomain) :
    w / 2 + 1 / 4 ∈ stirDomain ∧ w / 2 ≠ 0 ∧ w / 2 ∈ slitPlane := by
  obtain ⟨h1, h2⟩ := hw
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp
    linarith
  · have := norm_sub_le (w / 2 + 1 / 4) (1 / 4)
    rw [add_sub_cancel_right, norm_div, Complex.norm_two] at this
    have e : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
    linarith
  · exact div_ne_zero (norm_pos_iff.mp (by linarith)) two_ne_zero
  · rw [mem_slitPlane_iff]
    by_cases him : w.im = 0
    · left
      have hn := Complex.norm_le_abs_re_add_abs_im w
      rw [him, abs_zero, add_zero] at hn
      have : 3 < |w.re| := lt_of_lt_of_le h2 hn
      rw [lt_abs] at this
      simp only [div_re]
      norm_num
      rcases this with h | h <;> linarith
    · right
      simpa using him

/-- `√(2π) = exp (log (2π) / 2)`. -/
lemma sqrt_two_pi_eq :
    ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = exp ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) := by
  rw [← ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
  congr 2
  ring

/-- On `grDomain`, `gammaCoreRemainder = exp ∘ gammaCoreLog`. -/
theorem gammaCoreRemainder_eq_exp {w : ℂ} (hw : w ∈ grDomain) :
    gammaCoreRemainder w = exp (gammaCoreLog w) := by
  obtain ⟨⟨hs, hs1⟩, hu0, -⟩ := grDomain_props hw
  rw [gammaCoreRemainder, Gamma_eq_exp_stirMain_add hs.le hs1.le, sqrt_two_pi_eq,
    cpow_def_of_ne_zero hu0, ← exp_add, ← exp_add, ← exp_sub]
  congr 1
  unfold gammaCoreLog stirMain
  ring

/-- `(1 - x)⁻¹ ≤ 2` for `x ≤ 1/2`. -/
lemma inv_one_sub_le_two {x : ℝ} (hx : x ≤ 1 / 2) : (1 - x)⁻¹ ≤ 2 := by
  rw [inv_le_comm₀ (by linarith) two_pos]
  linarith

/-- `log (w/2 + 1/4) - log (w/2) = log (1 + 1/(2w))` for `Re w ≥ 0`, `w ≠ 0`. -/
lemma log_half_add_quarter_sub_log_half {w : ℂ} (hw : 0 ≤ w.re) (hw0 : w ≠ 0) :
    Complex.log (w / 2 + 1 / 4) - Complex.log (w / 2) = Complex.log (1 + 1 / (2 * w)) := by
  have hL := log_add_real_eq (z := w / 2) (by simp; linarith) (div_ne_zero hw0 two_ne_zero)
    (a := 1 / 4) (by norm_num)
  rw [show ((1 / 4 : ℝ) : ℂ) / (w / 2) = 1 / (2 * w) by push_cast; field_simp; ring] at hL
  push_cast at hL
  rw [hL, add_sub_cancel_left]

/-- `‖(t⁻¹ - 1) log(1+t) - 1‖ ≤ (5/2) ‖t‖` for `‖t‖ ≤ 1/2`. -/
lemma norm_aux_log {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) (ht0 : t ≠ 0) :
    ‖(t⁻¹ - 1) * Complex.log (1 + t) - 1‖ ≤ 5 / 2 * ‖t‖ := by
  have ht1 : ‖t‖ < 1 := lt_of_le_of_lt ht (by norm_num)
  have hC := norm_log_one_add_half_le_self ht
  have hid : (t⁻¹ - 1) * Complex.log (1 + t) - 1 =
      t⁻¹ * (Complex.log (1 + t) - t) - Complex.log (1 + t) := by
    field_simp
    ring
  have hnt : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  rw [hid]
  calc ‖t⁻¹ * (Complex.log (1 + t) - t) - Complex.log (1 + t)‖
      ≤ ‖t‖⁻¹ * ‖Complex.log (1 + t) - t‖ + ‖Complex.log (1 + t)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_inv]
    _ ≤ ‖t‖⁻¹ * (‖t‖ ^ 2 * 2 / 2) + 3 / 2 * ‖t‖ := by
        gcongr
        calc ‖Complex.log (1 + t) - t‖ ≤ ‖t‖ ^ 2 * (1 - ‖t‖)⁻¹ / 2 :=
            norm_log_one_add_sub_self_le ht1
          _ ≤ ‖t‖ ^ 2 * 2 / 2 := by
            gcongr
            exact inv_one_sub_le_two ht
    _ = 5 / 2 * ‖t‖ := by
        field_simp
        ring

/-- The elementary part of the exponent is `O(1/‖w‖)` on `Re w ≥ 0`. -/
lemma norm_elem_part_le {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 ≤ ‖w‖) :
    ‖(w/2 - 1/4) * (Complex.log (w/2 + 1/4) - Complex.log (w/2)) - 1/4‖ ≤ 5 / 16 / ‖w‖ := by
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [log_half_add_quarter_sub_log_half hw hw0]
  have hnw : 0 < ‖w‖ := by linarith
  have htn : ‖(1 : ℂ) / (2 * w)‖ = 1 / (2 * ‖w‖) := by
    rw [norm_div, norm_mul]
    norm_num
  have ht2 : ‖(1 : ℂ) / (2 * w)‖ ≤ 1 / 2 := by
    rw [htn, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h := norm_aux_log ht2 (by simp [hw0])
  have hid : (w/2 - 1/4) * Complex.log (1 + 1 / (2 * w)) - 1/4 =
      (1 / 4 : ℂ) * (((1 / (2 * w))⁻¹ - 1) * Complex.log (1 + 1 / (2 * w)) - 1) := by
    field_simp
    ring
  rw [hid, norm_mul, show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
  calc 1 / 4 * ‖((1 / (2 * w))⁻¹ - 1) * Complex.log (1 + 1 / (2 * w)) - 1‖
      ≤ 1 / 4 * (5 / 2 * (1 / (2 * ‖w‖))) := by
        rw [← htn]
        gcongr
    _ = 5 / 16 / ‖w‖ := by
        field_simp
        ring

/-- `‖w‖ / 2 ≤ ‖w/2 + 1/4‖` for `Re w ≥ 0`. -/
lemma norm_half_le_norm_s {w : ℂ} (hw : 0 ≤ w.re) : ‖w‖ / 2 ≤ ‖w / 2 + 1 / 4‖ := by
  have hure : 0 ≤ (w / 2).re := by
    simp
    linarith
  simpa [norm_div, Complex.norm_two] using norm_le_norm_add_real hure (a := 1 / 4) (by norm_num)

/-- `‖gammaCoreLog w‖ ≤ 8/‖w‖` on `Re w ≥ 0`, `‖w‖ ≥ 4`. -/
theorem norm_gammaCoreLog_le {w : ℂ} (hw : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) :
    ‖gammaCoreLog w‖ ≤ 8 / ‖w‖ := by
  have hnw : 0 < ‖w‖ := by linarith
  have hs := norm_half_le_norm_s hw
  have hsre : 0 ≤ (w / 2 + 1 / 4).re := by
    simp
    linarith
  have hR' : ‖stirR (w / 2 + 1 / 4)‖ ≤ 7 / ‖w‖ := by
    refine (norm_stirR_le hsre (by linarith)).trans ?_
    calc 7 / 2 / ‖w / 2 + 1 / 4‖ ≤ 7 / 2 / (‖w‖ / 2) := by gcongr
      _ = 7 / ‖w‖ := by field_simp
  rw [gammaCoreLog, add_sub_assoc]
  calc _ ≤ ‖stirR (w / 2 + 1 / 4)‖
        + ‖(w/2 - 1/4) * (Complex.log (w/2 + 1/4) - Complex.log (w/2)) - 1/4‖ := norm_add_le _ _
    _ ≤ 7 / ‖w‖ + 5 / 16 / ‖w‖ := add_le_add hR' (norm_elem_part_le hw (by linarith))
    _ ≤ 8 / ‖w‖ := by
        rw [← add_div]
        gcongr
        norm_num

/-- `‖gammaCoreRemainder w - 1‖ ≤ 64/‖w‖` for `Re w ≥ 0`, `‖w‖ ≥ 4`. -/
theorem norm_gammaCoreRemainder_sub_one_le {w : ℂ} (hw : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) :
    ‖gammaCoreRemainder w - 1‖ ≤ 64 / ‖w‖ := by
  have hnw : 0 < ‖w‖ := by linarith
  rw [gammaCoreRemainder_eq_exp (subset_grDomain hw hw4)]
  have hR := norm_gammaCoreLog_le hw hw4
  have hE := norm_exp_sub_sum_le_norm_mul_exp (gammaCoreLog w) 1
  simp only [range_one, sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one] at hE
  have hR2 : ‖gammaCoreLog w‖ ≤ 2 := by
    refine hR.trans ?_
    rw [div_le_iff₀ hnw]
    linarith
  have hexp : Real.exp ‖gammaCoreLog w‖ ≤ 8 :=
    (Real.exp_le_exp.mpr hR2).trans real_exp_two_lt.le
  calc ‖exp (gammaCoreLog w) - 1‖
      ≤ ‖gammaCoreLog w‖ * Real.exp ‖gammaCoreLog w‖ := hE
    _ ≤ 8 / ‖w‖ * 8 := by gcongr
    _ = 64 / ‖w‖ := by ring

/-! ### Holomorphy of `stirR` and its derivative -/

/-- `stirMain` has derivative `log z + (z - 1/2) / z - 1` at every `z` in the slit plane. -/
lemma hasDerivAt_stirMain {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt stirMain (Complex.log z + (z - 1 / 2) * z⁻¹ - 1) z := by
  have h := ((((hasDerivAt_id z).sub_const (1 / 2 : ℂ)).mul (hasDerivAt_log hz)).sub
    (hasDerivAt_id z)).add_const ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  simp [stirMain]

/-- The derivative of `stirD`, written explicitly. -/
noncomputable def stirDd (z : ℂ) : ℂ :=
  (Complex.log (z + 1) + (z + 1 - 1 / 2) * (z + 1)⁻¹ - 1)
    - (Complex.log z + (z - 1 / 2) * z⁻¹ - 1) - z⁻¹

/-- `stirD` has derivative `stirDd z` at `z` when `z` and `z + 1` lie in the slit plane. -/
lemma hasDerivAt_stirD {z : ℂ} (hz : z ∈ slitPlane) (hz1 : z + 1 ∈ slitPlane) :
    HasDerivAt stirD (stirDd z) z :=
  (((hasDerivAt_stirMain hz1).comp_add_const z 1).sub (hasDerivAt_stirMain hz)).sub
    (hasDerivAt_log hz)

/-- For `Re z > 0` and `j : ℕ`, `x ↦ stirD (x + j)` has derivative `stirDd (z + j)` at `z`. -/
lemma hasDerivAt_stirD_add {z : ℂ} (hz : 0 < z.re) (j : ℕ) :
    HasDerivAt (fun x => stirD (x + j)) (stirDd (z + j)) z := by
  have h1 : 0 < (z + j).re := by
    simp
    positivity
  have h2 : 0 < (z + j + 1).re := by
    simp
    positivity
  exact (hasDerivAt_stirD (Or.inl h1) (Or.inl h2)).comp_add_const z j

/-- `‖stirD (z + j)‖ ≤ 68 * (1 / (1 + j)²)` for `z ∈ stirDomain`. -/
lemma norm_stirD_add_le_stirDomain {z : ℂ} (hz : z ∈ stirDomain) (j : ℕ) :
    ‖stirD (z + j)‖ ≤ 68 * (1 / (1 + j) ^ 2) := by
  refine (norm_stirD_add_le' hz.1.le hz.2.le j).trans ?_
  gcongr
  exact hz.2.le

/-- `stirR` is holomorphic on `stirDomain`. -/
lemma differentiableOn_stirR : DifferentiableOn ℂ stirR stirDomain :=
  differentiableOn_tsum_of_summable_norm (F := fun (j : ℕ) z => stirD (z + j))
    (summable_bound one_pos 68)
    (fun j _ hz => (hasDerivAt_stirD_add hz.1 j).differentiableAt.differentiableWithinAt)
    isOpen_stirDomain (fun j _ hz => norm_stirD_add_le_stirDomain hz j)

/-- On `stirDomain`, the derivative of `stirR` at `s` is the sum of `stirDd (s + j)` over
`j : ℕ`. -/
lemma hasSum_deriv_stirR {s : ℂ} (hs : s ∈ stirDomain) :
    HasSum (fun j : ℕ => stirDd (s + j)) (deriv stirR s) := by
  have := hasSum_deriv_of_summable_norm (F := fun (j : ℕ) z => stirD (z + j))
    (summable_bound one_pos 68)
    (fun j z hz => (hasDerivAt_stirD_add hz.1 j).differentiableAt.differentiableWithinAt)
    isOpen_stirDomain (fun j z hz => norm_stirD_add_le_stirDomain hz j) hs
  rwa [funext fun j : ℕ => (hasDerivAt_stirD_add hs.1 j).deriv] at this

/-- `‖stirDd z‖ ≤ 2 / ‖z‖³` for `Re z ≥ 0` and `‖z‖ ≥ 2`. -/
lemma norm_stirDd_le {z : ℂ} (hz : 0 ≤ z.re) (hz2 : 2 ≤ ‖z‖) :
    ‖stirDd z‖ ≤ 2 / ‖z‖ ^ 3 := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hnz : 0 < ‖z‖ := by linarith
  set t := z⁻¹ with ht
  have htn : ‖t‖ = ‖z‖⁻¹ := norm_inv z
  have ht2 : ‖t‖ ≤ 1 / 2 := by
    rw [htn, inv_le_comm₀ hnz (by norm_num)]
    linarith
  have ht1 : ‖t‖ < 1 := lt_of_le_of_lt ht2 (by norm_num)
  have h1t : 1 / 2 ≤ ‖1 + t‖ := by
    have := norm_sub_le (1 + t) t
    rw [add_sub_cancel_right, norm_one] at this
    linarith
  have h1t0 : 1 + t ≠ 0 := norm_pos_iff.mp (by linarith)
  have hz1 : z + 1 ≠ 0 := by
    intro h
    apply h1t0
    rw [ht, show (1 : ℂ) + z⁻¹ = (z + 1) / z by field_simp, h, zero_div]
  have hid : stirDd z = (Complex.log (1 + t) - (t - t ^ 2 / 2)) - t ^ 3 / (2 * (1 + t)) := by
    rw [stirDd, log_add_one_eq hz hz0, ht]
    field_simp
    ring
  have hT : logTaylor 3 t = t - t ^ 2 / 2 := by
    simp [logTaylor_succ, logTaylor_zero]
    ring
  have hA := norm_log_sub_logTaylor_le 2 ht1
  rw [hT] at hA
  rw [hid]
  have hB : ‖t ^ 3 / (2 * (1 + t))‖ ≤ ‖t‖ ^ 3 := by
    rw [norm_div, norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (by positivity)]
    nlinarith [pow_nonneg (norm_nonneg t) 3]
  calc ‖Complex.log (1 + t) - (t - t ^ 2 / 2) - t ^ 3 / (2 * (1 + t))‖
      ≤ ‖Complex.log (1 + t) - (t - t ^ 2 / 2)‖ + ‖t ^ 3 / (2 * (1 + t))‖ := norm_sub_le _ _
    _ ≤ ‖t‖ ^ (2 + 1) * 2 / (2 + 1) + ‖t‖ ^ 3 := by
        gcongr
        calc ‖Complex.log (1 + t) - (t - t ^ 2 / 2)‖
            ≤ ‖t‖ ^ (2 + 1) * (1 - ‖t‖)⁻¹ / (2 + 1) := by exact_mod_cast hA
          _ ≤ ‖t‖ ^ (2 + 1) * 2 / (2 + 1) := by
            gcongr
            exact inv_one_sub_le_two ht2
    _ ≤ 2 * ‖t‖ ^ 3 := by
        norm_num
        nlinarith [pow_nonneg (norm_nonneg t) 3]
    _ = 2 / ‖z‖ ^ 3 := by
        rw [htn, inv_pow]
        ring

/-- `‖stirDd (s + j)‖ ≤ 4/‖s‖ · 1/(‖s‖ + j)²` for `Re s ≥ 0`, `‖s‖ ≥ 2`. -/
lemma norm_stirDd_add_le {s : ℂ} (hs : 0 ≤ s.re) (hs2 : 2 ≤ ‖s‖) (j : ℕ) :
    ‖stirDd (s + j)‖ ≤ 4 / ‖s‖ * (1 / (‖s‖ + j) ^ 2) := by
  have hre : 0 ≤ (s + j).re := by
    simp
    positivity
  have hn := norm_le_norm_add_nat hs j
  have hsq := sq_norm_add_nat hs j
  have hr : 0 < ‖s‖ := by linarith
  have h2 : (‖s‖ + j) ^ 2 ≤ 2 * ‖s + j‖ ^ 2 := by nlinarith [sq_nonneg (‖s‖ - j)]
  have hsj : 0 < ‖s + j‖ := by linarith
  refine (norm_stirDd_le hre (hs2.trans hn)).trans ?_
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hn h2 (by positivity) (norm_nonneg _)]

/-- `‖deriv stirR s‖ ≤ 6/‖s‖²` on `Re s > 0`, `‖s‖ ≥ 2`. -/
theorem norm_deriv_stirR_le {s : ℂ} (hs : 0 < s.re) (hs2 : 2 ≤ ‖s‖) :
    ‖deriv stirR s‖ ≤ 6 / ‖s‖ ^ 2 := by
  have hr : 0 < ‖s‖ := by linarith
  rw [← (hasSum_deriv_stirR ⟨hs, by linarith⟩).tsum_eq]
  have h1 : ‖∑' j : ℕ, stirDd (s + j)‖ ≤ ∑' j : ℕ, 4 / ‖s‖ * (1 / (‖s‖ + j) ^ 2) :=
    tsum_of_norm_bounded (summable_bound hr _).hasSum (norm_stirDd_add_le hs.le hs2)
  have h2 := tsum_bound_le hr (c := 4 / ‖s‖) (by positivity)
  have h3 : 4 / ‖s‖ * (1 / ‖s‖ ^ 2 + 1 / ‖s‖) ≤ 6 / ‖s‖ ^ 2 := by
    rw [div_add_div _ _ (by positivity) hr.ne', div_mul_div_comm,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hr 4, pow_pos hr 5, pow_pos hr 6]
  linarith

/-! ### Holomorphy of `gammaCoreRemainder` and its logarithmic derivative -/

/-- Explicit derivative of `gammaCoreLog`. -/
noncomputable def gammaCoreLogDeriv (w : ℂ) : ℂ :=
  deriv stirR (w / 2 + 1 / 4) * (1 / 2)
    + ((1 / 2) * (Complex.log (w / 2 + 1 / 4) - Complex.log (w / 2))
      + (w / 2 - 1 / 4) * ((w / 2 + 1 / 4)⁻¹ * (1 / 2) - (w / 2)⁻¹ * (1 / 2)))

/-- `gammaCoreLog` has derivative `gammaCoreLogDeriv w` at every `w ∈ grDomain`. -/
lemma hasDerivAt_gammaCoreLog {w : ℂ} (hw : w ∈ grDomain) :
    HasDerivAt gammaCoreLog (gammaCoreLogDeriv w) w := by
  obtain ⟨hs, -, hu⟩ := grDomain_props hw
  have hin : HasDerivAt (fun x : ℂ => x / 2 + 1 / 4) (1 / 2) w :=
    ((hasDerivAt_id w).div_const 2).add_const (1 / 4)
  have hR : HasDerivAt (fun x : ℂ => stirR (x / 2 + 1 / 4))
      (deriv stirR (w / 2 + 1 / 4) * (1 / 2)) w :=
    ((differentiableOn_stirR.differentiableAt
      (isOpen_stirDomain.mem_nhds hs)).hasDerivAt).comp (h₂ := stirR) w hin
  have hL1 : HasDerivAt (fun x : ℂ => Complex.log (x / 2 + 1 / 4))
      ((w / 2 + 1 / 4)⁻¹ * (1 / 2)) w :=
    (hasDerivAt_log (Or.inl hs.1)).comp (h₂ := Complex.log) w hin
  have hL2 : HasDerivAt (fun x : ℂ => Complex.log (x / 2)) ((w / 2)⁻¹ * (1 / 2)) w :=
    (hasDerivAt_log hu).comp (h₂ := Complex.log) w ((hasDerivAt_id' w).div_const 2)
  have hP : HasDerivAt (fun x : ℂ => x / 2 - 1 / 4) (1 / 2) w :=
    ((hasDerivAt_id w).div_const 2).sub_const (1 / 4)
  have h := (hR.add (hP.mul (hL1.sub hL2))).sub_const (1 / 4 : ℂ)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  · simp only [gammaCoreLogDeriv, Pi.sub_apply]
  · simp [gammaCoreLog]

/-- Near every `w ∈ grDomain`, `gammaCoreRemainder` agrees with `exp ∘ gammaCoreLog`. -/
lemma gammaCoreRemainder_eventuallyEq {w : ℂ} (hw : w ∈ grDomain) :
    gammaCoreRemainder =ᶠ[𝓝 w] fun x => exp (gammaCoreLog x) := by
  filter_upwards [isOpen_grDomain.mem_nhds hw] with x hx
  exact gammaCoreRemainder_eq_exp hx

/-- `gammaCoreRemainder` is holomorphic on the open set `grDomain`. -/
theorem differentiableOn_gammaCoreRemainder : DifferentiableOn ℂ gammaCoreRemainder grDomain :=
  fun _ hw => ((hasDerivAt_gammaCoreLog hw).cexp.differentiableAt.congr_of_eventuallyEq
    (gammaCoreRemainder_eventuallyEq hw)).differentiableWithinAt

/-- `gammaCoreRemainder` does not vanish on `grDomain`. -/
theorem gammaCoreRemainder_ne_zero {w : ℂ} (hw : w ∈ grDomain) : gammaCoreRemainder w ≠ 0 := by
  rw [gammaCoreRemainder_eq_exp hw]
  exact exp_ne_zero _

/-- The logarithmic derivative of `gammaCoreRemainder` is the derivative of its logarithm. -/
theorem logDeriv_gammaCoreRemainder {w : ℂ} (hw : w ∈ grDomain) :
    logDeriv gammaCoreRemainder w = gammaCoreLogDeriv w := by
  have hd : HasDerivAt gammaCoreRemainder
      (exp (gammaCoreLog w) * gammaCoreLogDeriv w) w :=
    ((hasDerivAt_gammaCoreLog hw).cexp).congr_of_eventuallyEq
      (gammaCoreRemainder_eventuallyEq hw)
  rw [logDeriv_apply, hd.deriv, gammaCoreRemainder_eq_exp hw]
  field_simp [exp_ne_zero]

/-- The elementary part of the derivative is `O(1/‖w‖²)` on `Re w ≥ 0`. -/
lemma norm_elem_deriv_le {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 ≤ ‖w‖) :
    ‖(1 / 2) * (Complex.log (w / 2 + 1 / 4) - Complex.log (w / 2))
      + (w / 2 - 1 / 4) * ((w / 2 + 1 / 4)⁻¹ * (1 / 2) - (w / 2)⁻¹ * (1 / 2))‖
      ≤ 5 / 8 / ‖w‖ ^ 2 := by
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [log_half_add_quarter_sub_log_half hw hw0]
  have hnw : 0 < ‖w‖ := by linarith
  set t : ℂ := 1 / (2 * w) with htdef
  have htn : ‖t‖ = 1 / (2 * ‖w‖) := by
    rw [htdef, norm_div, norm_mul]
    norm_num
  have ht2 : ‖t‖ ≤ 1 / 2 := by
    rw [htn, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have ht1 : ‖t‖ < 1 := lt_of_le_of_lt ht2 (by norm_num)
  have h1t : 1 / 2 ≤ ‖1 + t‖ := by
    have := norm_sub_le (1 + t) t
    rw [add_sub_cancel_right, norm_one] at this
    linarith
  have h1t0 : 1 + t ≠ 0 := norm_pos_iff.mp (by linarith)
  have hid : (1 / 2) * Complex.log (1 + t)
      + (w / 2 - 1 / 4) * ((w / 2 + 1 / 4)⁻¹ * (1 / 2) - (w / 2)⁻¹ * (1 / 2))
      = (1 / 2) * ((Complex.log (1 + t) - t) + 2 * t ^ 2 / (1 + t)) := by
    generalize Complex.log (1 + t) = L
    have hq : (2 * w + 1) ≠ 0 := by
      intro h
      apply h1t0
      rw [htdef, show (1 : ℂ) + 1 / (2 * w) = (2 * w + 1) / (2 * w) by field_simp, h, zero_div]
    have e1 : (w / 2 + 1 / 4)⁻¹ = 4 * (2 * w + 1)⁻¹ := by
      rw [show w / 2 + 1 / 4 = (2 * w + 1) / 4 by ring, inv_div, div_eq_mul_inv, mul_comm]
    have e3 : 2 * t ^ 2 / (1 + t) = w⁻¹ * (2 * w + 1)⁻¹ := by
      rw [htdef]
      field_simp
    have e4 : t = w⁻¹ / 2 := by
      rw [htdef]
      field_simp
    rw [e1, show (w / 2)⁻¹ = 2 * w⁻¹ by rw [inv_div, div_eq_mul_inv], e3, e4]
    linear_combination ((2 * w + 1)⁻¹ - 1 / 2) * mul_inv_cancel₀ hw0 +
      (1 / 2 - w⁻¹ / 2) * mul_inv_cancel₀ hq
  rw [hid]
  have hC : ‖2 * t ^ 2 / (1 + t)‖ ≤ 4 * ‖t‖ ^ 2 := by
    rw [norm_div, norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg ‖t‖]
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  calc 1 / 2 * ‖Complex.log (1 + t) - t + 2 * t ^ 2 / (1 + t)‖
      ≤ 1 / 2 * (‖Complex.log (1 + t) - t‖ + ‖2 * t ^ 2 / (1 + t)‖) := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 1 / 2 * (‖t‖ ^ 2 * 2 / 2 + 4 * ‖t‖ ^ 2) := by
        gcongr
        calc ‖Complex.log (1 + t) - t‖ ≤ ‖t‖ ^ 2 * (1 - ‖t‖)⁻¹ / 2 :=
            norm_log_one_add_sub_self_le ht1
          _ ≤ ‖t‖ ^ 2 * 2 / 2 := by
            gcongr
            exact inv_one_sub_le_two ht2
    _ = 5 / 8 / ‖w‖ ^ 2 := by
        rw [htn]
        field_simp
        ring

/-- `‖logDeriv gammaCoreRemainder w‖ ≤ 13/‖w‖²` for `Re w ≥ 0`, `‖w‖ ≥ 4`. -/
theorem norm_logDeriv_gammaCoreRemainder_le {w : ℂ} (hw : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) :
    ‖logDeriv gammaCoreRemainder w‖ ≤ 13 / ‖w‖ ^ 2 := by
  have hnw : 0 < ‖w‖ := by linarith
  rw [logDeriv_gammaCoreRemainder (subset_grDomain hw hw4), gammaCoreLogDeriv]
  have hs := norm_half_le_norm_s hw
  have hsre : 0 < (w / 2 + 1 / 4).re := by
    simp
    linarith
  have hD := norm_deriv_stirR_le hsre (by linarith)
  have hD' : ‖deriv stirR (w / 2 + 1 / 4) * (1 / 2)‖ ≤ 12 / ‖w‖ ^ 2 := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    calc ‖deriv stirR (w / 2 + 1 / 4)‖ * (1 / 2) ≤ 6 / (‖w‖ / 2) ^ 2 * (1 / 2) := by
          gcongr
          exact hD.trans (by gcongr)
      _ = 12 / ‖w‖ ^ 2 := by
          field_simp
          ring
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ 12 / ‖w‖ ^ 2 + 5 / 8 / ‖w‖ ^ 2 := add_le_add hD' (norm_elem_deriv_le hw (by linarith))
    _ ≤ 13 / ‖w‖ ^ 2 := by
        rw [← add_div]
        gcongr
        norm_num

/-! ### Digamma form -/

/-- Near every `s ∈ stirDomain`, `Γ` agrees with `z ↦ exp (stirMain z + stirR z)`. -/
lemma Gamma_eventuallyEq {s : ℂ} (hs : s ∈ stirDomain) :
    Complex.Gamma =ᶠ[𝓝 s] fun z => exp (stirMain z + stirR z) := by
  filter_upwards [isOpen_stirDomain.mem_nhds hs] with z hz
  exact Gamma_eq_exp_stirMain_add hz.1.le hz.2.le

/-- On `stirDomain`, `Γ'(s)/Γ(s) = log s + (s - 1/2)/s - 1 + stirR'(s)`. -/
lemma logDeriv_Gamma_eq {s : ℂ} (hs : s ∈ stirDomain) :
    logDeriv Complex.Gamma s = Complex.log s + (s - 1 / 2) * s⁻¹ - 1 + deriv stirR s := by
  have hR := (differentiableOn_stirR.differentiableAt (isOpen_stirDomain.mem_nhds hs)).hasDerivAt
  have hd := (((hasDerivAt_stirMain (Or.inl hs.1)).add hR).cexp).congr_of_eventuallyEq
    (Gamma_eventuallyEq hs)
  simp only [Pi.add_apply] at hd
  rw [logDeriv_apply, hd.deriv, Gamma_eq_exp_stirMain_add hs.1.le hs.2.le]
  field_simp [exp_ne_zero]

/-- On `grDomain`,
`logDeriv gammaCoreRemainder w = ½ ψ(w/2+1/4) − ½ log(w/2) + 1/(4w)`. -/
theorem logDeriv_gammaCoreRemainder_eq_digamma {w : ℂ} (hw : w ∈ grDomain) :
    logDeriv gammaCoreRemainder w =
      1 / 2 * Complex.digamma (w / 2 + 1 / 4) - 1 / 2 * Complex.log (w / 2) +
        1 / (4 * w) := by
  obtain ⟨hs, hu0, -⟩ := grDomain_props hw
  have hw0 : w ≠ 0 := fun h => hu0 (by rw [h, zero_div])
  have hs0 : w / 2 + 1 / 4 ≠ 0 := fun h => hs.1.ne' (by rw [h, zero_re])
  rw [Complex.digamma_def, logDeriv_gammaCoreRemainder hw, logDeriv_Gamma_eq hs, gammaCoreLogDeriv]
  field_simp
  ring

end GammaCore

end RiemannJensen
