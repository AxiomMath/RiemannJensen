module

public import RiemannJensen.MainTheorem.Counting
public import RiemannJensen.MainTheorem.WindowLoss
public import RiemannJensen.Dedekind.Foundation

/-!
# Final root-count assembly for Dedekind Jensen polynomials

The eventual square-root lower bound for the number of distinct negative roots
of the Jensen polynomials `dedekindJensen ξ d` of a candidate completed
function `ξ`, and the main statement packaged from it, derived from explicit
analytic inputs: the scale identities, the oscillatory formula on the counting
window, the polar form of the leading saddle term, continuity of the phase,
and the endpoint phase-span bound.

The only nondegeneracy assumption on the Jensen polynomials is eventual
nonvanishing `dedekindJensen ξ d ≠ 0`; neither the degree nor the leading
coefficient is used.
-/

@[expose] public section

namespace RiemannJensen.DedekindFinalAssembly

open Set Polynomial Filter Topology

variable (ξ : ℂ → ℂ)

/-! ### Rescaled reciprocal and root transport -/

/-- The rescaled degree-padded reciprocal
`A_d(X) = (T² / d)^d R_d(d X / T²)` at saddle scale `T`. -/
noncomputable def rescaledReciprocal (T : ℝ) (d : ℕ) : ℝ[X] :=
  C ((T ^ 2 / (d : ℝ)) ^ d) *
    (dedekindReciprocal ξ d).comp (C ((d : ℝ) / T ^ 2) * X)

/-- Evaluation of the rescaled reciprocal:
`A_d(x) = (T² / d)^d R_d(d x / T²)`. -/
theorem eval_rescaledReciprocal (T : ℝ) (d : ℕ) (x : ℝ) :
    (rescaledReciprocal ξ T d).eval x =
      (T ^ 2 / (d : ℝ)) ^ d *
        (dedekindReciprocal ξ d).eval (((d : ℝ) / T ^ 2) * x) := by
  simp [rescaledReciprocal]

/-- `A_d(-q) = (-q)^d J_d(-T² / (d q))` for `d ≥ 1`, `T ≠ 0`, `q ≠ 0`. -/
theorem rescaledReciprocal_eval_neg (T : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hT : T ≠ 0) {q : ℝ} (hq : q ≠ 0) :
    (rescaledReciprocal ξ T d).eval (-q) =
      (-q) ^ d * (dedekindJensen ξ d).eval (-T ^ 2 / ((d : ℝ) * q)) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hd)
  rw [eval_rescaledReciprocal, eval_dedekindReciprocal_eq ξ d
    (mul_ne_zero (div_ne_zero hd0 (pow_ne_zero 2 hT)) (neg_ne_zero.mpr hq)), ← mul_assoc,
    ← mul_pow]
  congr 2 <;> field_simp

/-- A zero `A_d(-q) = 0` with `q > 0` gives the negative Jensen root
`-T² / (d q)`. -/
theorem rescaledReciprocal_root_transport (T : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hT : T ≠ 0) {q : ℝ} (hq : 0 < q)
    (hroot : (rescaledReciprocal ξ T d).eval (-q) = 0) :
    -T ^ 2 / ((d : ℝ) * q) < 0 ∧
      (dedekindJensen ξ d).eval (-T ^ 2 / ((d : ℝ) * q)) = 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨reciprocalRootArgument_neg (by positivity) (mul_pos hdR hq), ?_⟩
  rw [rescaledReciprocal_eval_neg ξ T d hd hT hq.ne'] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left
    (pow_ne_zero d (neg_ne_zero.mpr hq.ne'))

/-- An oscillatory formula for `A_d(-q)` on a positive interval with phase span
`(n + 1)π` gives `n` distinct negative roots of a nonzero `J_d`. -/
theorem le_negativeRootCount_of_phaseSpan (T : ℝ) (d : ℕ) {n : ℕ}
    (hd : 1 ≤ d) (hT : T ≠ 0) (hJ : dedekindJensen ξ d ≠ 0)
    (R E θ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hθcont : ContinuousOn θ (Icc a b))
    (hR : ∀ q ∈ Icc a b, 0 < R q)
    (hE : ∀ q ∈ Icc a b, |E q| < 1 / 2)
    (hformula : ∀ q ∈ Icc a b,
      (rescaledReciprocal ξ T d).eval (-q) = 2 * R q * (Real.cos (θ q) + E q))
    (hspan : ((n + 1 : ℕ) : ℝ) * Real.pi ≤ θ b - θ a) :
    n ≤ dedekindNegativeRootCount ξ d := by
  have hPcont : ContinuousOn (fun x => (rescaledReciprocal ξ T d).eval (-x))
      (Icc a b) :=
    ((rescaledReciprocal ξ T d).continuous.comp continuous_neg).continuousOn
  obtain ⟨q, hq_inj, hq⟩ := phaseCrossings_of_phaseSpan
    (fun x => (rescaledReciprocal ξ T d).eval (-x)) R E θ a b n hab hPcont
    hθcont hR hE hformula hspan
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hd)
  have hpos : ∀ i, 0 < q i := fun i => ha.trans (hq i).1.1
  exact le_negativeDistinctRootCount_of_injective hJ
    (fun i => -T ^ 2 / ((d : ℝ) * q i))
    (reciprocalRootArgument_injective (pow_ne_zero 2 hT)
      (fun i j hij => hq_inj (mul_left_cancel₀ hd0 hij)))
    (fun i => (rescaledReciprocal_root_transport ξ T d hd hT (hpos i) (hq i).2).1)
    (fun i => (rescaledReciprocal_root_transport ξ T d hd hT (hpos i) (hq i).2).2)

/-! ### Rounding a real phase loss -/

/-- Natural rounding of a real phase loss: `L(E) = ⌈max 0 (E / π)⌉ + 2`. -/
noncomputable def phaseLossNat (E : ℝ) : ℕ :=
  ⌈max 0 (E / Real.pi)⌉₊ + 2

/-- `L(E) ≤ d` and `Δ ≥ π d - E` give the integral phase span
`(d - L(E) + 1) π ≤ Δ`. -/
theorem phaseLossNat_span {E Δ : ℝ} {d : ℕ}
    (hLd : phaseLossNat E ≤ d) (hΔ : Real.pi * d - E ≤ Δ) :
    (((d - phaseLossNat E) + 1 : ℕ) : ℝ) * Real.pi ≤ Δ := by
  have hpi := Real.pi_pos
  set c : ℕ := ⌈max 0 (E / Real.pi)⌉₊ with hc
  have hL : phaseLossNat E = c + 2 := rfl
  have hEc : E ≤ c * Real.pi :=
    (div_le_iff₀ hpi).mp ((le_max_right 0 (E / Real.pi)).trans (Nat.le_ceil _))
  have hcast : (((d - phaseLossNat E) + 1 : ℕ) : ℝ) = (d : ℝ) - c - 1 := by
    rw [hL] at hLd ⊢
    rw [Nat.cast_add, Nat.cast_sub hLd]
    push_cast
    ring
  rw [hcast]
  nlinarith

/-- `L(E) ≤ E / π + 3` for `E ≥ 0`. -/
theorem phaseLossNat_le {E : ℝ} (hE : 0 ≤ E) :
    (phaseLossNat E : ℝ) ≤ E / Real.pi + 3 := by
  have hx : 0 ≤ E / Real.pi := div_nonneg hE Real.pi_pos.le
  have hceil := Nat.ceil_lt_add_one hx
  rw [phaseLossNat, max_eq_right hx]
  push_cast
  linarith

/-- Under the oscillatory formula on a positive interval, a phase increase at
least `π d - E` gives `d - L(E) ≤ n_d`. -/
theorem sub_phaseLossNat_le_negativeRootCount (T : ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hT : T ≠ 0) (hJ : dedekindJensen ξ d ≠ 0)
    (R E₀ θ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hθcont : ContinuousOn θ (Icc a b))
    (hR : ∀ q ∈ Icc a b, 0 < R q)
    (hE₀ : ∀ q ∈ Icc a b, |E₀ q| < 1 / 2)
    (hformula : ∀ q ∈ Icc a b,
      (rescaledReciprocal ξ T d).eval (-q) =
        2 * R q * (Real.cos (θ q) + E₀ q))
    {E : ℝ} (hΔ : Real.pi * d - E ≤ θ b - θ a) :
    (d : ℝ) - phaseLossNat E ≤ (dedekindNegativeRootCount ξ d : ℝ) := by
  by_cases hLd : phaseLossNat E ≤ d
  · have hcount : ((d - phaseLossNat E : ℕ) : ℝ) ≤
        (dedekindNegativeRootCount ξ d : ℝ) := by
      exact_mod_cast le_negativeRootCount_of_phaseSpan ξ T d hd hT hJ R E₀ θ a b
        ha hab hθcont hR hE₀ hformula (phaseLossNat_span hLd hΔ)
    rwa [Nat.cast_sub hLd] at hcount
  · have hlt : (d : ℝ) < phaseLossNat E := by
      exact_mod_cast Nat.lt_of_not_ge hLd
    have hnn : (0 : ℝ) ≤ dedekindNegativeRootCount ξ d := by positivity
    linarith

/-! ### From the leading term to the oscillatory form -/

/-- Pointwise conversion: if `Z = |Z| e^{iφ}` is nonzero and
`|A - 2 Re Z| ≤ ε |Z|` with `ε < 1`, then `A = 2|Z|(cos φ + E₀)` with
`E₀ = (A - 2 Re Z) / (2|Z|)` and `|E₀| < 1/2`. -/
theorem oscillatory_form_of_polar {A : ℝ} {Z : ℂ} {φ ε : ℝ} (hZ : Z ≠ 0)
    (hpolar : Z = (‖Z‖ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
    (hε : ε < 1) (hosc : |A - 2 * Z.re| ≤ ε * ‖Z‖) :
    0 < ‖Z‖ ∧ |(A - 2 * Z.re) / (2 * ‖Z‖)| < 1 / 2 ∧
      A = 2 * ‖Z‖ * (Real.cos φ + (A - 2 * Z.re) / (2 * ‖Z‖)) := by
  have hn : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hre : Z.re = ‖Z‖ * Real.cos φ := by
    have h := congrArg Complex.re hpolar
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im] at h
    linarith
  refine ⟨hn, ?_, ?_⟩
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * ‖Z‖),
      div_lt_iff₀ (by positivity)]
    nlinarith
  · field_simp
    linarith

/-- The polar form `Z = |Z| e^{iθ}` of a nonvanishing leading term with
`|A_d(-q) - 2 Re Z(q)| ≤ ε |Z(q)|`, `ε < 1`, and a phase increase at least
`π d - E` give `d - L(E) ≤ n_d`. -/
theorem sub_phaseLossNat_le_negativeRootCount_of_polar (T : ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hT : T ≠ 0) (hJ : dedekindJensen ξ d ≠ 0)
    (Z : ℝ → ℂ) (θ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hθcont : ContinuousOn θ (Icc a b)) (hZ : ∀ q ∈ Icc a b, Z q ≠ 0)
    (hpolar : ∀ q ∈ Icc a b, Z q = (‖Z q‖ : ℂ) * Complex.exp ((θ q : ℂ) * Complex.I))
    {ε : ℝ} (hε : ε < 1)
    (hosc : ∀ q ∈ Icc a b,
      |(rescaledReciprocal ξ T d).eval (-q) - 2 * (Z q).re| ≤ ε * ‖Z q‖)
    {E : ℝ} (hΔ : Real.pi * d - E ≤ θ b - θ a) :
    (d : ℝ) - phaseLossNat E ≤ (dedekindNegativeRootCount ξ d : ℝ) := by
  have h q (hq : q ∈ Icc a b) := oscillatory_form_of_polar (hZ q hq) (hpolar q hq) hε (hosc q hq)
  exact sub_phaseLossNat_le_negativeRootCount ξ T d hd hT hJ (fun q => ‖Z q‖)
    (fun q => ((rescaledReciprocal ξ T d).eval (-q) - 2 * (Z q).re) / (2 * ‖Z q‖)) θ a b
    ha hab hθcont (fun q hq => (h q hq).1) (fun q hq => (h q hq).2.1)
    (fun q hq => (h q hq).2.2) hΔ

/-! ### Window losses -/

/-- The edge offset `τ_{M,d} = M √(log d / d)`. -/
noncomputable def edgeOffset (M : ℝ) (d : ℕ) : ℝ :=
  M * Real.sqrt (Real.log d / d)

/-- `τ_{M,d} ≥ 0` for `M ≥ 0`. -/
theorem edgeOffset_nonneg {M : ℝ} (hM : 0 ≤ M) (d : ℕ) : 0 ≤ edgeOffset M d :=
  mul_nonneg hM (Real.sqrt_nonneg _)

/-- `τ_{M,d} > 0` for `M > 0` and `d ≥ 2`. -/
theorem edgeOffset_pos {M : ℝ} (hM : 0 < M) {d : ℕ} (hd : 2 ≤ d) :
    0 < edgeOffset M d := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  exact mul_pos hM (Real.sqrt_pos.mpr (div_pos (Real.log_pos hdR) (by linarith)))

/-- `τ_{M,d} ≤ M` for `d ≥ 1`, since `log d ≤ d`. -/
theorem edgeOffset_le {M : ℝ} (hM : 0 ≤ M) {d : ℕ} (hd : 1 ≤ d) :
    edgeOffset M d ≤ M := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact mul_le_of_le_one_right hM (Real.sqrt_le_one.mpr ((div_le_one hdR).mpr
    ((Real.log_le_sub_one_of_pos hdR).trans (by linarith))))

/-- Edge counting-window loss: `d τ_{M,d}^{3/2} ≤ M √M √(d log d)` for
`d ≥ 1`. -/
theorem edge_window_loss {M : ℝ} (hM : 0 ≤ M) {d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) * edgeOffset M d ^ (3 / 2 : ℝ) ≤
      M * Real.sqrt M * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
  have hrpow : edgeOffset M d ^ (3 / 2 : ℝ) =
      edgeOffset M d * Real.sqrt (edgeOffset M d) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' (edgeOffset_nonneg hM d) (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]
  have hdτ : (d : ℝ) * edgeOffset M d = M * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
    rw [edgeOffset, ← nat_mul_sqrt_log_div_nat hd]
    ring
  rw [hrpow, ← mul_assoc, hdτ]
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (edgeOffset_le hM hd))
    (mul_nonneg hM (Real.sqrt_nonneg _))).trans_eq (by ring)

/-- A scale with `N T Λ = 4 π d`, `N, Λ > 0` and `d ≥ 1` has `T > 0`. -/
theorem pos_of_scale_product {N T Λ : ℝ} {d : ℕ} (hN : 0 < N) (hΛ : 0 < Λ) (hd : 1 ≤ d)
    (h : N * T * Λ = 4 * Real.pi * d) : 0 < T := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  by_contra hT
  have : N * T * Λ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hN.le (not_lt.mp hT)) hΛ.le
  nlinarith [Real.pi_pos]

/-- Upper counting-window loss for a scale with `N T_d Λ_d = 4 π d`,
`0 < Λ_d` and `Λ_d ≤ B log d` from `D` onward:
`d / √(c₀ T_d) ≤ C √(d log d)`. -/
theorem exists_upper_window_loss_bound_of_scale {N c₀ B : ℝ} (hN : 0 < N)
    (hc₀ : 0 < c₀) (hB : 0 < B) (T Λ : ℕ → ℝ) {D : ℕ}
    (hprod : ∀ d : ℕ, D ≤ d → N * T d * Λ d = 4 * Real.pi * d)
    (hΛpos : ∀ d : ℕ, D ≤ d → 0 < Λ d)
    (hΛ : ∀ d : ℕ, D ≤ d → Λ d ≤ B * Real.log d) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, D ≤ d → 1 ≤ d →
      (d : ℝ) / Real.sqrt (c₀ * T d) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
  refine ⟨Real.sqrt (N * B / (4 * Real.pi * c₀)), by positivity, ?_⟩
  intro d hDd hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hprodd := hprod d hDd
  have hcT : 0 < c₀ * T d := mul_pos hc₀ (pos_of_scale_product hN (hΛpos d hDd) hd hprodd)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, Real.sq_sqrt hcT.le, mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N * B / (4 * Real.pi * c₀)),
    Real.sq_sqrt (mul_nonneg hdR.le hlog), div_le_iff₀ hcT]
  have hfinal : (d : ℝ) ^ 2 =
      (d : ℝ) * (N * Λ d) / (4 * Real.pi * c₀) * (c₀ * T d) := by
    field_simp
    nlinarith [hprodd]
  rw [hfinal]
  apply mul_le_mul_of_nonneg_right _ hcT.le
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (hΛ d hDd) (mul_nonneg hdR.le hN.le)]

/-- `C (log d)^{-1/10} < 1` for all large `d`. -/
theorem eventually_mul_log_rpow_lt_one (C : ℝ) :
    ∀ᶠ d : ℕ in atTop, C * Real.log (d : ℝ) ^ (-(1 / 10 : ℝ)) < 1 := by
  have h : Tendsto (fun d : ℕ => Real.log (d : ℝ) ^ (-(1 / 10 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine (h.const_mul C).eventually (gt_mem_nhds ?_)
  simp

/-- If `d X ≤ K s` and `1 ≤ s`, the rounded loss of `C d X + C` is at most
`(C (K + 1) / π + 3) s`. -/
theorem phaseLossNat_le_of_window_bound {C K X d s : ℝ} (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hd : 0 ≤ d) (hdX : d * X ≤ K * s) (hs : 1 ≤ s) :
    (phaseLossNat (C * d * X + C) : ℝ) ≤ (C * (K + 1) / Real.pi + 3) * s := by
  have hle : C * d * X + C ≤ C * (K + 1) * s := by
    nlinarith [mul_le_mul_of_nonneg_left hdX hC, mul_le_mul_of_nonneg_left hs hC]
  have hdiv := div_le_div_of_nonneg_right hle Real.pi_pos.le
  rw [mul_div_right_comm] at hdiv
  rw [add_mul]
  linarith [phaseLossNat_le (add_nonneg (mul_nonneg (mul_nonneg hC hd) hX) hC)]

/-! ### The analytic inputs -/

/-- The explicit analytic inputs of the root count for the Jensen polynomials
of `ξ`, at fixed window parameters `M, c₀ > 0`. The counting window is
`I_d = [q_{e,d} + τ_{M,d}, c₀ T_d]`; the rescaled reciprocal is
`A_d = rescaledReciprocal ξ (T d) d`. -/
structure Inputs where
  /-- The field degree `N`. -/
  N : ℝ
  N_pos : 0 < N
  /-- The saddle scale `T_d`. -/
  T : ℕ → ℝ
  /-- The logarithmic scale `Λ_d`. -/
  Λ : ℕ → ℝ
  /-- Exact scale product `N T_d Λ_d = 4 π d`, eventually. -/
  scale_product : ∀ᶠ d : ℕ in atTop, N * T d * Λ d = 4 * Real.pi * d
  /-- Positivity of the logarithmic scale, eventually. -/
  scale_lambda_pos : ∀ᶠ d : ℕ in atTop, 0 < Λ d
  /-- Upper logarithmic scale bound `Λ_d ≤ 3 log d`, eventually. -/
  scale_lambda_upper : ∀ᶠ d : ℕ in atTop, Λ d ≤ 3 * Real.log d
  /-- The saddle edge `q_{e,d}`. -/
  qe : ℕ → ℝ
  /-- The saddle edge is nonnegative, eventually. -/
  qe_nonneg : ∀ᶠ d : ℕ in atTop, 0 ≤ qe d
  /-- The constant `M` of the edge offset `τ_{M,d}`. -/
  M : ℝ
  /-- The constant `c₀` of the upper window endpoint `c₀ T_d`. -/
  c₀ : ℝ
  /-- The edge-offset constant is positive. -/
  M_pos : 0 < M
  /-- The window-endpoint constant is positive. -/
  c₀_pos : 0 < c₀
  /-- Eventual Jensen nonvanishing. -/
  jensen_ne_zero : ∀ᶠ d : ℕ in atTop, dedekindJensen ξ d ≠ 0
  /-- The counting window is eventually nonempty. -/
  window_nonempty : ∀ᶠ d : ℕ in atTop, qe d + edgeOffset M d ≤ c₀ * T d
  /-- The leading saddle contribution `Z_d(q)`. -/
  Z : ℕ → ℝ → ℂ
  /-- The uniform oscillatory formula
  `A_d(-q) = 2 Re Z_d(q) + O(|Z_d(q)| (log d)^{-1/10})` on the window. -/
  oscillation : ∃ C : ℝ, ∀ᶠ d : ℕ in atTop,
    ∀ q ∈ Icc (qe d + edgeOffset M d) (c₀ * T d),
      |(rescaledReciprocal ξ (T d) d).eval (-q) - 2 * (Z d q).re| ≤
        C * ‖Z d q‖ * Real.log (d : ℝ) ^ (-(1 / 10 : ℝ))
  /-- The leading term does not vanish on the window. -/
  leading_ne_zero : ∀ᶠ d : ℕ in atTop,
    ∀ q ∈ Icc (qe d + edgeOffset M d) (c₀ * T d), Z d q ≠ 0
  /-- The saddle action `S_d`. -/
  S : ℕ → ℝ → ℝ
  /-- The phase correction `ω_d`. -/
  ω : ℕ → ℝ → ℝ
  /-- Exact polar form `Z_d(q) = |Z_d(q)| exp(i (d S_d(q) + ω_d(q)))` on the
  window. -/
  leading_polar : ∀ᶠ d : ℕ in atTop,
    ∀ q ∈ Icc (qe d + edgeOffset M d) (c₀ * T d),
      Z d q = (‖Z d q‖ : ℂ) *
        Complex.exp ((((d : ℝ) * S d q + ω d q : ℝ) : ℂ) * Complex.I)
  /-- Continuity of the phase correction on the window. -/
  phase_correction_continuous : ∀ᶠ d : ℕ in atTop,
    ContinuousOn (ω d) (Icc (qe d + edgeOffset M d) (c₀ * T d))
  /-- Continuity of the saddle action on the window. -/
  action_continuous : ∀ᶠ d : ℕ in atTop,
    ContinuousOn (S d) (Icc (qe d + edgeOffset M d) (c₀ * T d))
  /-- Endpoint phase-span bound: the increase of `d S_d + ω_d` across the window
  is at least `π d - C d (Q_{c₀,d}^{-1/2} + τ_{M,d}^{3/2}) - C`. -/
  phase_span : ∃ C : ℝ, ∀ᶠ d : ℕ in atTop,
    Real.pi * d - C * d * ((c₀ * T d) ^ (-(1 / 2 : ℝ)) +
        edgeOffset M d ^ (3 / 2 : ℝ)) - C ≤
      ((d : ℝ) * S d (c₀ * T d) + ω d (c₀ * T d)) -
        ((d : ℝ) * S d (qe d + edgeOffset M d) + ω d (qe d + edgeOffset M d))

/-! ### Assembly -/

/-- Eventual distinct negative Jensen roots: there are `C > 0` and `D` with
`d - C √(d log d) ≤ n_d` for every `d ≥ D`. -/
theorem eventual_negativeRootCount_bound (I : Inputs ξ) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      (d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (dedekindNegativeRootCount ξ d : ℝ) := by
  obtain ⟨C₁, hosc⟩ := I.oscillation
  obtain ⟨C₂, hspan⟩ := I.phase_span
  have hall := (eventually_ge_atTop 2).and (I.scale_product.and
    (I.scale_lambda_pos.and (I.scale_lambda_upper.and (I.qe_nonneg.and
    (I.jensen_ne_zero.and (I.window_nonempty.and (hosc.and
    (I.leading_ne_zero.and (I.leading_polar.and
    (I.phase_correction_continuous.and (I.action_continuous.and (hspan.and
    (eventually_mul_log_rpow_lt_one C₁)))))))))))))
  obtain ⟨D, hD⟩ := eventually_atTop.mp hall
  obtain ⟨Cup, hCup, hup⟩ := exists_upper_window_loss_bound_of_scale I.N_pos
    I.c₀_pos (by norm_num : (0 : ℝ) < 3) I.T I.Λ (D := D)
    (fun d hd => (hD d hd).2.1) (fun d hd => (hD d hd).2.2.1)
    (fun d hd => (hD d hd).2.2.2.1)
  set C₂' := max C₂ 0
  set C₀ := C₂' * (Cup + I.M * Real.sqrt I.M + 1) with hC₀
  have hC₂'0 : 0 ≤ C₂' := le_max_right _ _
  have hMsq : 0 ≤ I.M * Real.sqrt I.M := mul_nonneg I.M_pos.le (Real.sqrt_nonneg _)
  have hC₀0 : 0 ≤ C₀ := mul_nonneg hC₂'0 (by linarith)
  refine ⟨C₀ / Real.pi + 3, by positivity, D, fun d hDd => ?_⟩
  obtain ⟨h2, hprod, hΛpos, -, hqe, hJ, hwin, hoscd, hZne, hpol, hωc, hSc,
    hspand, hsmall⟩ := hD d hDd
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hT : 0 < I.T d := pos_of_scale_product I.N_pos hΛpos hd1 hprod
  set a := I.qe d + edgeOffset I.M d
  set b := I.c₀ * I.T d
  have ha : 0 < a := by linarith [edgeOffset_pos I.M_pos h2]
  have hcT : 0 ≤ I.c₀ * I.T d := mul_nonneg I.c₀_pos.le hT.le
  have hX0 : 0 ≤ (I.c₀ * I.T d) ^ (-(1 / 2 : ℝ)) + edgeOffset I.M d ^ (3 / 2 : ℝ) :=
    add_nonneg (Real.rpow_nonneg hcT _)
      (Real.rpow_nonneg (edgeOffset_nonneg I.M_pos.le d) _)
  have hΔ : Real.pi * d - (C₂' * d * ((I.c₀ * I.T d) ^ (-(1 / 2 : ℝ)) +
        edgeOffset I.M d ^ (3 / 2 : ℝ)) + C₂') ≤
      ((d : ℝ) * I.S d b + I.ω d b) - ((d : ℝ) * I.S d a + I.ω d a) := by
    have hC : C₂ ≤ C₂' := le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hC (mul_nonneg hdR.le hX0)]
  have hbase := sub_phaseLossNat_le_negativeRootCount_of_polar ξ (I.T d) d hd1 hT.ne' hJ
    (I.Z d) (fun q => (d : ℝ) * I.S d q + I.ω d q) a b ha hwin
    ((continuousOn_const.mul hSc).add hωc) hZne hpol hsmall
    (fun q hq => (hoscd q hq).trans_eq (by ring)) hΔ
  have hdX : (d : ℝ) * ((I.c₀ * I.T d) ^ (-(1 / 2 : ℝ)) +
        edgeOffset I.M d ^ (3 / 2 : ℝ)) ≤
      (Cup + I.M * Real.sqrt I.M) * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
    rw [mul_add, Real.rpow_neg hcT, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv, add_mul]
    linarith [hup d hDd hd1, edge_window_loss I.M_pos.le hd1]
  have hL := phaseLossNat_le_of_window_bound hC₂'0 hX0 hdR.le hdX
    (one_le_sqrt_nat_mul_log_nat h2)
  rw [← hC₀] at hL
  linarith

/-- Almost all Dedekind Jensen zeros are negative real: there are `C > 0` and
`d₀ ≥ 2` such that, for `d ≥ d₀`, `J_d ≠ 0` and `J_d` has at least
`d - C √(d log d)` distinct negative real roots. -/
theorem dedekindJensen_main (I : Inputs ξ) :
    ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      dedekindJensen ξ d ≠ 0 ∧
        (d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
          (dedekindNegativeRootCount ξ d : ℝ) := by
  obtain ⟨D₁, hD₁⟩ := eventually_atTop.mp I.jensen_ne_zero
  obtain ⟨C, hC, D₂, hD₂⟩ := eventual_negativeRootCount_bound ξ I
  refine ⟨C, hC, max 2 (max D₁ D₂), le_max_left _ _, fun d hd => ?_⟩
  have hd' : max D₁ D₂ ≤ d := le_of_max_le_right hd
  exact ⟨hD₁ d (le_of_max_le_left hd'), hD₂ d (le_of_max_le_right hd')⟩

end RiemannJensen.DedekindFinalAssembly
