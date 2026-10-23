module

public import Mathlib

/-!
# The whole-line theta kernel `Φ` and the Riemann `ξ`-function

We study the kernel
`Φ(t) = ∑_{n ≥ 1} (2π²n⁴e^{9t} − 3πn²e^{5t}) exp(−πn²e^{4t})` on the whole real line. It is
continuous, even, strictly positive and decays double-exponentially, so all its weighted moments
are finite. Its two-sided Laplace transform is Riemann's `ξ`-function:
`∫ e^{zt} Φ(t) dt = ξ(½ + z/2) / 4` for every complex `z`, and in particular
`∫ Φ(t) cos(xt) dt = Ξ(x/2) / 4`.

## Main definitions

* `ThetaKernel.Phi`: The kernel `Φ`.
* `ThetaKernel.omega`: The theta series `ω(x) = ∑_{n ≥ 1} exp(-π n² x)`.
* `ThetaKernel.xi`: Riemann's `ξ`-function, written via `completedRiemannZeta₀`.
* `ThetaKernel.Xi`: Riemann's `Ξ(x) = ξ(½ + i x)`.

## Main results

* `ThetaKernel.Phi_neg`: `Φ` is even.
* `ThetaKernel.Phi_pos`: `Φ` is strictly positive.
* `ThetaKernel.exists_abs_Phi_le`: `Φ` decays double-exponentially.
* `ThetaKernel.integrable_cexp_mul_Phi`: `t ↦ e^{zt} Φ(t)` is integrable for every complex `z`.
* `ThetaKernel.integral_cexp_mul_Phi_eq_completedRiemannZeta₀`:
  `∫ e^{zt} Φ(t) dt = ⅛ (s(s-1) Λ₀(s) + 1)` with `s = ½ + z/2`.
* `ThetaKernel.integral_cexp_mul_Phi_eq_xi`: `∫ e^{zt} Φ(t) dt = ξ(½ + z/2) / 4`.
* `ThetaKernel.integral_Phi_mul_cos`: `∫ Φ(t) cos(xt) dt = Ξ(x/2) / 4`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set

noncomputable section

namespace ThetaKernel

/-- A generic summand `(c₀ eᵗ + c₁ N² e^{5t} + c₂ N⁴ e^{9t}) exp(-π N² e^{4t})`, `N = n + 1`. -/
def term (c₀ c₁ c₂ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (c₀ * exp t + c₁ * ((n : ℝ) + 1) ^ 2 * exp (5 * t) + c₂ * ((n : ℝ) + 1) ^ 4 * exp (9 * t)) *
    exp (-π * ((n : ℝ) + 1) ^ 2 * exp (4 * t))

/-- The summand of `Φ` at index `n ≥ 1`. -/
def phiTerm (n : ℕ) (t : ℝ) : ℝ :=
  (2 * π ^ 2 * (n : ℝ) ^ 4 * exp (9 * t) - 3 * π * (n : ℝ) ^ 2 * exp (5 * t)) *
    exp (-π * (n : ℝ) ^ 2 * exp (4 * t))

/-- `Φ(t) = ∑_{n ≥ 1} (2π²n⁴e^{9t} − 3πn²e^{5t}) exp(−πn²e^{4t})`. -/
def Phi (t : ℝ) : ℝ := ∑' n : ℕ, phiTerm (n + 1) t

/-- The `(n + 1)`-st summand of `Φ` is the generic summand with coefficients `0, -3π, 2π²`. -/
lemma phiTerm_succ (n : ℕ) (t : ℝ) : phiTerm (n + 1) t = term 0 (-3 * π) (2 * π ^ 2) n t := by
  simp only [phiTerm, term]; push_cast; ring

/-- The bound `(|c₀| + |c₁| + |c₂|) e^{9(|a|+1)} N⁴ exp(-π e^{4(a-1)} N)`, `N = n + 1`, on the
generic summand for `t ∈ (a - 1, a + 1)`. -/
def bnd (c₀ c₁ c₂ a : ℝ) (n : ℕ) : ℝ :=
  (|c₀| + |c₁| + |c₂|) * exp (9 * (|a| + 1)) *
    (((n : ℝ) + 1) ^ 4 * exp (-(π * exp (4 * (a - 1))) * ((n : ℝ) + 1)))

/-- The bound sequence `bnd c₀ c₁ c₂ a` is summable. -/
lemma summable_bnd (c₀ c₁ c₂ a : ℝ) : Summable (bnd c₀ c₁ c₂ a) := by
  have hr : 0 < π * exp (4 * (a - 1)) := by positivity
  have h := (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul 4 hr)
  push_cast at h
  exact h.mul_left _

/-- For `t ∈ (a - 1, a + 1)`, the generic summand is bounded in absolute value by `bnd`. -/
lemma abs_term_le (c₀ c₁ c₂ a : ℝ) (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (a - 1) (a + 1)) :
    |term c₀ c₁ c₂ n t| ≤ bnd c₀ c₁ c₂ a n := by
  obtain ⟨h1, h2⟩ := ht
  set N : ℝ := (n : ℝ) + 1 with hNdef
  have hN : 1 ≤ N := by simp [hNdef]
  have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
  have hN4 : N ^ 2 ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
  have hT : t ≤ |a| + 1 := by linarith [le_abs_self a]
  have hT0 : 0 ≤ |a| + 1 := by positivity
  set X := exp (9 * (|a| + 1))
  have e1 : exp t ≤ X := exp_le_exp.mpr (by linarith)
  have e5 : exp (5 * t) ≤ X := exp_le_exp.mpr (by linarith)
  have e9 : exp (9 * t) ≤ X := exp_le_exp.mpr (by linarith)
  have hpoly : |c₀ * exp t + c₁ * N ^ 2 * exp (5 * t) + c₂ * N ^ 4 * exp (9 * t)| ≤
      (|c₀| + |c₁| + |c₂|) * X * N ^ 4 := by
    refine (abs_add_three _ _ _).trans ?_
    have hNpos : (0:ℝ) < N := by linarith
    simp only [abs_mul, Real.abs_exp, abs_pow, abs_of_pos hNpos]
    have a0 : |c₀| * exp t ≤ |c₀| * (X * N ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      nlinarith [exp_pos t, (exp_pos _ : 0 < X)]
    have a1 : |c₁| * N ^ 2 * exp (5 * t) ≤ |c₁| * (X * N ^ 4) := by
      rw [mul_assoc, mul_comm X]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hN4 e5 (exp_pos _).le (by positivity))
        (abs_nonneg _)
    have a2 : |c₂| * N ^ 4 * exp (9 * t) ≤ |c₂| * (X * N ^ 4) := by
      rw [mul_assoc, mul_comm X]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e9 (by positivity))
        (abs_nonneg _)
    nlinarith
  have hexp : exp (-π * N ^ 2 * exp (4 * t)) ≤ exp (-(π * exp (4 * (a - 1))) * N) := by
    apply exp_le_exp.mpr
    have h4 : exp (4 * (a - 1)) ≤ exp (4 * t) := exp_le_exp.mpr (by linarith)
    have hNN : N ≤ N ^ 2 := by nlinarith
    nlinarith [pi_pos, exp_pos (4 * (a - 1)), mul_le_mul hNN h4 (exp_pos _).le (by positivity)]
  unfold term bnd
  rw [← hNdef, abs_mul, abs_of_pos (exp_pos _)]
  calc _ ≤ ((|c₀| + |c₁| + |c₂|) * X * N ^ 4) * exp (-(π * exp (4 * (a - 1))) * N) :=
        mul_le_mul hpoly hexp (exp_pos _).le (by positivity)
    _ = _ := by ring

/-- For each `t`, the generic summands `term c₀ c₁ c₂ n t` are summable in `n`. -/
lemma summable_term (c₀ c₁ c₂ : ℝ) (t : ℝ) : Summable fun n => term c₀ c₁ c₂ n t :=
  Summable.of_norm_bounded (summable_bnd c₀ c₁ c₂ t) fun n =>
    abs_term_le c₀ c₁ c₂ t n ⟨by linarith, by linarith⟩

/-- Each generic summand is continuous in `t`. -/
lemma continuous_term (c₀ c₁ c₂ : ℝ) (n : ℕ) : Continuous (term c₀ c₁ c₂ n) := by
  unfold term; fun_prop

/-- The series `t ↦ ∑ₙ term c₀ c₁ c₂ n t` is continuous. -/
lemma continuous_tsum_term (c₀ c₁ c₂ : ℝ) : Continuous fun t => ∑' n, term c₀ c₁ c₂ n t := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  have h : ContinuousOn (fun t => ∑' n, term c₀ c₁ c₂ n t) (Ioo (a - 1) (a + 1)) :=
    continuousOn_tsum (fun n => (continuous_term c₀ c₁ c₂ n).continuousOn)
      (summable_bnd c₀ c₁ c₂ a) fun n t ht => abs_term_le c₀ c₁ c₂ a n ht
  exact h.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))

/-- The derivative of the summand with `c₂ = 0` is the summand with coefficients
`c₀, 5c₁ - 4πc₀, -4πc₁`. -/
lemma hasDerivAt_term (c₀ c₁ : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (term c₀ c₁ 0 n) (term c₀ (5 * c₁ - 4 * π * c₀) (-4 * π * c₁) n t) t := by
  set N : ℝ := (n : ℝ) + 1 with hNdef
  have hp : HasDerivAt (fun s => c₀ * exp s + c₁ * N ^ 2 * exp (5 * s) + 0 * N ^ 4 * exp (9 * s))
      (c₀ * exp t + c₁ * N ^ 2 * (exp (5 * t) * (5 * 1)) + 0 * N ^ 4 * (exp (9 * t) * (9 * 1))) t :=
    (((hasDerivAt_exp t).const_mul c₀).add
      (((hasDerivAt_id' t).const_mul 5).exp.const_mul _)).add
      (((hasDerivAt_id' t).const_mul 9).exp.const_mul _)
  have he : HasDerivAt (fun s => exp (-π * N ^ 2 * exp (4 * s)))
      (exp (-π * N ^ 2 * exp (4 * t)) * (-π * N ^ 2 * (exp (4 * t) * (4 * 1)))) t :=
    (((hasDerivAt_id' t).const_mul 4).exp.const_mul _).exp
  have h5 : exp (5 * t) = exp t * exp (4 * t) := by rw [← exp_add]; ring_nf
  have h9 : exp (9 * t) = exp t * exp (4 * t) * exp (4 * t) := by
    rw [← exp_add, ← exp_add]; ring_nf
  refine (hp.mul he).congr_deriv ?_
  simp only [term, ← hNdef]
  rw [h5, h9]; ring

/-- The derivative of `term 1 0 0 n` is `term 1 (-4π) 0 n`. -/
lemma hasDerivAt_term0 (n : ℕ) (t : ℝ) :
    HasDerivAt (term 1 0 0 n) (term 1 (-4 * π) 0 n t) t := by
  convert hasDerivAt_term 1 0 n t using 1; simp only [term]; ring

/-- The derivative of `term 1 (-4π) 0 n` is `term 1 (-24π) (16π²) n`. -/
lemma hasDerivAt_term1 (n : ℕ) (t : ℝ) :
    HasDerivAt (term 1 (-4 * π) 0 n) (term 1 (-24 * π) (16 * π ^ 2) n t) t := by
  convert hasDerivAt_term 1 (-4 * π) n t using 1; simp only [term]; ring

/-! ### Summability, local uniformity and continuity of `Φ` -/

/-- `Φ(t)` is the series of the generic summands with coefficients `0, -3π, 2π²`. -/
lemma Phi_eq_tsum_term (t : ℝ) : Phi t = ∑' n, term 0 (-3 * π) (2 * π ^ 2) n t := by
  unfold Phi; simp_rw [phiTerm_succ]

/-- The defining series of `Φ(t)` is summable. -/
theorem summable_phiTerm (t : ℝ) : Summable fun n : ℕ => phiTerm (n + 1) t := by
  simp_rw [phiTerm_succ]; exact summable_term _ _ _ t

/-- The defining series of `Φ` is dominated, locally uniformly in `t`, by a summable sequence. -/
theorem phiTerm_locally_uniform (a : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ t ∈ Ioo (a - 1) (a + 1), |phiTerm (n + 1) t| ≤ u n :=
  ⟨bnd 0 (-3 * π) (2 * π ^ 2) a, summable_bnd _ _ _ a, fun n t ht => by
    rw [phiTerm_succ]; exact abs_term_le _ _ _ a n ht⟩

/-- `Φ` is continuous. -/
theorem continuous_Phi : Continuous Phi := by
  rw [show Phi = fun t => ∑' n, term 0 (-3 * π) (2 * π ^ 2) n t from funext Phi_eq_tsum_term]
  exact continuous_tsum_term _ _ _

/-! ### The auxiliary function `B(t) = eᵗ ω(e^{4t})` and its derivatives -/

/-- `B(t) = ∑_{n ≥ 1} eᵗ exp(-π n² e^{4t})`. -/
def B (t : ℝ) : ℝ := ∑' n, term 1 0 0 n t
/-- `B'(t) = ∑_{n ≥ 1} (eᵗ − 4π n² e^{5t}) exp(-π n² e^{4t})`. -/
def B1 (t : ℝ) : ℝ := ∑' n, term 1 (-4 * π) 0 n t
/-- `B''(t) = ∑_{n ≥ 1} (eᵗ − 24π n² e^{5t} + 16π² n⁴ e^{9t}) exp(-π n² e^{4t})`. -/
def B2 (t : ℝ) : ℝ := ∑' n, term 1 (-24 * π) (16 * π ^ 2) n t

/-- The derivative of `B` is `B1`. -/
lemma hasDerivAt_B (t : ℝ) : HasDerivAt B (B1 t) t := by
  have mem : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  exact hasDerivAt_tsum_of_isPreconnected (summable_bnd 1 (-4 * π) 0 t) isOpen_Ioo
    isPreconnected_Ioo (fun n y _ => hasDerivAt_term0 n y)
    (fun n y hy => abs_term_le 1 (-4 * π) 0 t n hy) mem (summable_term 1 0 0 t) mem

/-- The derivative of `B1` is `B2`. -/
lemma hasDerivAt_B1 (t : ℝ) : HasDerivAt B1 (B2 t) t := by
  have mem : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  exact hasDerivAt_tsum_of_isPreconnected (summable_bnd 1 (-24 * π) (16 * π ^ 2) t) isOpen_Ioo
    isPreconnected_Ioo (fun n y _ => hasDerivAt_term1 n y)
    (fun n y hy => abs_term_le 1 (-24 * π) (16 * π ^ 2) t n hy) mem
    (summable_term 1 (-4 * π) 0 t) mem

/-- `Φ(t) = (B''(t) − B(t)) / 8`. -/
lemma Phi_eq (t : ℝ) : Phi t = (B2 t - B t) / 8 := by
  rw [Phi_eq_tsum_term, B2, B, ← Summable.tsum_sub (summable_term _ _ _ t) (summable_term _ _ _ t),
    ← tsum_div_const]
  congr 1; funext n; simp only [term]; ring

/-! ### The theta functional equation -/

/-- `ω(x) = ∑_{n ≥ 1} exp(-π n² x)`. -/
def omega (x : ℝ) : ℝ := ∑' n : ℕ, exp (-π * ((n : ℝ) + 1) ^ 2 * x)

/-- For `x > 0`, the even Hurwitz kernel at `0` is `1 + 2ω(x)`. -/
lemma evenKernel_zero_eq {x : ℝ} (hx : 0 < x) : HurwitzZeta.evenKernel 0 x = 1 + 2 * omega x := by
  have h := HurwitzZeta.hasSum_int_evenKernel 0 hx
  simp only [add_zero, QuotientAddGroup.mk_zero] at h
  have h3 : HasSum (fun n : ℕ => 2 * exp (-π * (n : ℝ) ^ 2 * x))
      (HurwitzZeta.evenKernel 0 x + 1) := by
    convert h.nat_add_neg using 1
    · funext n; push_cast; ring_nf
    · simp
  have h4 := ((hasSum_nat_add_iff' 1).mpr h3).tsum_eq
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, Nat.cast_add, Nat.cast_one,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul, exp_zero,
    mul_one] at h4
  rw [tsum_mul_left] at h4
  unfold omega; linarith

/-- `B(t) = eᵗ ω(e^{4t})`. -/
lemma B_eq (t : ℝ) : B t = exp t * omega (exp (4 * t)) := by
  unfold B omega; rw [← tsum_mul_left]; congr 1; funext n; simp [term]

/-- `B(-t) = B(t) + sinh t`. -/
lemma B_neg (t : ℝ) : B (-t) = B t + sinh t := by
  have hx : 0 < exp (4 * t) := exp_pos _
  have fe := HurwitzZeta.evenKernel_functional_equation 0 (exp (4 * t))
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero, evenKernel_zero_eq hx,
    evenKernel_zero_eq (by positivity)] at fe
  have hsq : exp (4 * t) ^ (1 / 2 : ℝ) = exp (2 * t) := by rw [← Real.exp_mul]; ring_nf
  have hinv : 1 / exp (4 * t) = exp (4 * (-t)) := by rw [one_div, ← Real.exp_neg]; ring_nf
  rw [hsq, hinv] at fe
  have key : 1 + 2 * omega (exp (4 * (-t))) = exp (2 * t) * (1 + 2 * omega (exp (4 * t))) := by
    rw [fe]; field_simp
  have hm : exp (-t) * exp (2 * t) = exp t := by rw [← exp_add]; ring_nf
  rw [B_eq, B_eq, sinh_eq]
  linear_combination (exp (-t) / 2) * key + (1 / 2 + omega (exp (4 * t))) * hm

/-- `B'(-t) = -(B'(t) + cosh t)`. -/
lemma B1_neg (t : ℝ) : B1 (-t) = -(B1 t + cosh t) := by
  have h1 : HasDerivAt (fun s => B (-s)) (B1 (-t) * (-1)) t :=
    (hasDerivAt_B (-t)).comp t (hasDerivAt_neg t)
  have h2 : HasDerivAt (fun s => B (-s)) (B1 t + cosh t) t := by
    rw [show (fun s => B (-s)) = fun s => B s + sinh s from funext B_neg]
    exact (hasDerivAt_B t).add (Real.hasDerivAt_sinh t)
  linarith [h1.unique h2]

/-- `B''(-t) = B''(t) + sinh t`. -/
lemma B2_neg (t : ℝ) : B2 (-t) = B2 t + sinh t := by
  have h1 : HasDerivAt (fun s => B1 (-s)) (B2 (-t) * (-1)) t :=
    (hasDerivAt_B1 (-t)).comp t (hasDerivAt_neg t)
  have h2 : HasDerivAt (fun s => B1 (-s)) (-(B2 t + sinh t)) t := by
    rw [show (fun s => B1 (-s)) = fun s => -(B1 s + cosh s) from funext B1_neg]
    exact ((hasDerivAt_B1 t).add (Real.hasDerivAt_cosh t)).neg
  linarith [h1.unique h2]

/-- `Φ` is even. -/
theorem Phi_neg (t : ℝ) : Phi (-t) = Phi t := by
  rw [Phi_eq, Phi_eq, B2_neg, B_neg]
  ring

/-- `Φ(|t|) = Φ(t)`. -/
theorem Phi_abs (t : ℝ) : Phi |t| = Phi t := by
  rcases abs_choice t with h | h <;> simp [h, Phi_neg]

/-! ### Positivity -/

/-- For `n ≥ 1` and `t ≥ 0`, the `n`-th summand of `Φ(t)` is positive. -/
lemma phiTerm_pos {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) : 0 < phiTerm n t := by
  unfold phiTerm
  apply mul_pos _ (exp_pos _)
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h4 : 1 ≤ exp (4 * t) := one_le_exp (by linarith)
  have h9 : exp (9 * t) = exp (5 * t) * exp (4 * t) := by rw [← exp_add]; ring_nf
  rw [h9, show 2 * π ^ 2 * (n : ℝ) ^ 4 * (exp (5 * t) * exp (4 * t)) -
      3 * π * (n : ℝ) ^ 2 * exp (5 * t)
      = π * (n : ℝ) ^ 2 * exp (5 * t) * (2 * π * ((n : ℝ) ^ 2 * exp (4 * t)) - 3) by ring]
  apply mul_pos (by positivity)
  have h1 : 1 ≤ (n : ℝ) ^ 2 := one_le_pow₀ hN
  have h2 : 1 ≤ (n : ℝ) ^ 2 * exp (4 * t) := one_le_mul_of_one_le_of_one_le h1 h4
  nlinarith [pi_gt_three]

/-- `Φ(t) > 0` for `t ≥ 0`. -/
theorem Phi_pos_of_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 < Phi t :=
  Summable.tsum_pos (summable_phiTerm t) (fun n => (phiTerm_pos (by omega) ht).le) 0
    (phiTerm_pos (by omega) ht)

/-- `Φ(t) > 0` for every real `t`. -/
theorem Phi_pos (t : ℝ) : 0 < Phi t :=
  Phi_abs t ▸ Phi_pos_of_nonneg (abs_nonneg t)

/-! ### Double-exponential decay -/

/-- The constant `∑_{n ≥ 1} n⁴ e^{-π n²}` in the decay bound for `Φ`. -/
def phiDecayConst : ℝ := ∑' n, term 0 0 1 n 0

/-- `phiDecayConst` is nonnegative. -/
lemma phiDecayConst_nonneg : 0 ≤ phiDecayConst := tsum_nonneg fun n => by unfold term; positivity

/-- For `t ≥ 0`, the `(n + 1)`-st summand of `Φ(t)` is at most
`2π² e^π e^{9t} exp(-π e^{4t}) (n + 1)⁴ e^{-π(n+1)²}`. -/
lemma phiTerm_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    phiTerm (n + 1) t ≤
      2 * π ^ 2 * exp π * (exp (9 * t) * exp (-π * exp (4 * t))) * term 0 0 1 n 0 := by
  unfold phiTerm term
  push_cast
  set N : ℝ := (n : ℝ) + 1 with hNdef
  set x := exp (4 * t) with hx
  have hN : 1 ≤ N := by simp [hNdef]
  have hN2 : 0 ≤ N ^ 2 - 1 := by nlinarith
  have hx1 : 0 ≤ x - 1 := by linarith [one_le_exp (by linarith : (0:ℝ) ≤ 4 * t)]
  have hE : exp (-π * N ^ 2 * x) ≤ exp π * exp (-π * x) * exp (-π * N ^ 2) := by
    rw [← exp_add, ← exp_add]
    exact exp_le_exp.mpr (by nlinarith [mul_nonneg (mul_nonneg pi_pos.le hN2) hx1])
  simp only [mul_zero, exp_zero, mul_one, zero_mul, zero_add]
  have h5 : 0 ≤ 3 * π * N ^ 2 * exp (5 * t) := by positivity
  calc (2 * π ^ 2 * N ^ 4 * exp (9 * t) - 3 * π * N ^ 2 * exp (5 * t)) * exp (-π * N ^ 2 * x)
      ≤ (2 * π ^ 2 * N ^ 4 * exp (9 * t)) * exp (-π * N ^ 2 * x) :=
        mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
    _ ≤ (2 * π ^ 2 * N ^ 4 * exp (9 * t)) * (exp π * exp (-π * x) * exp (-π * N ^ 2)) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = _ := by ring

/-- For `t ≥ 0`, `Φ(t) ≤ 2π² e^π e^{9t} exp(-π e^{4t}) phiDecayConst`. -/
lemma Phi_le {t : ℝ} (ht : 0 ≤ t) :
    Phi t ≤ 2 * π ^ 2 * exp π * (exp (9 * t) * exp (-π * exp (4 * t))) * phiDecayConst := by
  unfold Phi phiDecayConst
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun n => phiTerm_le n ht) (summable_phiTerm t)
    ((summable_term 0 0 1 0).mul_left _)

/-- For `t ≥ 0`, `e^{9t} exp(-π e^{4t}) ≤ exp(-(1/2) e^{4t})`. -/
lemma exp_nine_mul_le {t : ℝ} (ht : 0 ≤ t) :
    exp (9 * t) * exp (-π * exp (4 * t)) ≤ exp (-(1 / 2) * exp (4 * t)) := by
  rw [← exp_add]
  apply exp_le_exp.mpr
  have h1 := add_one_le_exp (4 * t)
  have h2 : 0 ≤ exp (4 * t) := (exp_pos _).le
  nlinarith [pi_gt_three, mul_nonneg (by linarith [pi_gt_three] : (0:ℝ) ≤ π - 3) h2]

/-- Double-exponential decay: `|Φ t| ≤ A exp(-(1/2) e^{4|t|})`. -/
theorem exists_abs_Phi_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, |Phi t| ≤ A * exp (-(1 / 2) * exp (4 * |t|)) := by
  refine ⟨2 * π ^ 2 * exp π * phiDecayConst, mul_nonneg (by positivity) phiDecayConst_nonneg,
    fun t => ?_⟩
  rw [abs_of_pos (Phi_pos t), ← Phi_abs]
  refine (Phi_le (abs_nonneg t)).trans ?_
  calc 2 * π ^ 2 * exp π * (exp (9 * |t|) * exp (-π * exp (4 * |t|))) * phiDecayConst
      = (2 * π ^ 2 * exp π * phiDecayConst) * (exp (9 * |t|) * exp (-π * exp (4 * |t|))) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_nine_mul_le (abs_nonneg t))
      (mul_nonneg (by positivity) phiDecayConst_nonneg)

/-! ### Integrability: all weighted moments are finite -/

/-- `t ↦ |t|ᵏ e^{a|t|} Φ(t)` is integrable for every `k : ℕ` and real `a`. -/
theorem integrable_Phi_weight (k : ℕ) (a : ℝ) :
    Integrable fun t : ℝ => |t| ^ k * exp (a * |t|) * Phi t := by
  obtain ⟨A, hA, hb⟩ := exists_abs_Phi_le
  have hint := (integrable_exp_neg_mul_sq (b := 1) one_pos).const_mul
    (A * (k.factorial : ℝ) * exp ((1 + a) ^ 2))
  refine hint.mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (((continuous_abs.pow k).mul (continuous_exp.comp
      (continuous_const.mul continuous_abs))).mul continuous_Phi).aestronglyMeasurable
  · set s := |t| with hs
    have hs0 : 0 ≤ s := abs_nonneg t
    have hpow : s ^ k ≤ k.factorial * exp s := by
      have := pow_div_factorial_le_exp s hs0 k
      rwa [div_le_iff₀ (by exact_mod_cast k.factorial_pos), mul_comm] at this
    have h8 : 8 * s ^ 2 ≤ exp (4 * s) := by
      have := pow_div_factorial_le_exp (4 * s) (by positivity) 2
      norm_num [Nat.factorial] at this; nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_abs, abs_of_pos (exp_pos _)]
    calc s ^ k * exp (a * s) * |Phi t|
        ≤ (k.factorial * exp s) * exp (a * s) * (A * exp (-(1 / 2) * exp (4 * s))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hpow (exp_pos _).le) (hb t) (abs_nonneg _)
            (by positivity)
      _ ≤ (k.factorial * exp s) * exp (a * s) * (A * exp (-4 * s ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hA
          exact exp_le_exp.mpr (by nlinarith)
      _ = A * k.factorial * exp (s + a * s + -4 * s ^ 2) := by
          rw [exp_add, exp_add]; ring
      _ ≤ A * k.factorial * exp ((1 + a) ^ 2 + -1 * t ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA (Nat.cast_nonneg _))
          apply exp_le_exp.mpr
          nlinarith [sq_abs t, sq_nonneg (6 * s - (1 + a)), sq_nonneg (1 + a)]
      _ = A * k.factorial * exp ((1 + a) ^ 2) * exp (-1 * t ^ 2) := by rw [exp_add]; ring

/-- Every moment `∫ tᵏ Φ(t) dt` exists. -/
theorem integrable_pow_mul_Phi (k : ℕ) : Integrable fun t : ℝ => t ^ k * Phi t := by
  refine (integrable_Phi_weight k 0).mono'
    ((continuous_pow k).mul continuous_Phi).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  simp [abs_of_pos (Phi_pos t)]

/-- `Re (z t) ≤ ‖z‖ |t|` for complex `z` and real `t`. -/
lemma re_mul_ofReal_le_norm_mul_abs (z : ℂ) (t : ℝ) : (z * (t : ℂ)).re ≤ ‖z‖ * |t| := by
  rw [show (z * (t : ℂ)).re = z.re * t by simp]
  calc z.re * t ≤ |z.re * t| := le_abs_self _
    _ = |z.re| * |t| := abs_mul _ _
    _ ≤ ‖z‖ * |t| := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (abs_nonneg _)

/-- `t ↦ e^{z t} Φ(t)` is integrable for every complex `z` (so `∫ Φ(t) cosh(z t) dt` exists). -/
theorem integrable_cexp_mul_Phi (z : ℂ) :
    Integrable fun t : ℝ => Complex.exp (z * t) * (Phi t : ℂ) := by
  refine (integrable_Phi_weight 0 ‖z‖).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (Complex.continuous_ofReal.comp continuous_Phi)).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Phi_pos t),
      pow_zero, one_mul]
    exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (re_mul_ofReal_le_norm_mul_abs z t))
      (Phi_pos t).le

/-! ### The Mellin transform of `Φ` and the `ξ`-function

The substitution `x = e^{4t}` turns `∫ e^{at} exp(-c e^{4t}) dt` into a Gamma integral; summing
over `n` for `Re z > 1` gives the Dirichlet series of `ζ`, and analytic continuation extends the
identity to all `z`. -/

/-- The image of `t ↦ e^{4t}` is `(0, ∞)`. -/
lemma image_exp_four : (fun t : ℝ => rexp (4 * t)) '' univ = Ioi 0 := by
  ext x; constructor
  · rintro ⟨t, -, rfl⟩; exact exp_pos _
  · intro hx; exact ⟨Real.log x / 4, trivial, by simp [mul_div_cancel₀, exp_log (mem_Ioi.mp hx)]⟩

/-- `(eᵘ)^b = e^{ub}` for real `u` and complex `b`. -/
lemma ofReal_exp_cpow (u : ℝ) (b : ℂ) : ((rexp u : ℝ) : ℂ) ^ b = Complex.exp (u * b) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (exp_pos u).ne'),
    ← Complex.ofReal_log (exp_pos u).le, Real.log_exp]

/-- For `c > 0`, `(1 / c)^b = exp(-b log c)`. -/
lemma one_div_cpow_eq {c : ℝ} (hc : 0 < c) (b : ℂ) :
    (1 / (c : ℂ)) ^ b = Complex.exp (-b * Real.log c) := by
  rw [Complex.cpow_def_of_ne_zero (by simp [hc.ne']),
    show (1 / (c : ℂ)) = ((c⁻¹ : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (inv_pos.mpr hc).le, Real.log_inv]
  push_cast; ring_nf

/-- `∫ e^{a t} exp(-c e^{4t}) dt = ¼ c^{-a/4} Γ(a/4)`. -/
theorem integral_cexp_mul_exp_neg_mul_exp_four {a : ℂ} (ha : 0 < a.re) {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, Complex.exp (a * t) * ((rexp (-c * rexp (4 * t)) : ℝ) : ℂ) =
      (1 / 4) * Complex.exp (-(a / 4) * Real.log c) * Complex.Gamma (a / 4) := by
  have hsub := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (f := fun t => rexp (4 * t)) (f' := fun t => rexp (4 * t) * 4)
    (fun x _ => (((hasDerivAt_id x).const_mul 4).exp.congr_deriv (by simp)).hasDerivWithinAt)
    (fun x _ y _ h => by simpa using h)
    (fun x : ℝ => (x : ℂ) ^ (a / 4 - 1) * Complex.exp (-(c * x)))
  rw [image_exp_four, Measure.restrict_univ] at hsub
  have hG := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := a / 4) (r := c)
    (by simp; linarith) hc
  rw [hsub, one_div_cpow_eq hc] at hG
  have hpt : ∀ t : ℝ, |rexp (4 * t) * 4| • (((rexp (4 * t) : ℝ) : ℂ) ^ (a / 4 - 1) *
      Complex.exp (-(c * ((rexp (4 * t) : ℝ) : ℂ)))) =
      4 * (Complex.exp (a * t) * ((rexp (-c * rexp (4 * t)) : ℝ) : ℂ)) := by
    intro t
    rw [abs_of_pos (by positivity), ofReal_exp_cpow, Complex.real_smul]
    push_cast
    rw [show (-(c:ℂ) * Complex.exp (4 * t)) = -(c * Complex.exp (4 * t)) by ring]
    have : Complex.exp (4 * t) * Complex.exp (4 * t * (a / 4 - 1)) = Complex.exp (a * t) := by
      rw [← Complex.exp_add]; ring_nf
    linear_combination (4 * Complex.exp (-(c * Complex.exp (4 * t)))) * this
  simp_rw [hpt, integral_const_mul] at hG
  linear_combination hG / 4

/-- For `Re a > 0` and `c > 0`, `t ↦ e^{at} exp(-c e^{4t})` is integrable. -/
theorem integrable_cexp_mul_exp_neg_mul_exp_four {a : ℂ} (ha : 0 < a.re) {c : ℝ} (hc : 0 < c) :
    Integrable fun t : ℝ => Complex.exp (a * t) * ((rexp (-c * rexp (4 * t)) : ℝ) : ℂ) := by
  have hσ : Integrable fun t : ℝ =>
      Complex.exp ((a.re : ℂ) * t) * ((rexp (-c * rexp (4 * t)) : ℝ) : ℂ) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_cexp_mul_exp_neg_mul_exp_four (by simpa using ha) hc]
    refine mul_ne_zero (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _))
      (Complex.Gamma_ne_zero_of_re_pos ?_)
    simp; linarith
  refine hσ.mono (by fun_prop) (Eventually.of_forall fun t => ?_)
  simp only [norm_mul, Complex.norm_exp]
  simp

/-- `e^{zt} e^{kt} = e^{(z + k)t}`. -/
lemma cexp_mul_ofReal_exp (z : ℂ) (k t : ℝ) :
    Complex.exp (z * t) * ((rexp (k * t) : ℝ) : ℂ) = Complex.exp ((z + k) * t) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]; push_cast; ring_nf

/-- For `Re z > -1` and `c > 0`, with `w = (z + 1)/4`,
`∫ e^{zt} (α e^{9t} + β e^{5t}) exp(-c e^{4t}) dt = ¼ c^{-w} Γ(w) w (α (w + 1)/c² + β/c)`. -/
theorem integral_two_term {z : ℂ} (hz : -1 < z.re) (α β : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, Complex.exp (z * t) *
        (((α * rexp (9 * t) + β * rexp (5 * t)) * rexp (-c * rexp (4 * t)) : ℝ) : ℂ) =
      (1 / 4) * Complex.exp (-((z + 1) / 4) * Real.log c) * Complex.Gamma ((z + 1) / 4) *
        ((z + 1) / 4) * (α * ((z + 1) / 4 + 1) / c ^ 2 + β / c) := by
  set w := (z + 1) / 4 with hw
  have h9 : 0 < (z + 9).re := by simp; linarith
  have h5 : 0 < (z + 5).re := by simp; linarith
  have hw0 : w ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hw] at this; linarith
  have hw1 : w + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hw] at this; linarith
  have hpt : ∀ t : ℝ, Complex.exp (z * t) *
      (((α * rexp (9 * t) + β * rexp (5 * t)) * rexp (-c * rexp (4 * t)) : ℝ) : ℂ) =
      (α : ℂ) * (Complex.exp ((z + 9) * t) * ((rexp (-c * rexp (4 * t)) : ℝ) : ℂ)) +
      (β : ℂ) * (Complex.exp ((z + 5) * t) * ((rexp (-c * rexp (4 * t)) : ℝ) : ℂ)) := by
    intro t
    have e9 := cexp_mul_ofReal_exp z 9 t
    have e5 := cexp_mul_ofReal_exp z 5 t
    push_cast at e9 e5 ⊢
    rw [← e9, ← e5]; ring
  simp_rw [hpt]
  rw [integral_add ((integrable_cexp_mul_exp_neg_mul_exp_four h9 hc).const_mul _)
      ((integrable_cexp_mul_exp_neg_mul_exp_four h5 hc).const_mul _),
    integral_const_mul, integral_const_mul, integral_cexp_mul_exp_neg_mul_exp_four h9 hc,
    integral_cexp_mul_exp_neg_mul_exp_four h5 hc]
  rw [show (z + 9) / 4 = w + 1 + 1 by rw [hw]; ring, show (z + 5) / 4 = w + 1 by rw [hw]; ring,
    Complex.Gamma_add_one _ hw1, Complex.Gamma_add_one _ hw0]
  have hL : Complex.exp (-(Real.log c : ℂ)) = (c : ℂ)⁻¹ := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hc]; push_cast; rfl
  have e2 : Complex.exp (-(w + 1 + 1) * Real.log c) =
      Complex.exp (-w * Real.log c) * (c : ℂ)⁻¹ * (c : ℂ)⁻¹ := by
    rw [← hL, ← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have e1 : Complex.exp (-(w + 1) * Real.log c) = Complex.exp (-w * Real.log c) * (c : ℂ)⁻¹ := by
    rw [← hL, ← Complex.exp_add]; ring_nf
  rw [e1, e2]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp

/-! ### Termwise integrals -/

/-- For `Re z > -1` and `c > 0`, `t ↦ e^{zt} (α e^{9t} + β e^{5t}) exp(-c e^{4t})` is
integrable. -/
theorem integrable_two_term {z : ℂ} (hz : -1 < z.re) (α β : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable fun t : ℝ => Complex.exp (z * t) *
        (((α * rexp (9 * t) + β * rexp (5 * t)) * rexp (-c * rexp (4 * t)) : ℝ) : ℂ) := by
  have h9 : 0 < (z + 9).re := by simp; linarith
  have h5 : 0 < (z + 5).re := by simp; linarith
  refine (((integrable_cexp_mul_exp_neg_mul_exp_four h9 hc).const_mul (α : ℂ)).add
    ((integrable_cexp_mul_exp_neg_mul_exp_four h5 hc).const_mul (β : ℂ))).congr
      (Eventually.of_forall fun t => ?_)
  have e9 := cexp_mul_ofReal_exp z 9 t
  have e5 := cexp_mul_ofReal_exp z 5 t
  push_cast at e9 e5 ⊢
  simp only [Pi.add_apply]
  rw [← e9, ← e5]; ring

/-- The `(n + 1)`-st summand of `Φ` in two-term form with `c = π(n + 1)²`. -/
lemma phiTerm_eq (n : ℕ) (t : ℝ) : phiTerm (n + 1) t =
    (2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * rexp (9 * t) + -3 * π * ((n : ℝ) + 1) ^ 2 * rexp (5 * t)) *
      rexp (-(π * ((n : ℝ) + 1) ^ 2) * rexp (4 * t)) := by
  unfold phiTerm; push_cast; ring_nf

/-- The two-term integral with `c = π (n+1)²`, written as a Dirichlet-series term. -/
theorem integral_term {z : ℂ} (hz : -1 < z.re) (α β : ℝ) (n : ℕ) :
    ∫ t : ℝ, Complex.exp (z * t) *
        (((α * ((n : ℝ) + 1) ^ 4 * rexp (9 * t) + β * ((n : ℝ) + 1) ^ 2 * rexp (5 * t)) *
          rexp (-(π * ((n : ℝ) + 1) ^ 2) * rexp (4 * t)) : ℝ) : ℂ) =
      (1 / 4) * Complex.Gamma ((z + 1) / 4) * ((z + 1) / 4) *
        (α * ((z + 1) / 4 + 1) / π ^ 2 + β / π) *
        ((π : ℂ) ^ (-((z + 1) / 2) / 2) * (1 / ((n : ℂ) + 1) ^ ((z + 1) / 2))) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc : 0 < π * ((n : ℝ) + 1) ^ 2 := by positivity
  rw [integral_two_term hz (α * ((n : ℝ) + 1) ^ 4) (β * ((n : ℝ) + 1) ^ 2) hc]
  have hπ : (π : ℂ) ^ (-((z + 1) / 2) / 2) =
      Complex.exp (Real.log π * (-((z + 1) / 2) / 2)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr pi_ne_zero),
      ← Complex.ofReal_log pi_pos.le]
  have hn : ((n : ℂ) + 1) ^ ((z + 1) / 2) =
      Complex.exp (Real.log ((n : ℝ) + 1) * ((z + 1) / 2)) := by
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_add_one_ne_zero n),
      show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hN.le]
  have hL : Real.log (π * ((n : ℝ) + 1) ^ 2) = Real.log π + 2 * Real.log ((n : ℝ) + 1) := by
    rw [Real.log_mul pi_ne_zero (by positivity), Real.log_pow]; push_cast; ring
  have hE : Complex.exp (-((z + 1) / 4) * (Real.log (π * ((n : ℝ) + 1) ^ 2) : ℝ)) =
      Complex.exp (Real.log π * (-((z + 1) / 2) / 2)) *
        (1 / Complex.exp (Real.log ((n : ℝ) + 1) * ((z + 1) / 2))) := by
    rw [one_div, ← Complex.exp_neg, ← Complex.exp_add, hL]; push_cast; ring_nf
  rw [hE, hπ, hn]
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  have hn0 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  push_cast
  field_simp

/-- Termwise Mellin–Dirichlet identity for the `n`-th summand of `Φ`. -/
theorem integral_phiTerm {z : ℂ} (hz : -1 < z.re) (n : ℕ) :
    ∫ t : ℝ, Complex.exp (z * t) * (phiTerm (n + 1) t : ℂ) =
      (1 / 8) * ((1 / 2 + z / 2) * (z / 2 - 1 / 2)) *
        ((π : ℂ) ^ (-(1 / 2 + z / 2) / 2) * Complex.Gamma ((1 / 2 + z / 2) / 2) *
          (1 / ((n + 1 : ℕ) : ℂ) ^ (1 / 2 + z / 2))) := by
  simp_rw [phiTerm_eq]
  rw [integral_term hz (2 * π ^ 2) (-3 * π) n, show (1 / 2 + z / 2) = (z + 1) / 2 by ring,
    show (z + 1) / 2 / 2 = (z + 1) / 4 by ring]
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  push_cast
  field_simp
  ring

/-! ### Interchange of sum and integral for `Re z > 1` -/

/-- For `Re z > -1`, `t ↦ e^{zt}` times the `(n + 1)`-st summand of `Φ(t)` is integrable. -/
theorem integrable_phiTerm {z : ℂ} (hz : -1 < z.re) (n : ℕ) :
    Integrable fun t : ℝ => Complex.exp (z * t) * (phiTerm (n + 1) t : ℂ) := by
  have hc : 0 < π * ((n : ℝ) + 1) ^ 2 := by positivity
  refine (integrable_two_term hz (2 * π ^ 2 * ((n : ℝ) + 1) ^ 4)
    (-3 * π * ((n : ℝ) + 1) ^ 2) hc).congr (Eventually.of_forall fun t => ?_)
  simp only [phiTerm_eq]

/-- For `Re z > 1`, the integrals of `‖e^{zt} φₙ₊₁(t)‖` over the summands `φₙ₊₁` of `Φ` are
summable. -/
theorem summable_integral_norm {z : ℂ} (hz : 1 < z.re) :
    Summable fun n : ℕ => ∫ t : ℝ, ‖Complex.exp (z * t) * (phiTerm (n + 1) t : ℂ)‖ := by
  set σ := z.re with hσ
  let X : ℕ → ℝ → ℝ := fun n t =>
    (2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * rexp (9 * t) + 3 * π * ((n : ℝ) + 1) ^ 2 * rexp (5 * t)) *
      rexp (-(π * ((n : ℝ) + 1) ^ 2) * rexp (4 * t))
  let G : ℕ → ℝ → ℝ := fun n t => rexp (σ * t) * X n t
  have hσ' : -1 < (σ : ℂ).re := by simp; linarith
  have hGc : ∀ n (t : ℝ), Complex.exp ((σ : ℂ) * t) * (X n t : ℂ) = ((G n t : ℝ) : ℂ) := by
    intro n t; simp only [G]; push_cast; rfl
  have hGint : ∀ n, Integrable (G n) := by
    intro n
    have hc : 0 < π * ((n : ℝ) + 1) ^ 2 := by positivity
    have h := (integrable_two_term hσ' (2 * π ^ 2 * ((n : ℝ) + 1) ^ 4)
      (3 * π * ((n : ℝ) + 1) ^ 2) hc).re
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only
    rw [show ((2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * rexp (9 * t) +
      3 * π * ((n : ℝ) + 1) ^ 2 * rexp (5 * t)) * rexp (-(π * ((n : ℝ) + 1) ^ 2) * rexp (4 * t)))
      = X n t from rfl, hGc]
    simp
  have hGval : ∀ n, ((∫ t, G n t : ℝ) : ℂ) =
      (1 / 4) * Complex.Gamma (((σ : ℂ) + 1) / 4) * (((σ : ℂ) + 1) / 4) *
        (2 * π ^ 2 * (((σ : ℂ) + 1) / 4 + 1) / π ^ 2 + 3 * π / π) *
        ((π : ℂ) ^ (-(((σ : ℂ) + 1) / 2) / 2) * (1 / ((n : ℂ) + 1) ^ (((σ : ℂ) + 1) / 2))) := by
    intro n
    rw [← integral_complex_ofReal]
    simp_rw [← hGc]
    rw [integral_term hσ' (2 * π ^ 2) (3 * π) n]
    push_cast; ring
  have hs : 1 < (((σ : ℂ) + 1) / 2).re := by simp; linarith
  have hD : Summable fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (((σ : ℂ) + 1) / 2) := by
    simpa using (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
  have hGsum : Summable fun n => ∫ t, G n t := by
    rw [← Complex.summable_ofReal]
    simp_rw [hGval]
    exact (hD.mul_left _).mul_left _
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
    (fun n => integral_mono (integrable_phiTerm (by linarith) n).norm (hGint n) fun t => ?_) hGsum
  simp only [G, X]
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, phiTerm_eq]
  have hre : (z * (t : ℂ)).re = σ * t := by simp [hσ]
  rw [hre]
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  rw [abs_mul, abs_of_pos (exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
  have ha : 0 ≤ 2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * rexp (9 * t) := by positivity
  have hb : 0 ≤ 3 * π * ((n : ℝ) + 1) ^ 2 * rexp (5 * t) := by positivity
  rw [abs_le]; constructor <;> nlinarith

/-- For `Re z > 1`, `∫ e^{zt} Φ(t) dt` is the sum of the termwise integrals. -/
theorem integral_eq_tsum {z : ℂ} (hz : 1 < z.re) :
    ∫ t : ℝ, Complex.exp (z * t) * (Phi t : ℂ) =
      ∑' n : ℕ, ∫ t : ℝ, Complex.exp (z * t) * (phiTerm (n + 1) t : ℂ) := by
  rw [integral_tsum_of_summable_integral_norm (fun n => integrable_phiTerm (by linarith) n)
    (summable_integral_norm hz)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Phi, Complex.ofReal_tsum, tsum_mul_left]

/-- For `Re z > 1`, `∫ e^{zt} Φ(t) dt = ⅛ (s(s-1) Λ₀(s) + 1)` with `s = ½ + z/2`. -/
theorem integral_cexp_mul_Phi_eq_completedRiemannZeta₀_of_one_lt_re {z : ℂ} (hz : 1 < z.re) :
    ∫ t : ℝ, Complex.exp (z * t) * (Phi t : ℂ) =
      (1 / 8) *
        ((1 / 2 + z / 2) * (z / 2 - 1 / 2) * completedRiemannZeta₀ (1 / 2 + z / 2) + 1) := by
  rw [integral_eq_tsum hz]
  simp_rw [integral_phiTerm (show -1 < z.re by linarith)]
  rw [tsum_mul_left, tsum_mul_left]
  set s := 1 / 2 + z / 2 with hsdef
  have hs : 1 < s.re := by simp [hsdef]; linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : 1 - s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hsum := Complex.summable_one_div_nat_cpow.mpr hs
  have h0 : ∑' n : ℕ, 1 / (n : ℂ) ^ s = ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ s := by
    rw [hsum.tsum_eq_zero_add]
    simp [Complex.zero_cpow hs0]
  rw [← h0, ← completedZeta_eq_tsum_of_one_lt_re hs, completedRiemannZeta_eq,
    show z / 2 - 1 / 2 = s - 1 by rw [hsdef]; ring]
  have hs1' : s - 1 ≠ 0 := by intro h; apply hs1; linear_combination -h
  field_simp
  ring

/-! ### Analytic continuation -/

/-- The derivative of `z ↦ ∫ e^{zt} Φ(t) dt` at `z₀` is `∫ t e^{z₀t} Φ(t) dt`. -/
theorem hasDerivAt_integral_cexp_mul_Phi (z₀ : ℂ) :
    HasDerivAt (fun z : ℂ => ∫ t : ℝ, Complex.exp (z * t) * (Phi t : ℂ))
      (∫ t : ℝ, (t : ℂ) * Complex.exp (z₀ * t) * (Phi t : ℂ)) z₀ := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ one_pos)
    (F' := fun z (t : ℝ) => (t : ℂ) * Complex.exp (z * t) * (Phi t : ℂ))
    (Eventually.of_forall fun z => (integrable_cexp_mul_Phi z).aestronglyMeasurable)
    (integrable_cexp_mul_Phi z₀) ?_ ?_ (integrable_Phi_weight 1 (‖z₀‖ + 1)) ?_).2
  · exact ((Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).mul
      (Complex.continuous_ofReal.comp continuous_Phi)).aestronglyMeasurable
  · refine Eventually.of_forall fun t z hz => ?_
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Phi_pos t), pow_one]
    apply mul_le_mul_of_nonneg_right _ (Phi_pos t).le
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith [norm_le_norm_add_norm_sub' z z₀]
    exact exp_le_exp.mpr ((re_mul_ofReal_le_norm_mul_abs z t).trans
      (mul_le_mul_of_nonneg_right hz' (abs_nonneg _)))
  · refine Eventually.of_forall fun t z _ => ?_
    have h := (((hasDerivAt_id z).mul_const (t : ℂ)).cexp).mul_const (Phi t : ℂ)
    exact h.congr_deriv (by simp only [id]; ring)

/-- `z ↦ ∫ e^{zt} Φ(t) dt` is entire. -/
theorem differentiable_integral_cexp_mul_Phi :
    Differentiable ℂ fun z : ℂ => ∫ t : ℝ, Complex.exp (z * t) * (Phi t : ℂ) :=
  fun z => (hasDerivAt_integral_cexp_mul_Phi z).differentiableAt

/-- `∫ Φ(t) e^{zt} dt = ⅛ ((s(s-1)) Λ₀(s) + 1)` with `s = ½ + z/2`, for every complex `z`. -/
theorem integral_cexp_mul_Phi_eq_completedRiemannZeta₀ (z : ℂ) :
    ∫ t : ℝ, Complex.exp (z * t) * (Phi t : ℂ) =
      (1 / 8) *
        ((1 / 2 + z / 2) * (z / 2 - 1 / 2) * completedRiemannZeta₀ (1 / 2 + z / 2) + 1) := by
  have hR : Differentiable ℂ fun z : ℂ =>
      (1 / 8) *
        ((1 / 2 + z / 2) * (z / 2 - 1 / 2) * completedRiemannZeta₀ (1 / 2 + z / 2) + 1) := by
    have := differentiable_completedZeta₀
    fun_prop
  have hf := Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_integral_cexp_mul_Phi
  have hg := Complex.analyticOnNhd_univ_iff_differentiable.mpr hR
  have hev : (fun z : ℂ => ∫ t : ℝ, Complex.exp (z * t) * (Phi t : ℂ)) =ᶠ[𝓝 (2 : ℂ)]
      fun z : ℂ => (1 / 8) *
        ((1 / 2 + z / 2) * (z / 2 - 1 / 2) * completedRiemannZeta₀ (1 / 2 + z / 2) + 1) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact integral_cexp_mul_Phi_eq_completedRiemannZeta₀_of_one_lt_re hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ _) hev
    (mem_univ z)

/-! ### The Riemann ξ-function and equivalent forms -/

/-- Riemann's `ξ(s) = ½ s (s-1) π^{-s/2} Γ(s/2) ζ(s)`, written via the entire `Λ₀`. -/
def xi (s : ℂ) : ℂ := (1 / 2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

/-- Riemann's `Ξ(x) = ξ(½ + i x)`. -/
def Xi (x : ℂ) : ℂ := xi (1 / 2 + x * Complex.I)

/-- For `s ≠ 0, 1`, `ξ(s) = ½ s (s - 1) Λ(s)`. -/
theorem xi_eq_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi s = (1 / 2) * s * (s - 1) * completedRiemannZeta s := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs1'' : 1 - s ≠ 0 := fun h => hs1' (by linear_combination -h)
  rw [xi, completedRiemannZeta_eq]
  field_simp
  ring

/-- `∫ e^{zt} Φ(t) dt = ξ(½ + z/2) / 4`. -/
theorem integral_cexp_mul_Phi_eq_xi (z : ℂ) :
    ∫ t : ℝ, Complex.exp (z * t) * (Phi t : ℂ) = xi (1 / 2 + z / 2) / 4 := by
  rw [integral_cexp_mul_Phi_eq_completedRiemannZeta₀, xi]; ring

/-- Centered form: `∫ Φ(t) e^{2zt} dt = ξ(½ + z) / 4`. -/
theorem integral_cexp_two_mul_Phi_eq_xi (z : ℂ) :
    ∫ t : ℝ, Complex.exp (2 * z * t) * (Phi t : ℂ) = xi (1 / 2 + z) / 4 := by
  rw [integral_cexp_mul_Phi_eq_xi]; congr 2; ring

/-- `∫ e^{-zt} Φ(t) dt = ∫ e^{zt} Φ(t) dt`. -/
theorem integral_cexp_neg_mul_Phi (z : ℂ) :
    ∫ t : ℝ, Complex.exp (-z * t) * (Phi t : ℂ) = ∫ t : ℝ, Complex.exp (z * t) * (Phi t : ℂ) := by
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Complex.ofReal_neg, Phi_neg]; ring_nf

/-- `∫ Φ(t) cosh(zt) dt = ξ(½ + z/2) / 4`. -/
theorem integral_ccosh_mul_Phi (z : ℂ) :
    ∫ t : ℝ, Complex.cosh (z * t) * (Phi t : ℂ) = xi (1 / 2 + z / 2) / 4 := by
  have h : ∀ t : ℝ, Complex.cosh (z * t) * (Phi t : ℂ) = (1 / 2 : ℂ) *
      (Complex.exp (z * t) * (Phi t : ℂ) + Complex.exp (-z * t) * (Phi t : ℂ)) := by
    intro t; rw [Complex.cosh, neg_mul]; ring
  simp_rw [h]
  rw [integral_const_mul, integral_add (integrable_cexp_mul_Phi z) (integrable_cexp_mul_Phi (-z)),
    integral_cexp_neg_mul_Phi, integral_cexp_mul_Phi_eq_xi]
  ring

/-- Riemann's real form: `∫_ℝ Φ(t) cos(xt) dt = Ξ(x/2) / 4 = ξ(½ + ix/2) / 4`. -/
theorem integral_Phi_mul_cos (x : ℝ) :
    ((∫ t : ℝ, Phi t * Real.cos (x * t) : ℝ) : ℂ) = Xi (x / 2) / 4 := by
  rw [← integral_complex_ofReal]
  have h : ∀ t : ℝ, ((Phi t * Real.cos (x * t) : ℝ) : ℂ) =
      Complex.cosh ((x * Complex.I) * t) * (Phi t : ℂ) := by
    intro t
    rw [show (x : ℂ) * Complex.I * t = ((x * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.cosh_mul_I]
    push_cast; ring
  simp_rw [h]
  rw [integral_ccosh_mul_Phi, Xi]
  congr 2
  ring

/-- `e^{t/2} (θ₀(e^{2t}) − 1) / 2 = B(t/2)`. -/
theorem seed_eq (t : ℝ) :
    exp (t / 2) * (HurwitzZeta.evenKernel 0 (exp (2 * t)) - 1) / 2 = B (t / 2) := by
  rw [evenKernel_zero_eq (exp_pos _), B_eq]
  ring_nf

/-- `∫ e^{zt} · 2Φ(t/2) dt = ξ(½ + z)`. -/
theorem integral_cexp_mul_two_Phi_half (z : ℂ) :
    ∫ t : ℝ, Complex.exp (z * t) * ((2 * Phi (t / 2) : ℝ) : ℂ) = xi (1 / 2 + z) := by
  have h := Measure.integral_comp_mul_left
    (fun u : ℝ => Complex.exp (2 * z * u) * ((Phi u : ℝ) : ℂ)) (1 / 2 : ℝ)
  have h2 : ∀ t : ℝ, Complex.exp (z * t) * ((2 * Phi (t / 2) : ℝ) : ℂ) =
      2 * (Complex.exp (2 * z * ((1 / 2 * t : ℝ) : ℂ)) * ((Phi (1 / 2 * t) : ℝ) : ℂ)) := by
    intro t
    rw [show t / 2 = 1 / 2 * t by ring]
    push_cast
    ring_nf
  simp_rw [h2]
  rw [integral_const_mul, h, integral_cexp_two_mul_Phi_eq_xi]
  norm_num
  ring

/-- `∫_{(0, ∞)} cosh(zt) Φ(t) dt = ξ(½ + z/2) / 8`. -/
theorem integral_Ioi_ccosh_mul_Phi (z : ℂ) :
    ∫ t in Ioi (0 : ℝ), Complex.cosh (z * t) * (Phi t : ℂ) = xi (1 / 2 + z / 2) / 8 := by
  set f : ℝ → ℂ := fun t => Complex.cosh (z * t) * (Phi t : ℂ) with hf
  have hint : Integrable f := by
    have h : f = fun t : ℝ => (1 / 2 : ℂ) *
        (Complex.exp (z * t) * (Phi t : ℂ) + Complex.exp (-z * t) * (Phi t : ℂ)) := by
      funext t
      simp only [hf, Complex.cosh, neg_mul]
      ring
    rw [h]
    exact ((integrable_cexp_mul_Phi z).add (integrable_cexp_mul_Phi (-z))).const_mul _
  have heven : ∀ t, f (-t) = f t := by
    intro t
    simp only [hf, Complex.ofReal_neg, Phi_neg, mul_neg, Complex.cosh_neg]
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hint.integrableOn
    hint.integrableOn
  have hneg : ∫ t in Iic (0 : ℝ), f t = ∫ t in Ioi (0 : ℝ), f t := by
    simpa only [heven, neg_zero] using integral_comp_neg_Iic (0 : ℝ) f
  have hfull : ∫ t, f t = xi (1 / 2 + z / 2) / 4 := integral_ccosh_mul_Phi z
  rw [hneg] at hsplit
  rw [← hsplit] at hfull
  linear_combination hfull / 2

end ThetaKernel
