module

public import RiemannJensen.Dedekind.EulerLogComparison
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The logarithmic derivative of the Dedekind zeta function

For a number field `K`, the logarithmic derivative of the Dedekind zeta function on `Re s > 1` is
the sum over prime ideals of the derivatives of the Euler-factor logarithms. On `Re s ≥ 4` this
sum is bounded by a constant times `2 ^ (-Re s)`, giving exponential decay.

## Main definitions

* `dedekindPrimeLogDerivative`: The derivative of the Euler logarithm of one prime ideal.
* `dedekindLogDerivMajorant`: The sum of the norms of these derivatives at `s = 4`.
* `dedekindLogDerivDecayConstant`: A positive constant controlling the exponential decay.
* `dedekindLogDerivWeightedConstant`: The constant in the weighted estimate.

## Main results

* `analyticDedekindZeta_logDeriv_eq_derivEulerLog`: On `Re s > 1`, the logarithmic derivative of
  `analyticDedekindZeta K` is the derivative of the Euler logarithm.
* `analyticDedekindZeta_logDeriv_explicit`: The bound by `2 ^ (4 - Re s)` times the majorant.
* `analyticDedekindZeta_logDeriv_decay`: Exponential decay of the logarithmic derivative.
* `analyticDedekindZeta_logDeriv_weighted`: A linearly weighted logarithmic derivative is
  uniformly bounded.
-/

@[expose] public section

namespace RiemannJensen

set_option autoImplicit false

noncomputable section

open NumberField Filter Complex
open scoped Topology Classical

/-- The derivative of one prime-ideal Euler logarithm. -/
def dedekindPrimeLogDerivative
    (K : Type) [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (s : ℂ) : ℂ :=
  -Complex.log ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) *
      ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s) /
    (1 - ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s))

/-- Differentiation of a single prime-ideal Euler logarithm in its
convergence half-plane. -/
theorem hasDerivAt_dedekindPrimeLogFactor
    (K : Type) [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (dedekindPrimeLogFactor K p)
      (dedekindPrimeLogDerivative K p s) s := by
  let N : ℕ := Ideal.absNorm p.asIdeal
  change HasDerivAt (-fun z : ℂ => Complex.log (1 - (N : ℂ) ^ (-z)))
    (-Complex.log (N : ℂ) * (N : ℂ) ^ (-s) /
      (1 - (N : ℂ) ^ (-s))) s
  have hN2 : 2 ≤ N := two_le_absNorm_heightOne K p
  have hzlt : ‖(N : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN2) (by linarith)
  have hslit : 1 - (N : ℂ) ^ (-s) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [sub_re, one_re]
    linarith [Complex.re_le_norm ((N : ℂ) ^ (-s))]
  have hpow : HasDerivAt (fun z : ℂ => (N : ℂ) ^ (-z))
      ((N : ℂ) ^ (-s) * Complex.log (N : ℂ) * (-1)) s :=
    (hasDerivAt_id s).neg.const_cpow (Or.inl (by exact_mod_cast (by omega : N ≠ 0)))
  rw [show -Complex.log (N : ℂ) * (N : ℂ) ^ (-s) / (1 - (N : ℂ) ^ (-s)) =
      -((0 - (N : ℂ) ^ (-s) * Complex.log (N : ℂ) * (-1)) / (1 - (N : ℂ) ^ (-s))) by ring]
  simpa only [Pi.sub_apply, Pi.one_apply] using (((hasDerivAt_const s 1).sub hpow).clog hslit).neg

/-- The derivatives of the prime logarithms sum to the derivative of their
sum throughout `Re s > 1`. -/
theorem hasSum_dedekindPrimeLogDerivative
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K) => dedekindPrimeLogDerivative K p s)
      (deriv (fun z : ℂ => ∑' p : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K), dedekindPrimeLogFactor K p z) s) := by
  have ha : 1 < (1 + s.re) / 2 := by linarith
  have hsa : (1 + s.re) / 2 < s.re := by linarith
  exact (Complex.hasSum_deriv_of_summable_norm (summable_dedekindEulerLogMajorant K ha)
      (F := fun p z => dedekindPrimeLogFactor K p z)
      (U := {z : ℂ | (1 + s.re) / 2 < z.re})
      (fun p z hz =>
        (hasDerivAt_dedekindPrimeLogFactor K p
          (ha.trans hz)).differentiableAt.differentiableWithinAt)
      (isOpen_lt continuous_const continuous_re)
      (fun p z hz => norm_dedekindPrimeLogFactor_le K ha p hz.le)
      hsa).congr_fun fun p => (hasDerivAt_dedekindPrimeLogFactor K p hs).deriv.symm

/-- On `Re s > 1`, the Euler logarithm agrees near `s` with the sum of the prime logarithms. -/
theorem dedekindEulerLog_eventuallyEq_tsum
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindEulerLog K =ᶠ[𝓝 s] (fun z => ∑' p : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K), dedekindPrimeLogFactor K p z) := by
  filter_upwards [isOpen_lt continuous_const continuous_re |>.mem_nhds hs] with z hz
  exact dedekindEulerLog_eq_locallyUniformSum K hz

/-- On `Re s > 1`, the logarithmic derivative of the continued Dedekind
zeta function is the derivative of its Euler logarithm. -/
theorem analyticDedekindZeta_logDeriv_eq_derivEulerLog
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    deriv (analyticDedekindZeta K) s / analyticDedekindZeta K s =
      deriv (dedekindEulerLog K) s := by
  have ha : 1 < (1 + s.re) / 2 := by linarith
  have hsa : (1 + s.re) / 2 < s.re := by linarith
  have hLdiff : DifferentiableAt ℂ (dedekindEulerLog K) s :=
    ((Complex.differentiableOn_tsum_of_summable_norm (summable_dedekindEulerLogMajorant K ha)
      (fun p z hz =>
        (hasDerivAt_dedekindPrimeLogFactor K p
          (ha.trans hz)).differentiableAt.differentiableWithinAt)
      (isOpen_lt continuous_const continuous_re)
      (fun p z hz => norm_dedekindPrimeLogFactor_le K ha p (le_of_lt hz)) s hsa).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hsa)).congr_of_eventuallyEq
      (dedekindEulerLog_eventuallyEq_tsum K hs)
  have hexp : (fun z => Complex.exp (dedekindEulerLog K z)) =ᶠ[𝓝 s]
      analyticDedekindZeta K := by
    filter_upwards [isOpen_lt continuous_const continuous_re |>.mem_nhds hs] with z hz
    exact dedekindEulerLog_exp K hz
  rw [← hexp.deriv_eq, hLdiff.hasDerivAt.cexp.deriv, ← dedekindEulerLog_exp K hs]
  field_simp [Complex.exp_ne_zero]

/-- Absolute sum at `σ = 4` of the differentiated Euler-log series. -/
noncomputable def dedekindLogDerivMajorant
    (K : Type) [Field K] [NumberField K] : ℝ :=
  ∑' p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
    ‖dedekindPrimeLogDerivative K p 4‖

/-- The differentiated Euler-log majorant is summable. -/
theorem summable_dedekindLogDerivMajorant
    (K : Type) [Field K] [NumberField K] :
    Summable (fun p : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K) => ‖dedekindPrimeLogDerivative K p 4‖) :=
  (hasSum_dedekindPrimeLogDerivative K (by norm_num)).summable.norm

/-- Real majorant for one differentiated prime Euler factor. -/
theorem norm_dedekindPrimeLogDerivative_le_real
    (K : Type) [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {s : ℂ} (hs : 1 < s.re) :
    ‖dedekindPrimeLogDerivative K p s‖ ≤
      Real.log (Ideal.absNorm p.asIdeal : ℝ) *
        (Ideal.absNorm p.asIdeal : ℝ) ^ (-s.re) /
      (1 - (Ideal.absNorm p.asIdeal : ℝ) ^ (-s.re)) := by
  let N : ℕ := Ideal.absNorm p.asIdeal
  have hN2 : 2 ≤ N := two_le_absNorm_heightOne K p
  have hpowlt : (N : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN2) (by linarith)
  have hnormpow : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hden : 1 - (N : ℝ) ^ (-s.re) ≤ ‖1 - (N : ℂ) ^ (-s)‖ := by
    simpa only [norm_one, hnormpow] using
      (norm_sub_norm_le (1 : ℂ) ((N : ℂ) ^ (-s)))
  rw [dedekindPrimeLogDerivative, norm_div, norm_mul, norm_neg, ← Complex.natCast_log,
    Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg _), hnormpow]
  exact div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hpowlt) hden

/-- At a real argument, the preceding real majorant is exact. -/
theorem norm_dedekindPrimeLogDerivative_ofReal
    (K : Type) [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {σ : ℝ} (hσ : 1 < σ) :
    ‖dedekindPrimeLogDerivative K p (σ : ℂ)‖ =
      Real.log (Ideal.absNorm p.asIdeal : ℝ) *
        (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) /
      (1 - (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ)) := by
  let N : ℕ := Ideal.absNorm p.asIdeal
  have hN2 : 2 ≤ N := two_le_absNorm_heightOne K p
  have hN0 : (0 : ℝ) < N := by positivity
  have hpowlt : (N : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN2) (by linarith)
  rw [dedekindPrimeLogDerivative, norm_div, norm_mul, norm_neg, ← Complex.natCast_log,
    Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg _),
    show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast,
    ← Complex.ofReal_neg, ← Complex.ofReal_cpow hN0.le,
    ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hN0.le _),
    abs_of_pos (sub_pos.mpr hpowlt)]

/-- Each differentiated prime factor decays from its value on the line
`Re s = 4` by the uniform factor `2 ^ (4 - Re s)`. -/
theorem norm_dedekindPrimeLogDerivative_le_scaled_four
    (K : Type) [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖dedekindPrimeLogDerivative K p s‖ ≤
      (2 : ℝ) ^ (4 - s.re) * ‖dedekindPrimeLogDerivative K p 4‖ := by
  have h4 := norm_dedekindPrimeLogDerivative_ofReal K p (σ := 4) (by norm_num)
  push_cast at h4
  rw [h4, ← mul_div_assoc]
  refine (norm_dedekindPrimeLogDerivative_le_real K p (by linarith)).trans ?_
  set N : ℕ := Ideal.absNorm p.asIdeal
  have hN2 : 2 ≤ N := two_le_absNorm_heightOne K p
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hsplit : (N : ℝ) ^ (-s.re) = (N : ℝ) ^ (4 - s.re) * (N : ℝ) ^ (-4 : ℝ) := by
    rw [← Real.rpow_add hN0]
    ring_nf
  have hab : (N : ℝ) ^ (-s.re) ≤ (N : ℝ) ^ (-4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hbase : (N : ℝ) ^ (4 - s.re) ≤ (2 : ℝ) ^ (4 - s.re) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hN2) (by linarith)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  refine div_le_div₀ (by positivity) ?_
    (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN2) (by norm_num)))
    (by linarith)
  rw [hsplit, mul_left_comm]
  gcongr

/-- The differentiated prime Euler factors sum directly to the derivative
of the Euler logarithm. -/
theorem hasSum_dedekindPrimeLogDerivative_eulerLog
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K) => dedekindPrimeLogDerivative K p s)
      (deriv (dedekindEulerLog K) s) :=
  (dedekindEulerLog_eventuallyEq_tsum K hs).deriv_eq ▸ hasSum_dedekindPrimeLogDerivative K hs

/-- Explicit Euler-product bound for the logarithmic derivative on the
closed half-plane `Re s ≥ 4`. -/
theorem analyticDedekindZeta_logDeriv_explicit
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 4 ≤ s.re) :
    ‖deriv (analyticDedekindZeta K) s / analyticDedekindZeta K s‖ ≤
      (2 : ℝ) ^ (4 - s.re) * dedekindLogDerivMajorant K := by
  rw [analyticDedekindZeta_logDeriv_eq_derivEulerLog K (by linarith)]
  exact (hasSum_dedekindPrimeLogDerivative_eulerLog K (s := s) (by linarith)).norm_le_of_bounded
    (by simpa only [dedekindLogDerivMajorant] using
      (summable_dedekindLogDerivMajorant K).hasSum.mul_left ((2 : ℝ) ^ (4 - s.re)))
    fun p => norm_dedekindPrimeLogDerivative_le_scaled_four K p hs

/-- A strictly positive field-dependent constant for exponential decay of
the Dedekind-zeta logarithmic derivative. -/
noncomputable def dedekindLogDerivDecayConstant
    (K : Type) [Field K] [NumberField K] : ℝ :=
  16 * (dedekindLogDerivMajorant K + 1)

/-- The majorant `dedekindLogDerivMajorant K` is nonnegative. -/
theorem dedekindLogDerivMajorant_nonneg
    (K : Type) [Field K] [NumberField K] :
    0 ≤ dedekindLogDerivMajorant K :=
  tsum_nonneg fun _ => norm_nonneg _

/-- The decay constant `dedekindLogDerivDecayConstant K` is positive. -/
theorem dedekindLogDerivDecayConstant_pos
    (K : Type) [Field K] [NumberField K] :
    0 < dedekindLogDerivDecayConstant K := by
  unfold dedekindLogDerivDecayConstant
  exact mul_pos (by norm_num)
    (by linarith [dedekindLogDerivMajorant_nonneg K])

/-- Exponential decay of the Dedekind-zeta logarithmic derivative. -/
theorem analyticDedekindZeta_logDeriv_decay
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 4 ≤ s.re) :
    ‖deriv (analyticDedekindZeta K) s / analyticDedekindZeta K s‖ ≤
      dedekindLogDerivDecayConstant K *
        Real.exp (-(Real.log 2) * s.re) := by
  have hid : (2 : ℝ) ^ (4 - s.re) = 16 * Real.exp (-(Real.log 2) * s.re) := by
    rw [Real.rpow_def_of_pos (by norm_num), show Real.log 2 * (4 - s.re) =
        4 * Real.log 2 + (-(Real.log 2) * s.re) by ring, Real.exp_add,
      ← Real.log_rpow (by norm_num), Real.exp_log (by norm_num)]
    norm_num
  refine (analyticDedekindZeta_logDeriv_explicit K hs).trans ?_
  rw [hid, dedekindLogDerivDecayConstant]
  nlinarith [Real.exp_pos (-(Real.log 2) * s.re), dedekindLogDerivMajorant_nonneg K]

/-- Constant for the weighted logarithmic-derivative estimate. -/
noncomputable def dedekindLogDerivWeightedConstant
    (K : Type) [Field K] [NumberField K] : ℝ :=
  dedekindLogDerivDecayConstant K * (Real.log 2)⁻¹ * Real.exp (-1)

/-- The weighted constant `dedekindLogDerivWeightedConstant K` is positive. -/
theorem dedekindLogDerivWeightedConstant_pos
    (K : Type) [Field K] [NumberField K] :
    0 < dedekindLogDerivWeightedConstant K := by
  unfold dedekindLogDerivWeightedConstant
  exact mul_pos
    (mul_pos (dedekindLogDerivDecayConstant_pos K)
      (inv_pos.mpr (Real.log_pos (by norm_num))))
    (Real.exp_pos _)

/-- A linearly weighted logarithmic derivative remains uniformly bounded. -/
theorem analyticDedekindZeta_logDeriv_weighted
    (K : Type) [Field K] [NumberField K]
    {s : ℂ} {x A : ℝ} (hs : 4 ≤ s.re)
    (hA : 0 ≤ A) (hxs : x ≤ A * s.re) :
    x * ‖deriv (analyticDedekindZeta K) s / analyticDedekindZeta K s‖ ≤
      dedekindLogDerivWeightedConstant K * A := by
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC := dedekindLogDerivDecayConstant_pos K
  have hsig : s.re * Real.exp (-Real.log 2 * s.re) ≤ (Real.log 2)⁻¹ * Real.exp (-1) := by
    rw [show s.re * Real.exp (-Real.log 2 * s.re) =
      (Real.log 2)⁻¹ * (Real.log 2 * s.re * Real.exp (-(Real.log 2 * s.re))) by field_simp]
    gcongr
    exact Real.mul_exp_neg_le_exp_neg_one _
  calc
    _ ≤ (A * s.re) * (dedekindLogDerivDecayConstant K * Real.exp (-Real.log 2 * s.re)) := by
      gcongr
      exact analyticDedekindZeta_logDeriv_decay K hs
    _ = A * dedekindLogDerivDecayConstant K * (s.re * Real.exp (-Real.log 2 * s.re)) := by ring
    _ ≤ A * dedekindLogDerivDecayConstant K * ((Real.log 2)⁻¹ * Real.exp (-1)) := by gcongr
    _ = dedekindLogDerivWeightedConstant K * A := by
      rw [dedekindLogDerivWeightedConstant]
      ring

end

end RiemannJensen
