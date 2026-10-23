module

public import RiemannJensen.Dedekind.EulerProductBridge
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# Bounds for the Dedekind Euler logarithm

For a number field `K`, the Euler logarithm of the Dedekind zeta function is the sum over the
nonzero prime ideals `p` of `-log (1 - N(p) ^ (-s))`. On a half-plane `Re s ≥ a` with `a > 1`
each term is bounded by `(3 / 2) * N(p) ^ (-a)`, so the sum converges absolutely and locally
uniformly on `Re s > 1`, and on `Re s ≥ 4` the Dedekind zeta function is bounded above and away
from zero by constants depending only on `K`.

## Main definitions

* `dedekindPrimeLogFactor`: The logarithm `-log (1 - N(p) ^ (-s))` of one Euler factor.
* `rationalPrimeBelow`: The rational prime lying below a prime ideal.
* `dedekindEulerLogMajorant`: The sum over prime ideals `p` of `(3 / 2) * N(p) ^ (-a)`.

## Main results

* `absNorm_eq_rationalPrimeBelow_pow`: `N(p)` is a power of the rational prime below `p`.
* `norm_dedekindPrimeLogFactor_le`: The bound `(3 / 2) * N(p) ^ (-a)` on one Euler logarithm.
* `dedekindEulerLog_converges`: Absolute and locally uniform convergence on `Re s > 1`.
* `norm_dedekindEulerLog_le_majorant`: The Euler logarithm is bounded by the majorant.
* `analyticDedekindZeta_norm_le_exp_majorant_four`,
  `exp_neg_majorant_four_le_analyticDedekindZeta_norm`: Upper and lower bounds for the Dedekind
  zeta function on `Re s ≥ 4`.
-/

@[expose] public section

namespace RiemannJensen

set_option autoImplicit false

noncomputable section

open NumberField Filter Complex
open scoped Topology Classical

/-- The logarithm of one prime-ideal Euler factor. -/
def dedekindPrimeLogFactor
    (K : Type) [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (s : ℂ) : ℂ :=
  -Complex.log (1 - ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s))

/-- The rational prime below a prime ideal of a number field. -/
def rationalPrimeBelow
    (K : Type) [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nat.Primes := by
  letI : NeZero p.asIdeal := ⟨p.ne_bot⟩
  exact ⟨Ideal.absNorm (Ideal.under ℤ p.asIdeal), Nat.absNorm_under_prime p.asIdeal⟩

/-- The norm of a prime ideal is a positive power of its rational prime below. -/
theorem absNorm_eq_rationalPrimeBelow_pow
    (K : Type) [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Ideal.absNorm p.asIdeal =
      (rationalPrimeBelow K p).1 ^ p.asIdeal.inertiaDeg ℤ :=
  (Ideal.absNorm_pow_inertiaDeg (Ideal.under ℤ p.asIdeal) p.asIdeal).symm

/-- On `Re s ≥ a` with `a > 1`, the Euler logarithm of a prime ideal `p` has norm at most
`(3 / 2) * N(p) ^ (-a)`. -/
theorem norm_dedekindPrimeLogFactor_le
    (K : Type) [Field K] [NumberField K] {a : ℝ} (ha : 1 < a)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {s : ℂ} (hs : a ≤ s.re) :
    ‖dedekindPrimeLogFactor K p s‖ ≤
      (3 / 2 : ℝ) * (Ideal.absNorm p.asIdeal : ℝ) ^ (-a) := by
  let q : ℕ := Ideal.absNorm p.asIdeal
  have hq2 : 2 ≤ q := two_le_absNorm_heightOne K p
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hpow : ‖(q : ℂ) ^ (-s)‖ ≤ (q : ℝ) ^ (-a) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hqone (by linarith)
  have hhalf : (q : ℝ) ^ (-a) ≤ 1 / 2 := by
    calc
      (q : ℝ) ^ (-a) ≤ (q : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hqone (by linarith)
      _ ≤ 1 / 2 := by
        rw [Real.rpow_neg_one, one_div]
        gcongr
        exact_mod_cast hq2
  rw [dedekindPrimeLogFactor, norm_neg, sub_eq_add_neg]
  refine (Complex.norm_log_one_add_half_le_self
    ((norm_neg _).trans_le (hpow.trans hhalf))).trans ?_
  simpa [q] using mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 3 / 2)

/-- The majorant is summable for every real exponent greater than one. -/
theorem summable_dedekindEulerLogMajorant
    (K : Type) [Field K] [NumberField K] {a : ℝ} (ha : 1 < a) :
    Summable (fun p : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K) =>
      (3 / 2 : ℝ) * (Ideal.absNorm p.asIdeal : ℝ) ^ (-a)) :=
  ((EulerProductBridge.P6B.ZetaNeZero.summable_absNorm_rpow K ha).comp_injective
    fun _ _ => IsDedekindDomain.HeightOneSpectrum.ext).mul_left (3 / 2 : ℝ)

/-- The sum over prime ideals of `dedekindPrimeLogFactor` converges absolutely and locally
uniformly on `Re s > 1`. -/
theorem dedekindEulerLog_converges
    (K : Type) [Field K] [NumberField K] :
    (∀ s : ℂ, 1 < s.re → Summable (fun p :
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        dedekindPrimeLogFactor K p s)) ∧
    HasSumLocallyUniformlyOn
      (fun p : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K) => fun s : ℂ => dedekindPrimeLogFactor K p s)
      (fun s : ℂ => ∑' p : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K), dedekindPrimeLogFactor K p s)
      {s : ℂ | 1 < s.re} := by
  refine ⟨fun s hs => by
    simpa [dedekindPrimeLogFactor] using dedekindPrimeLog_summable K hs, ?_⟩
  refine SummableLocallyUniformlyOn.hasSumLocallyUniformlyOn
    (SummableLocallyUniformlyOn_of_locally_bounded
      (isOpen_lt continuous_const continuous_re) fun C hC hCcompact => ?_)
  by_cases hCne : C.Nonempty
  · obtain ⟨z, hzC, hzmin⟩ := hCcompact.exists_isMinOn hCne continuous_re.continuousOn
    exact ⟨_, summable_dedekindEulerLogMajorant K (hC hzC),
      fun p s hsC => norm_dedekindPrimeLogFactor_le K (hC hzC) p (hzmin hsC)⟩
  · exact ⟨fun _ => 0, summable_zero, fun _ s hs => (hCne ⟨s, hs⟩).elim⟩

/-- The sum over prime ideals `p` of `(3 / 2) * N(p) ^ (-a)`, a majorant for the Euler
logarithm on `Re s ≥ a`. -/
def dedekindEulerLogMajorant
    (K : Type) [Field K] [NumberField K] (a : ℝ) : ℝ :=
  ∑' p : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K),
    (3 / 2 : ℝ) * (Ideal.absNorm p.asIdeal : ℝ) ^ (-a)

/-- On `Re s > 1`, `dedekindEulerLog` is the sum over prime ideals of
`dedekindPrimeLogFactor`. -/
theorem dedekindEulerLog_eq_locallyUniformSum
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindEulerLog K s =
      ∑' p : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K), dedekindPrimeLogFactor K p s := by
  simpa [dedekindPrimeLogFactor] using dedekindEulerLog_eq_primeLogSum K hs

/-- On `Re s ≥ a` with `a > 1`, the Dedekind Euler logarithm is bounded in norm by
`dedekindEulerLogMajorant K a`. -/
theorem norm_dedekindEulerLog_le_majorant
    (K : Type) [Field K] [NumberField K] {a : ℝ} (ha : 1 < a)
    {s : ℂ} (hs : a ≤ s.re) :
    ‖dedekindEulerLog K s‖ ≤ dedekindEulerLogMajorant K a := by
  have hf := (dedekindEulerLog_converges K).1 s (ha.trans_le hs)
  rw [dedekindEulerLog_eq_locallyUniformSum K (ha.trans_le hs), dedekindEulerLogMajorant]
  exact (norm_tsum_le_tsum_norm hf.norm).trans (Summable.tsum_le_tsum
    (fun p => norm_dedekindPrimeLogFactor_le K ha p hs) hf.norm
    (summable_dedekindEulerLogMajorant K ha))

/-- A field-dependent uniform upper bound for Dedekind zeta on `Re s ≥ 4`. -/
theorem analyticDedekindZeta_norm_le_exp_majorant_four
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 4 ≤ s.re) :
    ‖analyticDedekindZeta K s‖ ≤
      Real.exp (dedekindEulerLogMajorant K 4) := by
  rw [← dedekindEulerLog_exp K (by linarith), Complex.norm_exp, Real.exp_le_exp]
  exact (Complex.re_le_norm _).trans (norm_dedekindEulerLog_le_majorant K (by norm_num) hs)

/-- A positive field-dependent uniform lower bound for Dedekind zeta on
`Re s ≥ 4`. -/
theorem exp_neg_majorant_four_le_analyticDedekindZeta_norm
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 4 ≤ s.re) :
    Real.exp (-dedekindEulerLogMajorant K 4) ≤
      ‖analyticDedekindZeta K s‖ := by
  rw [← dedekindEulerLog_exp K (by linarith), Complex.norm_exp, Real.exp_le_exp]
  exact (neg_le_neg (norm_dedekindEulerLog_le_majorant K (by norm_num) hs)).trans
    (neg_le_of_abs_le (Complex.abs_re_le_norm _))

end

end RiemannJensen
