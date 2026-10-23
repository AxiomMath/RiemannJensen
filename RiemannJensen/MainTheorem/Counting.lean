module

public import RiemannJensen.Analysis.PhaseCrossings
public import RiemannJensen.Analysis.Scale
public import RiemannJensen.Polynomial

/-!
# Counting roots produced by the oscillatory argument

Lower bounds for the number of distinct negative roots of a Jensen polynomial. An injective
family of positive zeros `q` of `q ↦ (rescaledJensen d).eval (-q)` yields the same number of
distinct negative roots `-(scaleT d) ^ 2 / (d * q)` of `jensenPolynomial d`, and an oscillatory
formula `2 * R q * (cos (θ q) + E q)` with `|E q| < 1 / 2` on an interval over which `θ` increases
by at least `(n + 1) * π` gives at least `n` such roots.

## Main results

* `le_negativeDistinctRootCount_of_injective`: an injective `Fin n`-family of negative roots of
  `p` gives `n ≤ negativeDistinctRootCount p`.
* `le_negativeJensenRootCount_of_rescaled_roots`: `n` distinct positive zeros of the rescaled
  reciprocal polynomial give `n ≤ negativeJensenRootCount d`.
* `le_negativeJensenRootCount_of_phaseSpan`: a phase span of `(n + 1) * π` gives
  `n ≤ negativeJensenRootCount d`.
-/

@[expose] public section

namespace RiemannJensen

open Set Polynomial

/-- An injective `Fin n`-family of distinct negative roots contributes at least
`n` elements to `negativeDistinctRootCount`. -/
theorem le_negativeDistinctRootCount_of_injective
    {p : ℝ[X]} {n : ℕ} (hp : p ≠ 0) (z : Fin n → ℝ) (hz_inj : Function.Injective z)
    (hz_neg : ∀ i, z i < 0) (hz_root : ∀ i, p.eval (z i) = 0) :
    n ≤ negativeDistinctRootCount p := by
  classical
  let rootsNeg : Finset ℝ := p.roots.toFinset.filter fun x : ℝ => x < 0
  let f : Fin n → rootsNeg := fun i => ⟨z i, by
    simp only [rootsNeg, Finset.mem_filter, Multiset.mem_toFinset]
    exact ⟨(Polynomial.mem_roots hp).2 (hz_root i), hz_neg i⟩⟩
  simpa [negativeDistinctRootCount, rootsNeg] using
    Fintype.card_le_of_injective f fun i j hij => hz_inj (congrArg Subtype.val hij)

/-- If `gammaCoeff d ≠ 0`, an injective `Fin n`-family of negative roots of `jensenPolynomial d`
gives `n ≤ negativeJensenRootCount d`. -/
theorem le_negativeJensenRootCount_of_injective
    {d n : ℕ} (hgamma : gammaCoeff d ≠ 0) (z : Fin n → ℝ)
    (hz_inj : Function.Injective z)
    (hz_neg : ∀ i, z i < 0)
    (hz_root : ∀ i, (jensenPolynomial d).eval (z i) = 0) :
    n ≤ negativeJensenRootCount d :=
  le_negativeDistinctRootCount_of_injective
    (fun hp => hgamma (by simpa [coeff_jensenPolynomial_self] using congrArg (coeff · d) hp))
    z hz_inj hz_neg hz_root

/-- For `0 < A` and `0 < q`, the quotient `-A / q` is negative. -/
theorem reciprocalRootArgument_neg {A q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    -A / q < 0 :=
  div_neg_of_neg_of_pos (neg_lt_zero.mpr hA) hq

/-- For `A ≠ 0` and an injective family `q`, the family `i ↦ -A / q i` is injective. -/
theorem reciprocalRootArgument_injective {A : ℝ} (hA : A ≠ 0)
    {ι : Type*} {q : ι → ℝ} (hq_inj : Function.Injective q) :
    Function.Injective (fun i => -A / q i) := by
  intro i j hij
  apply hq_inj
  apply inv_injective
  apply (mul_left_cancel₀ (neg_ne_zero.mpr hA))
  simpa [div_eq_mul_inv] using hij

/-- If `0 < q` and `(rescaledJensen d).eval (-q) = 0`, then `x = -(scaleT d) ^ 2 / (d * q)` is
a negative root of `jensenPolynomial d`. -/
theorem rescaledJensen_root_transport
    (d : ℕ) (hd : 1 ≤ d) (hgamma : gammaCoeff d ≠ 0)
    {q : ℝ} (hq : 0 < q)
    (hroot : (rescaledJensen d).eval (-q) = 0) :
    -(scaleT d) ^ 2 / ((d : ℝ) * q) < 0 ∧
      (jensenPolynomial d).eval (-(scaleT d) ^ 2 / ((d : ℝ) * q)) = 0 :=
  ⟨reciprocalRootArgument_neg (pow_pos (lt_trans (by positivity) (scaleT_gt_base d hd)) 2)
      (mul_pos (Nat.cast_pos.mpr hd) hq),
    (rescaledJensen_neg_zero_iff d hd (natDegree_jensenPolynomial d hgamma) hq).mp hroot⟩

/-- An injective positive family of zeros of the rescaled reciprocal polynomial
produces the same number of distinct negative Jensen roots. -/
theorem le_negativeJensenRootCount_of_rescaled_roots
    (d : ℕ) {n : ℕ} (hd : 1 ≤ d) (hgamma : gammaCoeff d ≠ 0)
    (q : Fin n → ℝ) (hq_inj : Function.Injective q)
    (hq_pos : ∀ i, 0 < q i)
    (hq_root : ∀ i, (rescaledJensen d).eval (-(q i)) = 0) :
    n ≤ negativeJensenRootCount d := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  exact le_negativeJensenRootCount_of_injective hgamma _
    (reciprocalRootArgument_injective
      (pow_ne_zero 2 (lt_trans (by positivity) (scaleT_gt_base d hd)).ne')
      fun i j hij => hq_inj (mul_left_cancel₀ hd0 hij))
    (fun i => (rescaledJensen_root_transport d hd hgamma (hq_pos i) (hq_root i)).1)
    (fun i => (rescaledJensen_root_transport d hd hgamma (hq_pos i) (hq_root i)).2)

/-- If `(rescaledJensen d).eval (-q) = 2 * R q * (cos (θ q) + E q)` on `[a, b]` with `0 < a`,
`0 < R q` and `|E q| < 1 / 2`, and `(n + 1) * π ≤ θ b - θ a`, then
`n ≤ negativeJensenRootCount d`. -/
theorem le_negativeJensenRootCount_of_phaseSpan
    (d : ℕ) {n : ℕ} (hd : 1 ≤ d) (hgamma : gammaCoeff d ≠ 0)
    (R E θ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hPcont : ContinuousOn (fun q => (rescaledJensen d).eval (-q)) (Icc a b))
    (hθcont : ContinuousOn θ (Icc a b))
    (hR : ∀ q ∈ Icc a b, 0 < R q)
    (hE : ∀ q ∈ Icc a b, |E q| < 1 / 2)
    (hformula : ∀ q ∈ Icc a b,
      (rescaledJensen d).eval (-q) = 2 * R q * (Real.cos (θ q) + E q))
    (hspan : ((n + 1 : ℕ) : ℝ) * Real.pi ≤ θ b - θ a) :
    n ≤ negativeJensenRootCount d := by
  obtain ⟨q, hq_inj, hq⟩ := phaseCrossings_of_phaseSpan
    (fun x => (rescaledJensen d).eval (-x)) R E θ a b n hab hPcont hθcont
      hR hE hformula hspan
  exact le_negativeJensenRootCount_of_rescaled_roots d hd hgamma q hq_inj
    (fun i => ha.trans (hq i).1.1) fun i => (hq i).2

end RiemannJensen
