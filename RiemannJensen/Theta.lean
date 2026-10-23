module

public import RiemannJensen.Xi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# The theta kernel for Riemann xi

This file defines the summands `thetaTerm` and the kernel `thetaPhi` appearing in the
theta-integral representation of `riemannXi`.

## Main definitions

* `thetaTerm`: The summand of the theta kernel indexed by the positive integer `m + 1`.
* `thetaPhi`: The theta kernel, the sum over `m` of `thetaTerm m t`.

## Main results

* `thetaTerm_pos`: Each summand is strictly positive for `0 ≤ t`.
* `summable_thetaTerm`: The series defining `thetaPhi` is summable at every real argument.
* `thetaPhi_pos`: The theta kernel is strictly positive for `0 ≤ t`.
-/

@[expose] public section

namespace RiemannJensen

/-- The summand indexed by the positive integer `m + 1` in the Riemann xi
theta kernel. -/
noncomputable def thetaTerm (m : ℕ) (t : ℝ) : ℝ :=
  let n : ℝ := (m + 1 : ℕ)
  (4 * Real.pi ^ 2 * n ^ 4 * Real.exp (9 * t / 2) -
      6 * Real.pi * n ^ 2 * Real.exp (5 * t / 2)) *
    Real.exp (-Real.pi * n ^ 2 * Real.exp (2 * t))

/-- The theta kernel `Φ(t) = ∑_{n ≥ 1} (4π²n⁴e^{9t/2} - 6πn²e^{5t/2}) exp(-πn²e^{2t})`. -/
noncomputable def thetaPhi (t : ℝ) : ℝ :=
  ∑' m : ℕ, thetaTerm m t

/-- The summand `thetaTerm m t` factors as
`2πn²e^{5t/2} · (2πn²e^{2t} - 3) · exp(-πn²e^{2t})` with `n = m + 1`. -/
theorem thetaTerm_factor (m : ℕ) (t : ℝ) :
    thetaTerm m t = 2 * Real.pi * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * t / 2) *
      (2 * Real.pi * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * t) - 3) *
      Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * t)) := by
  dsimp [thetaTerm]
  have hexp :
      Real.exp (9 * t / 2) =
        Real.exp (5 * t / 2) * Real.exp (2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Every summand of the theta kernel is strictly positive on the
nonnegative half-line. -/
theorem thetaTerm_pos (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 < thetaTerm m t := by
  rw [thetaTerm_factor]
  have hn : (1 : ℝ) ≤ (m + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hn2 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((((m + 1 : ℕ) : ℝ) - 1))]
  have he : 1 ≤ Real.exp (2 * t) :=
    Real.one_le_exp (mul_nonneg (by norm_num) ht)
  have hlarge :
      3 < 2 * Real.pi * (((m + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * t) := by
    calc
      3 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      _ = 2 * Real.pi * 1 * 1 := by ring
      _ ≤ 2 * Real.pi * (((m + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * t) := by
        gcongr
  positivity

/-- The series defining the theta kernel is summable at every real argument. -/
theorem summable_thetaTerm (t : ℝ) : Summable fun m : ℕ => thetaTerm m t := by
  have h4 :=
    HurwitzKernelBounds.summable_f_nat 4 1 (Real.exp_pos (2 * t))
  have h2 :=
    HurwitzKernelBounds.summable_f_nat 2 1 (Real.exp_pos (2 * t))
  have h4' := h4.mul_left (4 * Real.pi ^ 2 * Real.exp (9 * t / 2))
  have h2' := h2.mul_left (6 * Real.pi * Real.exp (5 * t / 2))
  apply (h4'.sub h2').congr
  intro m
  simp only [thetaTerm, HurwitzKernelBounds.f_nat, Nat.cast_add, Nat.cast_one]
  ring

/-- The theta kernel is strictly positive on the nonnegative half-line. -/
theorem thetaPhi_pos {t : ℝ} (ht : 0 ≤ t) : 0 < thetaPhi t := by
  unfold thetaPhi
  exact (summable_thetaTerm t).tsum_pos
    (fun m => (thetaTerm_pos m ht).le) 0 (thetaTerm_pos 0 ht)

end RiemannJensen
