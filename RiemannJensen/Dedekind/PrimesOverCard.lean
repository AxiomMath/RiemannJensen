module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The number of primes over a rational prime

For a number field `K` and a nonzero prime `q` of `ℤ`, at most `[K : ℚ]` primes of `𝓞 K` lie
over `q`.
-/

public section

namespace RiemannJensen

open NumberField

/-- For a number field `K` and a nonzero maximal ideal `q` of `ℤ`, at most `[K : ℚ]` prime
ideals of `𝓞 K` lie over `q`. -/
theorem card_primesOverFinset_le_finrank (K : Type*) [Field K] [NumberField K] {q : Ideal ℤ}
    [q.IsMaximal] (hq0 : q ≠ ⊥) :
    (IsDedekindDomain.primesOverFinset q (𝓞 K)).card ≤ Module.finrank ℚ K := by
  have hcoe := IsDedekindDomain.coe_primesOverFinset hq0 (𝓞 K)
  let _ : Fintype (q.primesOver (𝓞 K)) :=
    Fintype.ofFinset (IsDedekindDomain.primesOverFinset q (𝓞 K)) fun x => by
      rw [← Finset.mem_coe, hcoe]
  calc (IsDedekindDomain.primesOverFinset q (𝓞 K)).card
      = ∑ _ : q.primesOver (𝓞 K), 1 := by simp [Fintype.card_ofFinset]
    _ ≤ ∑ Q : q.primesOver (𝓞 K), Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ :=
        Finset.sum_le_sum fun Q _ => Nat.one_le_iff_ne_zero.mpr <|
          mul_ne_zero (Ideal.ramificationIdx_pos (R := ℤ) Q.1).ne' (Ideal.inertiaDeg_pos Q.1 ℤ).ne'
    _ = Module.finrank ℤ (𝓞 K) := Ideal.sum_ramification_inertia_eq_finrank q (𝓞 K)
    _ = Module.finrank ℚ K := RingOfIntegers.rank K

end RiemannJensen

end
