[![](logo.svg)](https://axiommath.ai/)

# Riemann and Dedekind Jensen Polynomials

This is a Lean formalization of the theorem that almost all zeros of the Jensen polynomials of the Riemann and Dedekind xi functions are distinct negative reals.

## Main Results

* The Dedekind zeta function of every number field has an analytic continuation to ℂ \ {1}.
* This analytic continuation is unique.
* For every number field K and all large d, the degree-d Dedekind Jensen polynomial of K is nonzero and has at least d - C √(d log d) distinct negative real roots.
* For every d ≥ 2, the degree-d Riemann Jensen polynomial has at most C √(d log d) nonreal roots and at least d - C √(d log d) distinct negative real roots.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only depends on Mathlib. It contains formal statements of [§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean comparator on a Linux machine. First, follow the instructions in https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:
```
lake env comparator Comparator/comparator.json
```

This repository has been verified with the comparator (Lean kernel only).
