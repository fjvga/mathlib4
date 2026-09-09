/-
Copyright (c) 2026 Francisco Ramírez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Ramírez
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Topology
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-!
# Measure-zero of the zero set of a nontrivial real-analytic function

A real-analytic function `f : ℝ → ℝ` that is not identically zero vanishes only
on a set of `μ`-measure zero, for any atomless measure `μ` (in particular for
Lebesgue measure, and for any atomless probability measure).

This is the measure-theoretic packaging of Mathlib's isolated-zeros dichotomy
`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`: an analytic
function on a preconnected open set is either identically zero, or it is
eventually nonzero on a codiscrete set, and a codiscrete set has full measure
with respect to any atomless measure (`ae_restrict_le_codiscreteWithin`).

## Main results

* `analyticOnNhd_ne_zero_ae`: a nonzero real-analytic function on `ℝ` satisfies
  `f x ≠ 0` for `μ`-almost-every `x`, for any atomless `μ`.

## References

The isolated-zeros principle for analytic functions is classical; see e.g.
S. Krantz, H. Parks, *A Primer of Real Analytic Functions* (Birkhäuser, 2002).
The codiscrete-to-a.e. bridge is a standard measure-theoretic refinement.

## Tags

analytic function, isolated zeros, measure zero, atomless measure
-/

open MeasureTheory

/-- A real-analytic function `f : ℝ → ℝ` that is not identically zero satisfies
`f x ≠ 0` for `μ`-almost-every `x`, for any atomless measure `μ`. -/
theorem analyticOnNhd_ne_zero_ae {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ) (h0 : ∃ x, f x ≠ 0)
    {μ : Measure ℝ} [NoAtoms μ] :
    ∀ᵐ x ∂μ, f x ≠ 0 := by
  -- `f` is not identically zero on `univ`.
  have hnotEqOn : ¬ Set.EqOn f 0 Set.univ := by
    intro h
    obtain ⟨x, hx⟩ := h0
    exact hx (h (Set.mem_univ x))
  -- Isolated-zeros dichotomy (global version, `univ` is preconnected).
  have hdich :
      Set.EqOn f 0 Set.univ ∨ ∀ᶠ x in codiscreteWithin Set.univ, f x ≠ 0 :=
    hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ
  rcases hdich with hEq | hCodisc
  · exact absurd hEq hnotEqOn
  · -- `{x | f x ≠ 0}` is codiscrete in `univ`; transfer to "almost everywhere".
    have hle : ae (μ.restrict Set.univ) ≤ codiscreteWithin Set.univ :=
      ae_restrict_le_codiscreteWithin (μ := μ) MeasurableSet.univ
    have hae_restrict : ∀ᵐ x ∂(μ.restrict Set.univ), f x ≠ 0 := hle hCodisc
    rwa [Measure.restrict_univ] at hae_restrict
