/-
Copyright (c) 2026 Francisco Ramírez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Ramírez
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Topology
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Analytic matrix families have full rank almost everywhere

For a real-analytic matrix family `A : ℝ → Matrix (Fin k) (Fin k) ℝ` whose entries
are analytic on all of `ℝ`, if the determinant is nonzero at a single point
(`∃ ξ₀, (A ξ₀).det ≠ 0`), then the family has full rank `(A ξ).rank = k` for
`μ`-almost-every `ξ`, for any atomless measure `μ`.

This combines three facts:
1. the determinant of an analytic matrix family is analytic (`det_analyticOnNhd`,
   via the Leibniz expansion and closure of analytic functions under finite sums
   and products);
2. a nonzero real-analytic function is nonzero almost everywhere
   (`analyticOnNhd_ne_zero_ae`, the companion lemma
   `AnalyticMeasureZero.analyticOnNhd_ne_zero_ae`);
3. a square matrix with nonzero determinant has full rank.

## Main results

* `det_analyticOnNhd`: the determinant of an analytic matrix family is analytic.
* `rank_full_ae`: an analytic matrix family with a nondegenerate witness has
  full rank `μ`-almost-everywhere, for any atomless `μ`.
* `rankDrop_subset_detZero`: the rank-drop locus is contained in the
  determinant-zero locus.

## References

The fact that the zero set of a nontrivial real-analytic function has measure
zero is classical; see e.g. S. Krantz, H. Parks, *A Primer of Real Analytic
Functions* (Birkhäuser, 2002). Rank genericity for analytic families is a
standard consequence.

## Tags

analytic function, matrix, determinant, rank, measure zero, almost everywhere
-/

open MeasureTheory

namespace Matrix

/-- A nonzero real-analytic function `f : ℝ → ℝ` satisfies `f x ≠ 0` for
`μ`-almost-every `x`, for any atomless measure `μ`.

(Companion lemma from `AnalyticMeasureZero`; included here so this file is
self-contained. In Mathlib this lives in `Analysis/Analytic/MeasureZero.lean`.) -/
theorem analyticOnNhd_ne_zero_ae {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ) (h0 : ∃ x, f x ≠ 0)
    {μ : Measure ℝ} [NoAtoms μ] :
    ∀ᵐ x ∂μ, f x ≠ 0 := by
  have hnotEqOn : ¬ Set.EqOn f 0 Set.univ := fun h ↦
    let ⟨x, hx⟩ := h0; hx (h (Set.mem_univ x))
  have hdich : Set.EqOn f 0 Set.univ ∨ ∀ᶠ x in codiscreteWithin Set.univ, f x ≠ 0 :=
    hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ
  rcases hdich with hEq | hCodisc
  · exact absurd hEq hnotEqOn
  · have hle : ae (μ.restrict Set.univ) ≤ codiscreteWithin Set.univ :=
      ae_restrict_le_codiscreteWithin (μ := μ) MeasurableSet.univ
    have hae_restrict : ∀ᵐ x ∂(μ.restrict Set.univ), f x ≠ 0 := hle hCodisc
    rwa [Measure.restrict_univ] at hae_restrict

/-- The determinant of a real-analytic square matrix family `A : ℝ → Matrix (Fin k)
(Fin k) ℝ` (analytic entrywise) is itself a real-analytic function of `ξ`. -/
theorem det_analyticOnNhd {k : ℕ} (A : ℝ → Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun ξ => A ξ i j) Set.univ) :
    AnalyticOnNhd ℝ (fun ξ => (A ξ).det) Set.univ := by
  have hgoal : ∀ ξ, (A ξ).det
      = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A ξ (σ i) i :=
    fun ξ => Matrix.det_apply' (A ξ)
  simp only [hgoal]
  apply Finset.analyticOnNhd_fun_sum
  intro σ _
  have hprod : AnalyticOnNhd ℝ (fun ξ => ∏ i, A ξ (σ i) i) Set.univ := by
    apply Finset.analyticOnNhd_fun_prod
    intro i _
    exact hA (σ i) i
  exact analyticOnNhd_const.mul hprod

/-- A square matrix with nonzero determinant has full rank. -/
theorem rank_eq_card_of_det_ne_zero {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (h : M.det ≠ 0) : M.rank = k := by
  have hunit : IsUnit M := M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr h)
  have hrank : M.rank = Fintype.card (Fin k) := Matrix.rank_of_isUnit M hunit
  simpa using hrank

/-- The rank-drop locus `{ξ | (A ξ).rank ≠ k}` is contained in the
determinant-zero locus `{ξ | (A ξ).det = 0}`. -/
theorem rankDrop_subset_detZero {k : ℕ} (A : ℝ → Matrix (Fin k) (Fin k) ℝ) :
    {ξ : ℝ | (A ξ).rank ≠ k} ⊆ {ξ : ℝ | (A ξ).det = 0} := by
  intro ξ hξ
  simp only [Set.mem_setOf_eq] at hξ ⊢
  by_contra hdet
  exact hξ (rank_eq_card_of_det_ne_zero (A ξ) hdet)

/-- An analytic square matrix family with a nondegenerate witness has full rank
`μ`-almost-everywhere, for any atomless measure `μ`. -/
theorem rank_full_ae {k : ℕ} (A : ℝ → Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun ξ => A ξ i j) Set.univ)
    (hwit : ∃ ξ₀ : ℝ, (A ξ₀).det ≠ 0)
    {μ : Measure ℝ} [NoAtoms μ] :
    ∀ᵐ ξ ∂μ, (A ξ).rank = k := by
  have hdet_ne : ∀ᵐ ξ ∂μ, (A ξ).det ≠ 0 :=
    analyticOnNhd_ne_zero_ae (det_analyticOnNhd A hA) hwit
  filter_upwards [hdet_ne] with ξ hξ
  exact rank_eq_card_of_det_ne_zero (A ξ) hξ

end Matrix
