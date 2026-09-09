/-
Copyright (c) 2026 Francisco Ramírez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Ramírez
-/
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Map

/-!
# Integral of the Birkhoff sum under a measure-preserving map

For a measure-preserving map `T` on `(α, μ)` and an integrable function `φ`,
the integral of the Birkhoff sum `S_m φ(x) = Σ_{k < m} φ(T^k x)` satisfies
`∫ S_m φ dμ = m • ∫ φ dμ`. Dividing by `m > 0` gives the exact identity
`(1/m) ∫ S_m φ dμ = ∫ φ dμ` — the measure-averaged Birkhoff energy equals the
single-step integral, with no limit.

Mathlib defines `birkhoffSum` and `MeasurePreserving`, and has the
single-step integral invariance (`MeasurePreserving.integral_comp`), but does
not package the iterated-step invariance or the Birkhoff-sum identity.

## Main results

* `integral_comp_iterate`: `∫ φ ∘ T^[k] dμ = ∫ φ dμ` for `MeasurePreserving T μ μ`.
* `integral_birkhoffSum`: `∫ birkhoffSum T φ m dμ = m • ∫ φ dμ`.
* `integral_birkhoffSum_div`: `(∫ birkhoffSum T φ m dμ) / m = ∫ φ dμ` for `m > 0`.

## References

The Birkhoff ergodic theorem; see e.g. K. Petersen, *Ergodic Theory*
(Cambridge, 1983), §2. The integral identity is the zero-frequency case.

## Tags

Birkhoff sum, measure preserving, integral invariance, ergodic theory
-/

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {φ : α → ℝ}

/-- For `MeasurePreserving T μ μ`, the integral of `φ ∘ T^[k]` equals the
integral of `φ`. -/
theorem integral_comp_iterate (hT : MeasurePreserving T μ μ) (hTm : Measurable T)
    (hφ : AEStronglyMeasurable φ μ) (k : ℕ) :
    ∫ x, φ ((T^[k]) x) ∂μ = ∫ x, φ x ∂μ := by
  have hTk : MeasurePreserving (T^[k]) μ μ := hT.iterate k
  have hTkm : Measurable (T^[k]) := hTm.iterate k
  conv_rhs => rw [← hTk.map_eq]
  rw [integral_map hTkm.aemeasurable (by rw [hTk.map_eq]; exact hφ)]

/-- The integral of the Birkhoff sum `S_m φ = Σ_{k<m} φ ∘ T^[k]` equals
`m • ∫ φ dμ`. -/
theorem integral_birkhoffSum (hT : MeasurePreserving T μ μ) (hTm : Measurable T)
    (hφ : Integrable φ μ) (m : ℕ) :
    ∫ x, birkhoffSum T φ m x ∂μ = (m : ℝ) * ∫ x, φ x ∂μ := by
  have hexp : (fun x => birkhoffSum T φ m x) = fun x => ∑ k ∈ Finset.range m, φ ((T^[k]) x) :=
    rfl
  rw [hexp]
  have hint : ∀ k ∈ Finset.range m, Integrable (fun x => φ ((T^[k]) x)) μ := by
    intro k _
    exact ((hT.iterate k).integrable_comp hφ.aestronglyMeasurable).mpr hφ
  rw [integral_finset_sum (Finset.range m) hint]
  have hterm : ∀ k ∈ Finset.range m, (∫ x, φ ((T^[k]) x) ∂μ) = ∫ x, φ x ∂μ := by
    intro k _
    exact integral_comp_iterate hT hTm hφ.aestronglyMeasurable k
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- For `m > 0`, the measure-averaged Birkhoff energy is exactly `∫ φ dμ`:
`(∫ S_m φ dμ) / m = ∫ φ dμ`. No limit, no oscillation hypothesis. -/
theorem integral_birkhoffSum_div (hT : MeasurePreserving T μ μ) (hTm : Measurable T)
    (hφ : Integrable φ μ) (m : ℕ) (hm : 0 < m) :
    (∫ x, birkhoffSum T φ m x ∂μ) / m = ∫ x, φ x ∂μ := by
  rw [integral_birkhoffSum hT hTm hφ m]
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
