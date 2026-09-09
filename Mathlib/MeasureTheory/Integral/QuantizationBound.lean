/-
Copyright (c) 2026 Francisco Ramírez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Ramírez
-/

module
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Quantization bound for integrals over finite partitions

Given a finite measurable partition `{A i}_{i < n}` of the space, an integrable
function `g`, representatives `xr i ∈ A i`, and oscillation bounds
`B i` (with `|g x - g (xr i)| ≤ B i` on `A i`), the integral of `g` is
approximated by the quantized sum `Σ μ(A i) · g(xr i)` with error bounded by
`Σ μ(A i) · B i`:

  `|∫ g dμ − Σ μ(A i) · g(xr i)| ≤ Σ μ(A i) · B i`.

This is an elementary but useful estimate: the error of approximating an
integral by a finite sum over a partition is controlled by the oscillation
of the function on each cell.

## Main results

* `local_quant`: on a single cell `A` of finite measure, `|∫_A g − μ(A)·c| ≤ B·μ(A)`
  when `|g x − c| ≤ B` on `A`.
* `quantization_bound`: the global bound over a finite partition.

## References

Standard partition-based quadrature error estimate; see e.g. the treatment of
Riemann sums in any measure theory textbook.

## Tags

integral, partition, quantization, Riemann sum, error bound
-/

@[expose] public section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- On a single measurable set `A` of finite measure, if `|g x − c| ≤ B` on `A`,
then `|∫_A g dμ − μ(A)·c| ≤ B·μ(A)`. -/
theorem local_quant (g : X → ℝ) (A : Set X) (c B : ℝ) (hμ : μ A < ⊤)
    (hg : IntegrableOn g A μ) (hb : ∀ x ∈ A, |g x - c| ≤ B) :
    |(∫ x in A, g x ∂μ) - μ.real A * c| ≤ B * μ.real A := by
  have hconst : IntegrableOn (fun _ => c) A μ := by
    have : IsFiniteMeasure (μ.restrict A) := ⟨by rwa [Measure.restrict_apply_univ]⟩
    exact integrable_const c
  have h1 : (∫ x in A, g x ∂μ) - μ.real A * c = ∫ x in A, (g x - c) ∂μ := by
    rw [integral_sub hg hconst, setIntegral_const, smul_eq_mul]
  rw [h1]
  have := norm_setIntegral_le_of_norm_le_const (f := fun x => g x - c) (s := A) (C := B) hμ
    (by intro x hx; rw [Real.norm_eq_abs]; exact hb x hx)
  rwa [Real.norm_eq_abs] at this

/-- **Quantization bound.** Over a finite measurable disjoint partition
`{A i}` covering `univ`, with representatives `xr i` and oscillation bounds
`B i`, the integral is approximated by the quantized sum with error
`≤ Σ μ(A i) · B i`. -/
theorem quantization_bound {n : ℕ} (g : X → ℝ) (A : Fin n → Set X)
    (hmeas : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : ⋃ i, A i = Set.univ) (hfin : ∀ i, μ (A i) < ⊤) (hg : Integrable g μ)
    (xr : Fin n → X) (B : Fin n → ℝ)
    (hb : ∀ i, ∀ x ∈ A i, |g x - g (xr i)| ≤ B i) :
    |(∫ x, g x ∂μ) - ∑ i, μ.real (A i) * g (xr i)| ≤ ∑ i, μ.real (A i) * B i := by
  have hsplit : (∫ x, g x ∂μ) = ∑ i, ∫ x in A i, g x ∂μ := by
    conv_lhs => rw [← setIntegral_univ, ← hcover]
    exact integral_iUnion_fintype hmeas hdisj (fun i => hg.integrableOn)
  rw [hsplit, ← Finset.sum_sub_distrib]
  calc |∑ i, ((∫ x in A i, g x ∂μ) - μ.real (A i) * g (xr i))|
      ≤ ∑ i, |(∫ x in A i, g x ∂μ) - μ.real (A i) * g (xr i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, B i * μ.real (A i) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact local_quant g (A i) (g (xr i)) (B i) (hfin i) hg.integrableOn (hb i)
    _ = ∑ i, μ.real (A i) * B i := Finset.sum_congr rfl (fun i _ => by ring)
