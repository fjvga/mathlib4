/-
Copyright (c) 2026 Francisco Ramírez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Ramírez
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Inner product of a skew-adjoint operator with itself

For a continuous linear operator `T` on a real inner product space, being
*skew-adjoint* (`adjoint T = -T`) forces the quadratic form `x ↦ ⟪T x, x⟫_ℝ`
to vanish identically.

This is the real analogue of the situation already covered in Mathlib for the
complex case: `inner_map_self_eq_zero` (in
`Mathlib/Analysis/InnerProductSpace/LinearMap.lean`) shows that over `ℂ` the
identity `⟪T x, x⟫_ℂ = 0` characterises the zero operator *without* any
symmetry hypothesis, via complex polarization. Over `ℝ` that fails (rotations
are a counterexample), but it holds precisely for skew-adjoint operators, which
is the content of this file.

## Main results

* `ContinuousLinearMap.inner_self_eq_zero_of_adjoint_eq_neg`:
  if `adjoint T = -T` then `⟪T x, x⟫_ℝ = 0` for all `x`.
* `ContinuousLinearMap.adjoint_eq_neg_iff_inner_self_eq_zero`:
  over `ℝ`, `adjoint T = -T` is *equivalent* to `∀ x, ⟪T x, x⟫_ℝ = 0`.

## References

The skew-adjoint cancellation `⟪T x, x⟫ = 0` is the abstract Hilbert-space core
behind orthogonality identities for antisymmetric operators; see e.g.
E. Miller, *The Navier–Stokes strain equation* (Ph.D. thesis, University of
Toronto, 2019) and *A strain–vorticity interaction model equation*
(arXiv:2407.02691, 2024), where it underlies the orthogonality of the vorticity
to the symmetric strain.

## Tags

inner product space, adjoint, skew-adjoint, antisymmetric operator
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A skew-adjoint continuous linear operator on a real inner product space has
vanishing quadratic form: if `adjoint T = -T` then `⟪T x, x⟫_ℝ = 0` for all `x`.

The complex analogue (without any adjointness hypothesis) is
`inner_map_self_eq_zero`. -/
theorem inner_self_eq_zero_of_adjoint_eq_neg
    {T : E →L[ℝ] E} (hT : adjoint T = -T) (x : E) :
    ⟪T x, x⟫_ℝ = 0 := by
  -- `⟪(adjoint T) x, x⟫ = ⟪x, T x⟫ = ⟪T x, x⟫`; substituting `adjoint T = -T`
  -- gives `-⟪T x, x⟫ = ⟪T x, x⟫`, hence `⟪T x, x⟫ = 0`.
  have h1 : ⟪(adjoint T) x, x⟫_ℝ = ⟪T x, x⟫_ℝ := by
    rw [adjoint_inner_left, real_inner_comm]
  rw [hT, neg_apply, inner_neg_left] at h1
  linarith

/-- Over a real inner product space, an operator is skew-adjoint if and only if
its quadratic form vanishes identically.

The forward direction is `inner_self_eq_zero_of_adjoint_eq_neg`; the converse
uses that `⟪(T + adjoint T) x, x⟫ = 0` for all `x` forces the self-adjoint
operator `T + adjoint T` to be zero. -/
theorem adjoint_eq_neg_iff_inner_self_eq_zero {T : E →L[ℝ] E} :
    adjoint T = -T ↔ ∀ x, ⟪T x, x⟫_ℝ = 0 := by
  refine ⟨fun hT x => inner_self_eq_zero_of_adjoint_eq_neg hT x, fun hT => ?_⟩
  -- It suffices to show `adjoint T + T = 0`, equivalently `(adjoint T + T) = 0`.
  have hsa : IsSelfAdjoint (adjoint T + T) := by
    rw [isSelfAdjoint_iff', map_add, adjoint_adjoint, add_comm]
  -- `adjoint T + T` is self-adjoint with zero quadratic form, hence zero.
  have hquad : ∀ x, ⟪(adjoint T + T) x, x⟫_ℝ = 0 := by
    intro x
    -- `⟪(adjoint T) x, x⟫ = ⟪x, T x⟫ = ⟪T x, x⟫ = 0`, and `⟪T x, x⟫ = 0`.
    have hadj : ⟪(adjoint T) x, x⟫_ℝ = ⟪T x, x⟫_ℝ := by
      rw [adjoint_inner_left, real_inner_comm]
    rw [add_apply, inner_add_left, hadj, hT x, add_zero]
  -- A self-adjoint operator with vanishing real quadratic form is zero.
  have hsymm : (↑(adjoint T + T) : E →ₗ[ℝ] E).IsSymmetric := hsa.isSymmetric
  have hT0 : ((adjoint T + T : E →L[ℝ] E) : E →ₗ[ℝ] E) = 0 :=
    (hsymm.inner_map_self_eq_zero).mp hquad
  have hzero : adjoint T + T = 0 := by
    ext x
    simpa using congrArg (fun L => L x) hT0
  -- From `adjoint T + T = 0` conclude `adjoint T = -T`.
  exact eq_neg_of_add_eq_zero_left hzero

end ContinuousLinearMap
