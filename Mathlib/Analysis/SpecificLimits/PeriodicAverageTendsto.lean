/-
Copyright (c) 2026 Francisco Ramírez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Ramírez
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Continuous
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Module

/-!
# Convergence of the temporal average of a periodic function

For a continuous `T`-periodic function `h : ℝ → X` (vector-valued, over a normed
space), the temporal average `(1/T') • ∫ t in 0..T', h t` converges to the
average over one period `(1/T) • ∫ t in 0..T, h t` as `T' → ∞`.

This is the continuous Cesàro convergence for periodic functions. Mathlib has
`Filter.Tendsto.cesaro` (scalar Cesàro) and `Function.Periodic.intervalIntegral_add_zsmul_eq`
(periodicity of the integral), but not the packaged vector-valued convergence
of the time-averaged integral.

## Main results

* `periodicAverage_tendsto`: for continuous `T`-periodic `h`, the temporal
  average converges to the one-period average.

## References

The decomposition `T' = ⌊T'/T⌋·T + remainder` is the standard proof; see e.g.
H. Amann, J. Escher, *Analysis III* (Birkhäuser, 2009), §9.4.

## Tags

periodic function, Cesàro mean, temporal average, interval integral
-/

open scoped Topology
open Filter

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- For a continuous `T`-periodic function `h : ℝ → X`, the temporal average
`(1/T') • ∫ t in 0..T', h t` converges to `(1/T) • ∫ t in 0..T, h t` as
`T' → ∞`. -/
theorem periodicAverage_tendsto
    {T : ℝ} (hT : 0 < T) {h : ℝ → X}
    (hper : Function.Periodic h T) (hcont : Continuous h) :
    Tendsto (fun T' : ℝ => (1 / T') • ∫ t in (0:ℝ)..T', h t) atTop
      (𝓝 ((1 / T) • ∫ t in (0:ℝ)..T, h t)) := by
  obtain ⟨x₀, _, hx₀max⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_isMaxOn
      (Set.nonempty_Icc.mpr hT.le) (hcont.norm.continuousOn)
  set C := ‖h x₀‖ with hC
  have hCbound : ∀ t, ‖h t‖ ≤ C := by
    intro t
    set k : ℤ := ⌊t / T⌋ with hk
    have hred : h t = h (t - k * T) := (hper.sub_int_mul_eq k).symm
    have hmem : t - k * T ∈ Set.Icc (0:ℝ) T := by
      refine ⟨?_, ?_⟩
      · have h2 : (k : ℝ) * T ≤ t := by
          calc (⌊t/T⌋:ℝ) * T ≤ (t/T) * T := by nlinarith [Int.floor_le (t/T), hT]
            _ = t := by field_simp
        linarith
      · have h2 : t < ((k:ℝ) + 1) * T := by
          calc t = (t/T)*T := by field_simp
            _ < (⌊t/T⌋ + 1) * T := by nlinarith [Int.lt_floor_add_one (t/T), hT]
        nlinarith
    rw [hred]; exact hx₀max hmem
  have hint : ∀ t₁ t₂, IntervalIntegrable h volume t₁ t₂ :=
    fun t₁ t₂ => hcont.intervalIntegrable t₁ t₂
  set I := ∫ t in (0:ℝ)..T, h t with hI
  have key : Tendsto (fun T' : ℝ =>
      (1 / T') • (∫ t in (0:ℝ)..T', h t) - (1/T) • I) atTop (𝓝 0) := by
    have hdecomp : ∀ T' : ℝ,
        (∫ t in (0:ℝ)..T', h t) = (⌊T'/T⌋ : ℤ) • I + (∫ t in ((⌊T'/T⌋:ℝ)*T)..T', h t) := by
      intro T'
      have h1 : (∫ t in (0:ℝ)..((⌊T'/T⌋:ℤ) • T), h t) = (⌊T'/T⌋:ℤ) • I := by
        have := hper.intervalIntegral_add_zsmul_eq (⌊T'/T⌋:ℤ) 0 hint
        simpa [hI] using this
      have hadj := integral_add_adjacent_intervals
        (hint 0 ((⌊T'/T⌋:ℤ) • T)) (hint ((⌊T'/T⌋:ℤ) • T) T')
      rw [← hadj, h1]
      congr 2
      push_cast [zsmul_eq_mul]; ring
    set k : ℝ → ℤ := fun T' => ⌊T'/T⌋ with hkdef
    have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hCbound x₀)
    have hRbound : ∀ T' : ℝ, 0 < T' →
        ‖∫ t in ((k T':ℝ)*T)..T', h t‖ ≤ C * T := by
      intro T' hT'
      have hle : ‖∫ t in ((k T':ℝ)*T)..T', h t‖ ≤ C * |T' - (k T':ℝ)*T| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hCbound x)
      refine hle.trans ?_
      have hub : T' - (k T':ℝ)*T ≤ T := by
        have hlt := Int.lt_floor_add_one (T'/T)
        rw [hkdef]
        have : T' < ((⌊T'/T⌋:ℝ)+1)*T := by
          calc T' = (T'/T)*T := by field_simp
            _ < (⌊T'/T⌋+1)*T := by nlinarith
        nlinarith
      have hge : (k T':ℝ)*T ≤ T' := by
        rw [hkdef]
        have : (⌊T'/T⌋:ℝ) * T ≤ (T'/T)*T := by nlinarith [Int.floor_le (T'/T), hT]
        calc (⌊T'/T⌋:ℝ)*T ≤ (T'/T)*T := this
          _ = T' := by field_simp
      rw [abs_of_nonneg (by linarith)]
      nlinarith
    have hrw : ∀ T' : ℝ, 0 < T' →
        (1 / T') • (∫ t in (0:ℝ)..T', h t) - (1/T) • I =
        (((k T':ℝ)/T' - 1/T)) • I + (1/T') • (∫ t in ((k T':ℝ)*T)..T', h t) := by
      intro T' hT'
      have hzsmul : ((k T' : ℤ) • I) = ((k T':ℝ)) • I :=
        (Int.cast_smul_eq_zsmul ℝ (k T') I).symm
      rw [hdecomp T', hzsmul, smul_add, smul_smul]
      have hcoef : (1/T') * ((k T':ℝ)) = (k T':ℝ)/T' := by ring
      rw [hcoef]; module
    have hinv : Tendsto (fun T' : ℝ => 1/T') atTop (𝓝 0) := by
      simp only [one_div]; exact tendsto_inv_atTop_zero
    have htR : Tendsto (fun T' : ℝ => (1/T') • (∫ t in ((k T':ℝ)*T)..T', h t))
        atTop (𝓝 0) := by
      have hg : Tendsto (fun T' : ℝ => (1/T') * (C*T)) atTop (𝓝 0) := by
        have := hinv.mul_const (C*T); simpa using this
      refine squeeze_zero_norm' ?_ hg
      filter_upwards [eventually_gt_atTop 0] with T' hT'
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1/T')]
      exact mul_le_mul_of_nonneg_left (hRbound T' hT') (by positivity)
    have htI : Tendsto (fun T' : ℝ => (((k T':ℝ)/T' - 1/T)) • I) atTop (𝓝 0) := by
      have hcoef : Tendsto (fun T' : ℝ => ((k T':ℝ)/T')) atTop (𝓝 (1/T)) := by
        have hlb : ∀ᶠ T' in atTop, 1/T - 1/T' ≤ (k T':ℝ)/T' := by
          filter_upwards [eventually_gt_atTop 0] with T' hT'
          have hlt := Int.lt_floor_add_one (T'/T)
          have hk1 : (T'/T) - 1 ≤ (k T':ℝ) := by rw [hkdef]; linarith
          rw [div_sub_div _ _ (ne_of_gt hT) (ne_of_gt hT'), div_le_div_iff₀ (by positivity) hT']
          have hkT : ((T'/T) - 1) * T ≤ (k T':ℝ) * T := by nlinarith
          have e1 : ((T'/T) - 1) * T = T' - T := by field_simp
          nlinarith [hkT, e1, hT, hT', mul_pos hT hT']
        have hub : ∀ᶠ T' in atTop, (k T':ℝ)/T' ≤ 1/T := by
          filter_upwards [eventually_gt_atTop 0] with T' hT'
          have h0 : (k T':ℝ) ≤ T'/T := by rw [hkdef]; exact Int.floor_le (T'/T)
          rw [div_le_div_iff₀ hT' hT]
          have : (k T':ℝ) * T ≤ (T'/T) * T := by nlinarith
          calc (k T':ℝ) * T ≤ (T'/T)*T := this
            _ = T' := by field_simp
            _ = 1 * T' := by ring
        have hlow : Tendsto (fun T' : ℝ => 1/T - 1/T') atTop (𝓝 (1/T)) := by
          have := hinv.const_sub (1/T); simpa using this
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds hlb hub
      have hsub : Tendsto (fun T' : ℝ => ((k T':ℝ)/T' - 1/T)) atTop (𝓝 0) := by
        have := hcoef.sub_const (1/T); simpa using this
      simpa using hsub.smul_const I
    have hsum := (htI.add htR)
    rw [add_zero] at hsum
    refine (hsum.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with T' hT'
    exact (hrw T' hT').symm
  have := key.add (tendsto_const_nhds (x := (1/T) • I))
  simpa using this
