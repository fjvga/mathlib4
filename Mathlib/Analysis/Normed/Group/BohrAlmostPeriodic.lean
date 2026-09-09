/-
Copyright (c) 2026 Francisco Ramírez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Ramírez
-/

module
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Bohr almost-periodic functions (definition + elementary closure properties)

A function `f : ℝ → X` (into a normed additive group) is *almost periodic* in
the sense of Bohr if, for every `ε > 0`, there exists `L > 0` such that every
interval `[a, a + L]` contains an `ε`-almost-period `τ` (i.e.
`∀ t, ‖f (t + τ) - f t‖ < ε`).

Mathlib does not yet have a theory of Bohr almost-periodicity. This file
provides the definition and the closure properties provable without the
relative-density intersection theorem (companion PR).

## Main results

* `IsAlmostPeriodic`: the definition.
* `isAlmostPeriodic_const`: constant functions are almost periodic.
* `IsAlmostPeriodic.neg`: closed under negation.
* `IsAlmostPeriodic.const_mul`: closed under real scalar multiplication.
* `Function.Periodic.isAlmostPeriodic`: periodic ⇒ almost periodic.
* `IsAlmostPeriodic.bounded_of_continuous`: AP + continuous ⇒ uniformly bounded.
* `isAlmostPeriodic_tendstoUniformly`: closed under uniform limits.

## Tags

almost periodic, Bohr, periodic, almost period
-/

@[expose] public section

open Set

/-- A function `f : ℝ → X` is *almost periodic* (Bohr) if for every `ε > 0`
there exists `L > 0` such that every interval `[a, a + L]` of length `L`
contains an `ε`-almost-period `τ`: `∀ t, ‖f (t + τ) - f t‖ < ε`. -/
def IsAlmostPeriodic {X : Type*} [NormedAddCommGroup X] (f : ℝ → X) : Prop :=
  ∀ ε > 0, ∃ L > 0, ∀ a : ℝ, ∃ τ ∈ Set.Icc a (a + L), ∀ t, ‖f (t + τ) - f t‖ < ε

/-! ### Elementary closures -/

/-- Constant functions are almost periodic. -/
theorem isAlmostPeriodic_const {X : Type*} [NormedAddCommGroup X] (c : X) :
    IsAlmostPeriodic (fun _ => c) := by
  intro ε hε
  refine ⟨1, one_pos, fun a => ?_⟩
  refine ⟨a, ⟨le_refl a, by linarith⟩, fun t => ?_⟩
  rw [sub_self, norm_zero]; exact hε

/-- Almost-periodic functions are closed under negation. -/
theorem IsAlmostPeriodic.neg {X : Type*} [NormedAddCommGroup X] {f : ℝ → X}
    (hf : IsAlmostPeriodic f) : IsAlmostPeriodic (fun t => -f t) := by
  intro ε hε
  obtain ⟨L, hL, h⟩ := hf ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτ, hτt⟩ := h a
  refine ⟨τ, hτ, fun t => ?_⟩
  have heq : (fun t => -f t) (t + τ) - (fun t => -f t) t = -(f (t + τ) - f t) := by
    simp only []
    abel
  rw [heq, norm_neg]
  exact hτt t

/-- Almost-periodic functions are closed under real scalar multiplication. -/
theorem IsAlmostPeriodic.const_mul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : ℝ → X} (hf : IsAlmostPeriodic f) (c : ℝ) :
    IsAlmostPeriodic (fun t => c • f t) := by
  intro ε hε
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc]
    simp only [zero_smul]
    exact isAlmostPeriodic_const (0 : X) ε hε
  · have habs : 0 < |c| := abs_pos.mpr hc
    obtain ⟨L, hL, h⟩ := hf (ε / |c|) (by positivity)
    refine ⟨L, hL, fun a => ?_⟩
    obtain ⟨τ, hτ, hτt⟩ := h a
    refine ⟨τ, hτ, fun t => ?_⟩
    have hnorm : ‖c • f (t + τ) - c • f t‖ = |c| * ‖f (t + τ) - f t‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    rw [hnorm]
    calc |c| * ‖f (t + τ) - f t‖ < |c| * (ε / |c|) :=
          mul_lt_mul_of_pos_left (hτt t) habs
      _ = ε := mul_div_cancel₀ ε (ne_of_gt habs)

/-- A periodic function is almost periodic. -/
theorem Function.Periodic.isAlmostPeriodic {X : Type*} [NormedAddCommGroup X]
    {f : ℝ → X} {T : ℝ} (hT : 0 < T) (hf : Function.Periodic f T) :
    IsAlmostPeriodic f := by
  intro ε hε
  refine ⟨T, hT, fun a => ?_⟩
  have hge : a ≤ ((⌊a / T⌋ + 1 : ℤ) : ℝ) * T := by
    have h1 := Int.lt_floor_add_one (a / T)
    have h2 : a = (a / T) * T := by field_simp
    push_cast; nlinarith [h1, hT, h2]
  have hle : ((⌊a / T⌋ + 1 : ℤ) : ℝ) * T ≤ a + T := by
    have h1 := Int.floor_le (a / T)
    have hcast : ((⌊a / T⌋ + 1 : ℤ) : ℝ) = ((⌊a / T⌋ : ℤ) : ℝ) + 1 := by norm_num
    have h2 : a = (a / T) * T := by field_simp
    rw [hcast]; nlinarith [h1, hT, h2]
  refine ⟨((⌊a / T⌋ + 1 : ℤ) : ℝ) * T, ⟨hge, hle⟩, fun t => ?_⟩
  have hperiod := hf.int_mul (⌊a / T⌋ + 1)
  have heq : f (t + ((⌊a / T⌋ + 1 : ℤ) : ℝ) * T) = f t := hperiod t
  rw [heq, sub_self, norm_zero]; exact hε

/-! ### Boundedness -/

/-- An almost-periodic continuous function is uniformly bounded.
    REF: Corduneanu 2009, Thm 6.3. -/
theorem IsAlmostPeriodic.bounded_of_continuous {X : Type*} [NormedAddCommGroup X]
    {f : ℝ → X} (hf : IsAlmostPeriodic f) (hcont : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M := by
  obtain ⟨L, hLpos, hL⟩ := hf 1 one_pos
  have hcont' : Continuous fun t : ℝ => ‖f t‖ := continuous_norm.comp hcont
  have hcompact : IsCompact (Set.Icc 0 L) := isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) L).Nonempty := Set.nonempty_Icc.mpr (le_of_lt hLpos)
  obtain ⟨t0, ht0⟩ := hcompact.exists_isMaxOn hne hcont'.continuousOn
  obtain ⟨ht0mem, ht0max⟩ := ht0
  rw [isMaxOn_iff] at ht0max
  refine ⟨‖f t0‖ + 1, by linarith [norm_nonneg (f t0)], ?_⟩
  intro t
  obtain ⟨τ, hτ_Icc, hτ⟩ := hL (-t)
  have htp_mem : t + τ ∈ Set.Icc (0:ℝ) L :=
    ⟨by linarith [hτ_Icc.1], by linarith [hτ_Icc.2]⟩
  have h_max : ‖f (t + τ)‖ ≤ ‖f t0‖ := ht0max _ htp_mem
  have h_ap : ‖f (t + τ) - f t‖ < 1 := hτ t
  have h_tri : ‖f t‖ ≤ ‖f (t + τ)‖ + 1 := by
    have hsub : ‖f t - f (t + τ)‖ < 1 := by rw [norm_sub_rev]; exact h_ap
    have hcalc : ‖f t‖ ≤ ‖f t - f (t + τ)‖ + ‖f (t + τ)‖ := by
      have h := norm_add_le (f t - f (t + τ)) (f (t + τ))
      rwa [sub_add_cancel] at h
    linarith
  linarith

/-! ### Uniform limit closure -/

/-- Almost-periodicity is closed under uniform limits: if `F n → f` uniformly
    and each `F n` is almost-periodic, then `f` is almost-periodic.
    Standard `ε/3` argument. -/
theorem isAlmostPeriodic_tendstoUniformly {X : Type*} [NormedAddCommGroup X]
    {f : ℝ → X} {F : ℕ → ℝ → X}
    (hF : ∀ n, IsAlmostPeriodic (F n))
    (hlim : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t, ‖F n t - f t‖ < ε) :
    IsAlmostPeriodic f := by
  intro ε hε
  have hε3 : (0:ℝ) < ε / 3 := by linarith
  obtain ⟨N, hN⟩ := hlim (ε / 3) hε3
  obtain ⟨L, hLpos, hL⟩ := hF N (ε / 3) hε3
  refine ⟨L, hLpos, fun a => ?_⟩
  obtain ⟨τ, hτ, hτt⟩ := hL a
  refine ⟨τ, hτ, fun t => ?_⟩
  have h1 : ‖F N (t + τ) - f (t + τ)‖ < ε / 3 := hN N (le_refl N) (t + τ)
  have h2 : ‖F N (t + τ) - F N t‖ < ε / 3 := hτt t
  have h3 : ‖F N t - f t‖ < ε / 3 := hN N (le_refl N) t
  have hsplit : f (t + τ) - f t =
      (f (t + τ) - F N (t + τ)) + (F N (t + τ) - F N t) + (F N t - f t) := by abel
  rw [hsplit]
  have h_n3 : ∀ a b c : X, ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    intro a b c
    calc ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_add_le a b]
  calc ‖(f (t + τ) - F N (t + τ)) + (F N (t + τ) - F N t) + (F N t - f t)‖
      ≤ ‖f (t + τ) - F N (t + τ)‖ + ‖F N (t + τ) - F N t‖ + ‖F N t - f t‖ :=
        h_n3 _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [norm_sub_rev]; linarith
    _ = ε := by ring
