/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-- A  topological vector space is Bolognese if for every open `U` around a point there is a convex
open set `C` containing that point such that `C ⊆ U`. -/
def Bolognese (E : Type*) [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] : Prop :=
  ∀ (U : Set E) (x : E), IsOpen U → x ∈ U → ∃ C, IsOpen C ∧ Convex ℝ C ∧ x ∈ C ∧ C ⊆ U

open Pointwise Filter Set MeasureTheory ENNReal

theorem bolognese_iff_lc (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] : Bolognese E ↔ LocallyConvexSpace ℝ E := by
  refine ⟨fun h ↦ ?_ ,fun h ↦ ?_⟩
  · rw [locallyConvexSpace_iff]
    intro x
    rw [hasBasis_iff]
    intro T
    refine ⟨fun hT ↦ ?_, fun hT ↦ ?_⟩
    · obtain ⟨U, U_sub, hU, U_mem⟩ := mem_nhds_iff.mp hT
      obtain ⟨C, hC1, hC2, C_mem, C_sub⟩ := h U x hU U_mem
      exact ⟨C, ⟨hC1.mem_nhds C_mem, hC2⟩, C_sub.trans U_sub⟩
    · obtain ⟨_, ⟨mem_U, -⟩, sub⟩ := hT
      filter_upwards [mem_U] with a ha using sub ha
  · intro U x hU hx
    set U₀ := U - {x} with hU₀_def
    have U₀_mem : 0 ∈ U₀ := by
      rw [hU₀_def, sub_singleton, mem_image]
      refine ⟨x, hx, sub_self _⟩
    obtain ⟨C₀, ⟨hC₀_mem, hC₀_open, hC₀_AC⟩, C₀_id⟩ :=
      (hasBasis_iff.mp (nhds_hasBasis_absConvex_open ℝ E) U₀).mp (hU.sub_right.mem_nhds U₀_mem)
    use {x} + C₀
    refine ⟨hC₀_open.add_left, Convex.add (convex_singleton x) hC₀_AC.2, by simpa, ?_⟩
    · simp only [id_eq] at C₀_id
      grw [C₀_id, hU₀_def]
      intro a ha
      simp only [sub_singleton, singleton_add, image_add_left, mem_preimage,
        mem_image] at ha
      obtain ⟨y, hy, hya⟩ := ha
      replace hya : y - x + x = a := by
        simp_all only [sub_singleton, mem_image, neg_add_cancel_comm]
      rwa [← hya, sub_add, sub_self, sub_zero]

theorem bolognese_of_banach (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Bolognese E := by
  rw [bolognese_iff_lc E]
  infer_instance

/-- The restriction of the Lebesgue measure on `ℝ` to `[0,1]`: it is actually the
pull-back (and coincides, on `[0,1]` with the restriction). -/
noncomputable def ν : Measure (Icc (0 : ℝ) 1) :=
  Measure.comap ((↑) : (Icc (0 : ℝ) 1) → ℝ) (by volume_tac)

theorem Lp_bolognese (p : ℝ≥0∞) [Fact (1 ≤ p)] : Bolognese (Lp ℝ p ν) := bolognese_of_banach _

theorem separates_dual_of_bolognese (E : Type*) {v w : E} (hvw : v ≠ w) [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T1Space E] (hE : Bolognese E) : ∃ φ : StrongDual ℝ E, φ v ≠ φ w := by
  rw [bolognese_iff_lc] at hE
  exact SeparatingDual.exists_separating_of_ne hvw
