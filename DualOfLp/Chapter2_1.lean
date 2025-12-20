/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import Mathlib

theorem nonzero_functional_of_banach (E : Type*) {v : E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hv : v ≠ 0) : ∃ φ : StrongDual ℝ E, φ v ≠ 0 := by
  exact SeparatingDual.exists_ne_zero hv


theorem separating_dual_of_banach (E : Type*) {v w : E} (hvw : v ≠ w) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] : ∃ φ : StrongDual ℝ E, φ v ≠ φ w :=
  SeparatingDual.exists_separating_of_ne hvw

/- ## Bonus Question
Do you understand why the assumption `(hv : v ≠ 0)` in `nonzero_functional_of_banach` is right
before the statement, whereas `(hvw : v ≠ w)` in `separating_dual_of_banach` is right after the
introduction of `v` and `w`?
-/
