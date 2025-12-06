-- module

import Mathlib

noncomputable section

section Filter

open Filter Topology
variable {α β γ : Type*}

lemma mono' {f : α → β} {F G : Filter α} (h : F ≤ G) : F.map f ≤ G.map f := by
  -- simp +contextual [Filter.le_def] at h ⊢
  -- -- simp only [Filter.le_def, Filter.map, ← Filter.mem_sets, Set.mem_preimage]
  -- filter_upwards
  -- intro U hU
  exact fun _ H ↦ h H
  -- exact hU

def MyTendsto (f : α → β) (F : Filter α) (G : Filter β) := F.map f ≤ G

/- Scrivendo fare l' errore `MyTendsto (g ∘ f) G H` per mostrare che lean e' sveglio-/
lemma myTendsto_comp {f : α → β} {g : β → γ} {F : Filter α} {G : Filter β} {H : Filter γ}
    (hf : MyTendsto f F G) (hg : MyTendsto g G H) : MyTendsto (g ∘ f) F H :=
  (map_mono hf).trans hg

example (f g : ℝ → ℝ) (hf : MyTendsto f (𝓝 0) (𝓝 Real.pi))
    (hg : MyTendsto g (𝓝 Real.pi) atTop) : MyTendsto (g ∘ f) (𝓝 0) atTop := by
  apply myTendsto_comp hf hg

example (a : ℕ → ℝ) (φ : ℝ → ℂ) (ha : MyTendsto a atTop (𝓝 (-1)))
    (hφ : MyTendsto φ (𝓝 (-1)) (𝓝 (Complex.I))) : MyTendsto (φ ∘ a) atTop (𝓝 (Complex.I)) := by
  apply myTendsto_comp ha hφ

/-
`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intro a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.
-/

-- example (ε : Fin 4 → {x : ℝ | 0 < x}) :
--     ⋂ (i : Fin 4), (Set.Ioo (- (ε i).1) (ε (i+1))) ∈ 𝓝 (0) := by
--   have : Set.Ioo (- (⨅ (i : Fin 4), (ε i).1)) (⨆ (i : Fin 4), (ε i)) ∈ 𝓝 (0) := sorry
--   filter_upwards [this] with x hx
--   simp only [Set.mem_Ioo, Fin.isValue, Set.mem_iInter] at ⊢ hx
--   intro i
--   constructor
--   · replace hx := hx.1
--     apply lt_trans _ hx
--     rw [neg_lt, neg_neg]



-- example : MyTendsto (fun n : ℤ ↦ - n^2 + n - 3) atTop atBot := by
--   -- have : {b | b ≤ 100} ∈ atTop.map (fun n : ℤ ↦ - n^2 + n - 3) := sorry
--   -- let S : Set ℕ := {n | n ≤ 100 }
--   -- have hS : S ∈ atTop := sorry
--   simp only [MyTendsto, Filter.le_def]
--   intro T hT
--   filter_upwards-- [this]
  -- intro S
  -- filter_upwards [Filter.map_mem, eventually_gt_atTop 100]

end Filter

section Lp

open ENNReal MeasureTheory

variable (ι V : Type*) (E : ι → Type*) (p : ℝ≥0∞)
variable [(i : ι) → NormedAddCommGroup (E i)] [MeasurableSpace V] (μ : Measure V)

#check PreLp (α := ι) E
#check PiLp p E

#check @Lp V ℝ _ _ p (μ)
#check Lp ℝ p μ

example : PiLp p E = ((i : ι) → E i) := rfl
example : PreLp (α := ι) E = ((i : ι) → E i) := rfl

open ENNReal NNReal

def μL : Measure ℝ := (by volume_tac)

open Set in
def μD : OuterMeasure ℝ where
  measureOf := fun S ↦ S.indicator (fun _ ↦ (1 : ℝ≥0∞)) Real.pi
  empty := by simp
  mono {S T} hST := by
    apply Set.indicator_le_indicator_of_subset hST (by simp only [zero_le])
  iUnion_nat s _ := by
    calc
    indicator (⋃ n, s n) 1 Real.pi = ⨆ n, indicator (s n) 1 Real.pi :=
      indicator_iUnion_apply (M := ℝ≥0∞) rfl _ _ _
    _ ≤ ∑' n, indicator (s n) 1 Real.pi := iSup_le fun _ ↦ ENNReal.le_tsum _

-- abbrev LebesgueFilter := ae μL
def DiracFilter := ae μD

example : {x : ℝ | x < 0} =ᵐ[μD] (∅ : Set ℝ) := by
  rw [μD, ae_eq_empty, ← OuterMeasure.measureOf_eq_coe]
  simp only [Set.indicator_apply_eq_zero, Set.mem_setOf_eq, one_ne_zero,
    imp_false, not_lt]
  positivity

example (f g h : ℝ → ℝ) (h1 : f =ᵐ[μL] g) (h2 : g =ᵐ[μL] h) : f =ᵐ[μL] h := by
-- We need to prove that `∀ᶠ x, f x = h x`, namely `{x | f x = h x} ∈ ae (μL)`, namely
-- `μL {x | f x ≠ h x} = 0`.
  have := @Filter.inter_mem (f := ae μL) (s := {x | f x = g x}) (t := {x | g x = h x})
  have h1 : {x | f x = h x} ∈ ae μL := by
    convert_to {x | f x = g x ∧ g x = h x} ∈ ae μL
    sorry
    sorry
  filter_upwards [h1] with a ha using ha
  -- have h2 : ∀ᶠ x in ae μL, f x = h x := by exact h1
  -- exact h1
  -- filter_upwards [this]
