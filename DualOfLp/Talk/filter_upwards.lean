-- module

import Mathlib

example : 2 = 2 := rfl

open /- Filter -/ Topology
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
lemma myTendsto_comp {F : Filter α} {G : Filter β} {H : Filter γ}
    (hf : MyTendsto f F G) (hg : MyTendsto g G H) : MyTendsto (g ∘ f) F H :=
  (map_mono hf).trans hg

example (f g : ℝ → ℝ) (hf : MyTendsto f (𝓝 0) (𝓝 Real.pi))
    (hg : MyTendsto g (𝓝 Real.pi) atTop) : MyTendsto (g ∘ f) (𝓝 0) atTop := by
  apply myTendsto_comp hf hg

example (a : ℕ → ℝ) (φ : ℝ → ℂ) (ha : MyTendsto a atTop (𝓝 (-1)))
    (hφ : MyTendsto φ (𝓝 (-1)) (𝓝 (Complex.I))) : MyTendsto (φ ∘ a) atTop (𝓝 (Complex.I)) := by
  apply myTendsto_comp ha hφ

/--
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

example (ε : Fin 4 → {x : ℝ | 0 < x}) :
    ⋂ (i : Fin 4), (Set.Ioo (- (ε i).1) (ε (i+1))) ∈ 𝓝 (0) := by
  have : Set.Ioo (- (⨅ (i : Fin 4), (ε i).1)) (⨆ (i : Fin 4), (ε i)) ∈ 𝓝 (0) := sorry
  filter_upwards [this] with x hx
  simp only [Set.mem_Ioo, Fin.isValue, Set.mem_iInter] at ⊢ hx
  intro i
  constructor
  · replace hx := hx.1
    apply lt_trans _ hx
    rw [neg_lt, neg_neg]



-- example : MyTendsto (fun n : ℤ ↦ - n^2 + n - 3) atTop atBot := by
--   -- have : {b | b ≤ 100} ∈ atTop.map (fun n : ℤ ↦ - n^2 + n - 3) := sorry
--   -- let S : Set ℕ := {n | n ≤ 100 }
--   -- have hS : S ∈ atTop := sorry
--   simp only [MyTendsto, Filter.le_def]
--   intro T hT
--   filter_upwards-- [this]
  -- intro S
  -- filter_upwards [Filter.map_mem, eventually_gt_atTop 100]
