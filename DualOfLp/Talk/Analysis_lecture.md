# Filters

## Definition

A filter `F` on a type `α` is set in `Set α` (*i. e.* a collection of sets in `α`) such that:
1. The largest set `⊤ = Set.univ` is in `F`;
2. If `s,t : Set α` and `s ⊆ t`, then `s ∈ F` implies that `t ∈ F` (they are "upwards closed")
3. `F` is stable by finite intersections.

More precisely, `Filter` is a structure:

```lean
structure Filter (α : Type*) : Type*
  | sets : Set (Set α)
  | univ_sets : univ ∈ self.sets
  | sets_of_superset : ∀ {x y : Set α}, x ∈ sets → x ⊆ y → y ∈ sets
  | inter_sets : ∀ {x y : Set α}, x ∈ sets → y ∈ sets → x ∩ y ∈ sets
```

+++ Some examples of filters
* Given a term `a : α`, the collection of all sets containing `a` is the **principal** filter (at `a`): this generalises to any set `S ⊆ α`, being the case `S = {a}`. It is denoted `𝓟 S`, typed `\MCP S`.

* The collection of all sets of natural integers (or real numbers, or rational numbers...) that are
  "large enough" or "small enough" are filters. They are called `atTop` and `atBot`, respectively.

* In a topological space `X`, the collection of all neighbourhoods (*i. e.* sets containing an open neighbourhood) of a subspace `S` is a filter, denoted `𝓝 S`; when `S={x}`, we write `𝓝 x`.

+++

## Why filters

Filters are (among other things) a very convenient way to talk about **convergence**.

Consider a function $f : ℝ → ℝ$ and $a,b ∈ ℝ$. To say that
$$
\lim_{x → a} f (x) = b
$$
means
$$
∀\; ε > 0, ∃\; δ > 0 \;\text{ such that }\; ‖x - a‖ < δ ⇒  ‖f(x) - b‖ < ε
$$
or, equivalently,
$$
∀\; ε > 0, ∃\; δ > 0 \;\text{ such that }\; f (a - δ, a + δ) ⊆ (b - ε, b + ε).
$$
or, equivalently, that
$$
∀\; U_b ∈ 𝓝\; b, ∃\; V_a ∈ 𝓝\; a \text{ such that }V_a ⊆ f⁻¹ U_b.
$$
Upwards-closeness of filters makes the explicit description of $V_a$ useless: to require $V_a ⊆ f^{-1}U_b$ is the same as

    ∀ U : Set ℝ, U ∈  𝓝 b → f⁻¹' U ∈ 𝓝 a



And the statement
$\displaystyle{\lim_{x → +∞} f(x)=b}$ simply becomes

    ∀ U : Set ℝ, U ∈  𝓝 b → f⁻¹' U ∈ (atTop : Filter ℝ)

+++ Is this translation really useful?

Let $f,g : ℝ → ℝ$ and $a,b,c ∈ ℝ$. One theorem is that
$$
\lim_{x → a}f (x)=b ⇒ \lim_{y → b}g(y)= c ⇒ \lim_{x → a}(g∘ f)(x)=c
$$
while
$$
\lim_{x → +∞}f (x)=b ⇒ \lim_{y → b}g(y)= c ⇒ \lim_{x → +∞}(g∘ f)(x)=c
$$
is *another* theorem, because $+∞ ∉ ℝ$. And
$$
\lim_{x → a^-}f (x)=-∞ ⇒ \lim_{y → -\infty}g(y)= c ⇒ \lim_{x → a^-}(g∘ f)(x)=c
$$
is a third one. There are (at least) **5^3=125** such theorems.
+++

+++ Filters as generalised sets

( *Recall*: elements of `𝓟 s` = all sets
containing `s`.)

* #### `𝓟 s` replaces `s`, more general filters are "generalised sets" of `α`.

1. The **order** relation: sets on `α` are
ordered by inclusion, so `S₁ ≤ S₂ ↔ S₁ ⊆ S₂ ↔ ∀ T, T ⊇ S₂ → T ⊇ S₁`. Hence:

        def le (F G : Filter α) : F ≤ G ↔ ∀ t ∈ G, t ∈ F := Iff.rfl

1. Image of a filter through a function `f : α → β`. This operation is called
`Filter.map`:

        theorem mem_map (t : Set β) (F : Filter α) : t ∈ F.map f ↔ f ⁻¹' t ∈ F := Iff.rfl

3. With all this, the statement $\displaystyle{\lim_{x → a}f(x)=L}$ becomes

       def Tendsto (f : α → β) (F : Filter α) (G : Filter β) :=
          (𝓝 a).map f ≤ (𝓝 L)
