import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Connected.PathConnected

/-
Any two Hausdorff topologies on a finite-dimensional real vector space that make it a topological
vector space are equal.
-/
theorem unique_topology_of_finiteDimensional
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (t1 t2 : TopologicalSpace E)
    (h1 : @IsTopologicalAddGroup E t1 _)
    (h2 : @ContinuousSMul ℝ E _ _ t1)
    (h3 : @T2Space E t1)
    (h4 : @IsTopologicalAddGroup E t2 _)
    (h5 : @ContinuousSMul ℝ E _ _ t2)
    (h6 : @T2Space E t2) :
    t1 = t2 := by
  apply le_antisymm;
  · refine' continuous_def.mp _
    convert LinearMap.continuous_of_finiteDimensional _
    rotate_left
    exact ℝ
    all_goals try infer_instance
    exacts [ LinearMap.id, rfl ]
  · apply_rules [ continuous_def.mp ]
    convert LinearMap.continuous_of_finiteDimensional ( LinearMap.id )
    all_goals try assumption
    infer_instance

/-
The only topological vector space over `ℝ` with the discrete topology is the zero space
-/
theorem discrete_topology_implies_subsingleton {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DiscreteTopology E] :
    Subsingleton E := by
/- Let's take any element `x : E` and consider the map `f : ℝ → E` defined by
  `f(c) = c • x` -/
  have h_cont : ∀ x : E, Continuous (fun c : ℝ ↦ c • x) := by
    continuity;
  have h_const : ∀ x : E, ∀ c : ℝ, c • x = 0 • x := by
    have h_connected : ∀ x : E, IsConnected (Set.range (fun c : ℝ => c • x)) := by
      exact fun x => isConnected_range ( h_cont x )
    intro x c
    specialize h_connected x
    have := h_connected.isPreconnected.subsingleton (Set.mem_range_self 0) (Set.mem_range_self c)
    exact_mod_cast this.symm
  refine' ⟨ fun x y => _ ⟩
  have := h_const x 1; have := h_const y 1
  simp_all
