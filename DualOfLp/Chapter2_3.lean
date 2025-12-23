/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Aristotle by Harmonic
-/

import Mathlib
import DualOfLp.Chapter2_2

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

/-
Distance on $\ell^p$ for $0 < p < 1$.
-/
open scoped ENNReal

noncomputable def lp_dist {ι : Type*} (p : ℝ≥0∞) (f g : ↥(lp (fun _ : ι => ℝ) p)) : ℝ :=
  ∑' i, ‖(f : ∀ j, ℝ) i - (g : ∀ j, ℝ) i‖ ^ p.toReal

/-
For $0 < p < 1$, $\ell^p$ is a metric space.
-/
open scoped ENNReal

noncomputable instance lp.instDist_of_lt_one {ι : Type*} (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] : Dist (lp (fun _ : ι => ℝ) p) :=
  ⟨fun f g => ∑' i, ‖f i - g i‖ ^ p.toReal⟩

noncomputable instance lp.instMetricSpace_of_lt_one {ι : Type*} (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] : MetricSpace (lp (fun _ : ι => ℝ) p) :=
{ dist := Dist.dist
  dist_self := by
    -- By definition of distance, we have dist x x = ∑' i, ‖(x : ∀ j, ℝ) i - (x : ∀ j, ℝ) i‖ ^ p.toReal.
    simp [dist];
    cases p using ENNReal.recTopCoe <;> aesop;
    · -- Since ι is empty, its cardinality is zero.
      exfalso; exact False.elim (Fact.out : False);
    · exact Or.inr ( Real.zero_rpow ( by simpa using inst.1.ne' ) )
  dist_comm := by
    -- Since the absolute value function is symmetric, we have |x_i - y_i| = |y_i - x_i| for all i.
    have h_abs_symm : ∀ x y : ↥(lp (fun _ : ι => ℝ) p), ∀ i, ‖(x : ∀ j, ℝ) i - (y : ∀ j, ℝ) i‖ = ‖(y : ∀ j, ℝ) i - (x : ∀ j, ℝ) i‖ := by
      exact fun x y i => norm_sub_rev _ _;
    -- Since the sum of symmetric terms is symmetric, we can conclude that the distance function is symmetric.
    intros x y
    simp [dist, h_abs_symm]
  dist_triangle := by
    -- By the subadditivity of |a|^p for 0 < p < 1, we have |x_i - z_i|^p ≤ |x_i - y_i|^p + |y_i - z_i|^p for each i.
    have h_subadd : ∀ (x y z : ι → ℝ), ∀ i, ‖x i - z i‖ ^ p.toReal ≤ ‖x i - y i‖ ^ p.toReal + ‖y i - z i‖ ^ p.toReal := by
      -- By the subadditivity of $t^p$ for $0 < p < 1$, we have $(a + b)^p \leq a^p + b^p$ for non-negative $a$ and $b$.
      have h_subadd : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → (a + b) ^ p.toReal ≤ a ^ p.toReal + b ^ p.toReal := by
        intro a b ha hb; rcases eq_or_lt_of_le ha with ( rfl | ha ) <;> rcases eq_or_lt_of_le hb with ( rfl | hb ) <;> norm_num;
        · positivity;
        · positivity;
        · positivity;
        · -- By dividing both sides by $(a + b)^p$, we get $1 \leq \left(\frac{a}{a + b}\right)^p + \left(\frac{b}{a + b}\right)^p$.
          suffices h_div : 1 ≤ (a / (a + b)) ^ p.toReal + (b / (a + b)) ^ p.toReal by
            rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.div_rpow ( by positivity ) ( by positivity ) ] at h_div;
            rwa [ ← add_div, one_le_div ( by positivity ) ] at h_div;
          exact le_trans ( by norm_num [ ← add_div, div_self ( ne_of_gt ( add_pos ha hb ) ) ] ) ( add_le_add ( Real.rpow_le_rpow_of_exponent_ge ( by positivity ) ( div_le_one_of_le₀ ( by linarith ) ( by positivity ) ) ( show p.toReal ≤ 1 by simpa using ENNReal.toReal_mono ( by aesop ) ( show p ≤ 1 by exact le_of_lt ( Fact.out ) ) ) ) ( Real.rpow_le_rpow_of_exponent_ge ( by positivity ) ( div_le_one_of_le₀ ( by linarith ) ( by positivity ) ) ( show p.toReal ≤ 1 by simpa using ENNReal.toReal_mono ( by aesop ) ( show p ≤ 1 by exact le_of_lt ( Fact.out ) ) ) ) );
      exact fun x y z i => le_trans ( Real.rpow_le_rpow ( norm_nonneg _ ) ( by simpa using norm_add_le ( x i - y i ) ( y i - z i ) ) ( by positivity ) ) ( h_subadd _ _ ( norm_nonneg _ ) ( norm_nonneg _ ) );
    intro ⟨ x, hx ⟩ ⟨ y, hy ⟩ ⟨ z, hz ⟩;
    -- Apply the subadditivity of |a|^p for 0 < p < 1 to each term in the sum.
    have h_sum_subadd : ∑' i, ‖x i - z i‖ ^ p.toReal ≤ ∑' i, ‖x i - y i‖ ^ p.toReal + ∑' i, ‖y i - z i‖ ^ p.toReal := by
      rw [ ← Summable.tsum_add ];
      · refine' Summable.tsum_le_tsum _ _ _;
        · exact fun i => h_subadd x y z i;
        · have h_summable : Summable (fun i => ‖x i‖ ^ p.toReal + ‖z i‖ ^ p.toReal) := by
            have h_summable_x : Summable (fun i => ‖x i‖ ^ p.toReal) := by
              convert hx.summable;
              aesop;
              exact Or.inl ( ENNReal.toReal_pos ( ne_of_gt ( Fact.out : 0 < p ) ) ( ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) ) ) )
            have h_summable_z : Summable (fun i => ‖z i‖ ^ p.toReal) := by
              convert hz.summable using 1;
              cases p using ENNReal.recTopCoe <;> aesop;
              exact Or.inl Fact.out
            exact Summable.add h_summable_x h_summable_z;
          refine' h_summable.of_nonneg_of_le ( fun i => by positivity ) ( fun i => _ );
          refine' le_trans ( h_subadd x 0 z i ) _ ; simp +decide [ zero_sub ];
        · refine' Summable.add _ _;
          · have := hx.sub hy;
            rcases p with ( _ | _ | p ) <;> simp_all +decide [ Memℓp ];
            aesop;
            exact False.elim <| Fact.out;
          · have h_summable : Summable (fun i => ‖y i‖ ^ p.toReal) ∧ Summable (fun i => ‖z i‖ ^ p.toReal) := by
              cases p using ENNReal.recTopCoe <;> aesop;
              · exact False.elim <| Fact.out;
              · convert hy.summable using 1;
                aesop;
                exact Or.inl Fact.out;
              · convert hz.summable using 1;
                aesop;
                exact Or.inl Fact.out;
            -- Apply the subadditivity of |a|^p for 0 < p < 1 to each term in the sum to get ‖y i - z i‖ ^ p.toReal ≤ ‖y i‖ ^ p.toReal + ‖z i‖ ^ p.toReal.
            have h_subadd : ∀ i, ‖y i - z i‖ ^ p.toReal ≤ ‖y i‖ ^ p.toReal + ‖z i‖ ^ p.toReal := by
              intro i; specialize h_subadd y 0 z i; aesop;
            exact Summable.of_nonneg_of_le ( fun i => Real.rpow_nonneg ( norm_nonneg _ ) _ ) h_subadd ( h_summable.1.add h_summable.2 );
      · have := hx.sub hy;
        rcases p with ( _ | _ | p ) <;> simp_all +decide [ Memℓp ];
        split_ifs at this <;> simp_all +decide [ ne_of_gt ];
      · have h_summable : Summable (fun i => ‖y i‖ ^ p.toReal) ∧ Summable (fun i => ‖z i‖ ^ p.toReal) := by
          cases p using ENNReal.recTopCoe <;> aesop;
          · exact False.elim <| Fact.out;
          · convert hy.summable using 1;
            aesop;
            exact Or.inl Fact.out;
          · convert hz.summable using 1;
            aesop;
            exact Or.inl Fact.out;
        have h_summable : ∀ i, ‖y i - z i‖ ^ p.toReal ≤ ‖y i‖ ^ p.toReal + ‖z i‖ ^ p.toReal := by
          intro i; specialize h_subadd y 0 z i; aesop;
        exact Summable.of_nonneg_of_le ( fun i => Real.rpow_nonneg ( norm_nonneg _ ) _ ) h_summable ( Summable.add ( by tauto ) ( by tauto ) );
    exact?
  edist_dist := by
    all_goals generalize_proofs at *;
    exact?
  eq_of_dist_eq_zero := by
    -- If the distance between two elements is zero, then each term in the sum must be zero.
    have h_zero_terms : ∀ {x y : ↥(lp (fun _ : ι => ℝ) p)}, (∑' i, ‖(x : ∀ j, ℝ) i - (y : ∀ j, ℝ) i‖ ^ p.toReal) = 0 → ∀ i, ‖(x : ∀ j, ℝ) i - (y : ∀ j, ℝ) i‖ = 0 := by
      aesop;
      contrapose! a;
      refine' ne_of_gt ( lt_of_lt_of_le _ ( Summable.le_tsum _ i ( fun i _ => by positivity ) ) );
      · exact Real.rpow_pos_of_pos ( abs_pos.mpr a ) _;
      · convert property.sub property_1 |> fun h => h.summable using 1;
        simp +decide [ ENNReal.toReal_pos_iff, Fact.out ];
        exact Or.inl ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) );
    -- If the distance between two elements is zero, then each term in the sum must be zero, implying that the elements are equal.
    intros x y h_dist_zero
    have h_eq : ∀ i, (x : ∀ j, ℝ) i = (y : ∀ j, ℝ) i := by
      exact fun i => sub_eq_zero.mp ( norm_eq_zero.mp ( h_zero_terms h_dist_zero i ) );
    exact Subtype.ext ( funext h_eq ) }

/-
$\ell^p$ is a topological add group for $0 < p < 1$.
-/
open scoped ENNReal

noncomputable instance lp.instTopologicalAddGroup_of_lt_one {ι : Type*} (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] : IsTopologicalAddGroup (lp (fun _ : ι => ℝ) p) :=
{ continuous_add := by
    rw [Metric.continuous_iff]
    intro p_prod ε hε
    -- By the triangle inequality, we have:
    have h_triangle : ∀ a : ↥(lp (fun _ : ι => ℝ) p) × ↥(lp (fun _ : ι => ℝ) p), Dist.dist (a.1 + a.2) (p_prod.1 + p_prod.2) ≤ Dist.dist a.1 p_prod.1 + Dist.dist a.2 p_prod.2 := by
      -- Apply the triangle inequality to each term in the sum.
      have h_triangle : ∀ a : ↥(lp (fun _ : ι => ℝ) p) × ↥(lp (fun _ : ι => ℝ) p), ∀ i, ‖(a.1 i + a.2 i) - (p_prod.1 i + p_prod.2 i)‖ ^ p.toReal ≤ ‖a.1 i - p_prod.1 i‖ ^ p.toReal + ‖a.2 i - p_prod.2 i‖ ^ p.toReal := by
        -- Apply the concavity of the function $t^p$ for $0 < p < 1$ to the norms.
        have h_concave : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y) ^ p.toReal ≤ x ^ p.toReal + y ^ p.toReal := by
          intro x y hx hy; rcases eq_or_lt_of_le hx with ( rfl | hx ) <;> rcases eq_or_lt_of_le hy with ( rfl | hy ) <;> norm_num;
          · positivity;
          · positivity;
          · positivity;
          · -- By dividing both sides by $(x + y)^p$, we get $1 \leq \left(\frac{x}{x + y}\right)^p + \left(\frac{y}{x + y}\right)^p$.
            suffices h_div : 1 ≤ (x / (x + y)) ^ p.toReal + (y / (x + y)) ^ p.toReal by
              rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.div_rpow ( by positivity ) ( by positivity ) ] at h_div;
              rwa [ ← add_div, one_le_div ( by positivity ) ] at h_div;
            -- Since $0 < p < 1$, we have $(x / (x + y))^p + (y / (x + y))^p \geq (x / (x + y)) + (y / (x + y)) = 1$.
            have h_ineq : (x / (x + y)) ^ p.toReal + (y / (x + y)) ^ p.toReal ≥ (x / (x + y)) + (y / (x + y)) := by
              exact add_le_add ( by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_ge ( by positivity ) ( div_le_one_of_le₀ ( by linarith ) ( by positivity ) ) ( show p.toReal ≤ 1 by exact ENNReal.toReal_mono ( by aesop ) ( show p ≤ 1 from le_of_lt ( Fact.out ) ) ) ) ) ( by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_ge ( by positivity ) ( div_le_one_of_le₀ ( by linarith ) ( by positivity ) ) ( show p.toReal ≤ 1 by exact ENNReal.toReal_mono ( by aesop ) ( show p ≤ 1 from le_of_lt ( Fact.out ) ) ) ) );
            rwa [ ← add_div, div_self ( ne_of_gt ( add_pos hx hy ) ) ] at h_ineq;
        intro a i;
        exact le_trans ( Real.rpow_le_rpow ( norm_nonneg _ ) ( by simpa only [ add_sub_add_comm ] using norm_add_le ( ( a.1 : ι → ℝ ) i - p_prod.1 i ) ( ( a.2 : ι → ℝ ) i - p_prod.2 i ) ) ( by exact ENNReal.toReal_nonneg ) ) ( h_concave _ _ ( norm_nonneg _ ) ( norm_nonneg _ ) );
      intro a;
      refine' le_trans ( Summable.tsum_le_tsum ( fun i => h_triangle a i ) _ _ ) _;
      · have h_summable : Summable (fun i => ‖(a.1 i - p_prod.1 i)‖ ^ p.toReal + ‖(a.2 i - p_prod.2 i)‖ ^ p.toReal) := by
          have h_summable : Summable (fun i => ‖(a.1 i - p_prod.1 i)‖ ^ p.toReal) ∧ Summable (fun i => ‖(a.2 i - p_prod.2 i)‖ ^ p.toReal) := by
            have h_summable : ∀ (f : ↥(lp (fun _ : ι => ℝ) p)), Summable (fun i => ‖f i‖ ^ p.toReal) := by
              intro f;
              have := f.2;
              convert this.summable;
              cases p using ENNReal.recTopCoe <;> aesop;
              · exact False.elim <| Fact.out;
              · exact Or.inl Fact.out;
            exact ⟨ by simpa using h_summable ( a.1 - p_prod.1 ), by simpa using h_summable ( a.2 - p_prod.2 ) ⟩;
          exact h_summable.1.add h_summable.2;
        refine' h_summable.of_nonneg_of_le ( fun i => Real.rpow_nonneg ( norm_nonneg _ ) _ ) ( fun i => h_triangle a i );
      · have h_summable : Summable (fun i => ‖a.1 i - p_prod.1 i‖ ^ p.toReal) ∧ Summable (fun i => ‖a.2 i - p_prod.2 i‖ ^ p.toReal) := by
          have h_summable : ∀ (f : ↥(lp (fun _ : ι => ℝ) p)), Summable (fun i => ‖f i‖ ^ p.toReal) := by
            intro f;
            have := f.2;
            convert this.summable;
            cases p using ENNReal.recTopCoe <;> aesop;
            · exact False.elim <| Fact.out;
            · exact Or.inl Fact.out;
          exact ⟨ by simpa using h_summable ( a.1 - p_prod.1 ), by simpa using h_summable ( a.2 - p_prod.2 ) ⟩;
        exact h_summable.1.add h_summable.2;
      · rw [ Summable.tsum_add ];
        · rfl;
        · have := a.1.2;
          have := this.sub ( p_prod.1.2 );
          rw [ Memℓp ] at this;
          split_ifs at this <;> simp_all +decide [ sub_eq_add_neg ];
        · have := a.2.2;
          have := this.sub ( p_prod.2.2 );
          rcases p with ( _ | _ | p ) <;> simp_all +decide [ Memℓp ];
          aesop;
          exact False.elim <| Fact.out;
    -- By choosing δ = ε / 2, we ensure that if the distance between a and p_prod is less than δ, then both a.1 and a.2 are within ε / 2 of p_prod.1 and p_prod.2 respectively.
    use ε / 2;
    simp_all +decide [ Prod.dist_eq ];
    exact fun a ha b hb ha' hb' => lt_of_le_of_lt ( h_triangle a ha b hb ) ( by linarith )
  continuous_neg := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine' ⟨ ε, hε, fun a ha => _ ⟩;
    convert ha using 1;
    simp +decide [ Dist.dist ];
    exact tsum_congr fun i => by rw [ neg_add_eq_sub, abs_sub_comm ] ; }

#check IsTopologicalAddGroup

#check Metric.continuous_iff

/-
$\ell^p$ has continuous scalar multiplication for $0 < p < 1$.
-/
open scoped ENNReal

noncomputable instance lp.instContinuousSMul_of_lt_one {ι : Type*} (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] : ContinuousSMul ℝ (lp (fun _ : ι => ℝ) p) :=
{ continuous_smul := by
    rw [Metric.continuous_iff]
    intro p_prod ε hε
    -- We need to show continuity of scalar multiplication.
    -- d(c'x', cx) <= |c'|^p d(x', x) + |c' - c|^p d(x, 0)
    -- This inequality holds for 0 < p < 1.
    -- To prove continuity, we use the fact that the distance function is continuous and the inequality $d(c'x', cx) \leq |c'|^p d(x', x) + |c' - c|^p d(x, 0)$.
    have h_cont : ∀ (c' c : ℝ) (x' x : ↥(lp (fun _ : ι => ℝ) p)), dist (c' • x') (c • x) ≤ |c'|^p.toReal * dist x' x + |c' - c|^p.toReal * dist x 0 := by
      -- Apply the inequality $|c'x' - cx| \leq |c'|^p |x' - x| + |c' - c|^p |x|$ to each term in the sum.
      have h_ineq : ∀ (c' c : ℝ) (x' x : ↥(lp (fun _ : ι => ℝ) p)) (i : ι), ‖(c' • x' : ∀ j, ℝ) i - (c • x : ∀ j, ℝ) i‖ ^ p.toReal ≤ |c'|^p.toReal * ‖x' i - x i‖ ^ p.toReal + |c' - c|^p.toReal * ‖x i‖ ^ p.toReal := by
        intro c' c x' x i
        have h_ineq : ‖(c' • x' : ∀ j, ℝ) i - (c • x : ∀ j, ℝ) i‖ ≤ |c'| * ‖x' i - x i‖ + |c' - c| * ‖x i‖ := by
          convert norm_add_le ( c' * ( x' i - x i ) ) ( ( c' - c ) * x i ) using 1 <;> norm_num ; ring;
        have h_ineq_pow : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) ^ p.toReal ≤ a ^ p.toReal + b ^ p.toReal := by
          intro a b ha hb;
          have h_ineq_pow : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) ^ p.toReal ≤ a ^ p.toReal + b ^ p.toReal := by
            intro a b ha hb
            have h_ineq_pow : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≠ 0 → b ≠ 0 → (a + b) ^ p.toReal ≤ a ^ p.toReal + b ^ p.toReal := by
              intro a b ha hb ha' hb'
              have h_ineq_pow : (a / (a + b)) ^ p.toReal + (b / (a + b)) ^ p.toReal ≥ 1 := by
                have h_ineq_pow : ∀ x : ℝ, 0 < x ∧ x < 1 → x ^ p.toReal ≥ x := by
                  exact fun x hx => by simpa using Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le ( show p.toReal ≤ 1 by exact_mod_cast ENNReal.toReal_mono ( by aesop ) ( show p ≤ 1 by exact le_of_lt ( Fact.out ) ) ) ;
                exact le_trans ( by rw [ ← add_div, div_self ( by positivity ) ] ) ( add_le_add ( h_ineq_pow _ ⟨ by positivity, by rw [ div_lt_iff₀ ( by positivity ) ] ; linarith [ show 0 < a by positivity, show 0 < b by positivity ] ⟩ ) ( h_ineq_pow _ ⟨ by positivity, by rw [ div_lt_iff₀ ( by positivity ) ] ; linarith [ show 0 < a by positivity, show 0 < b by positivity ] ⟩ ) );
              rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.div_rpow ( by positivity ) ( by positivity ) ] at h_ineq_pow;
              rwa [ ← add_div, ge_iff_le, one_le_div ( by positivity ) ] at h_ineq_pow
            by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;> simp +decide [ * ];
            · positivity;
            · positivity;
            · positivity;
          exact h_ineq_pow a b ha hb;
        refine' le_trans ( Real.rpow_le_rpow ( by positivity ) h_ineq ( by exact ENNReal.toReal_nonneg ) ) _;
        convert h_ineq_pow ( |c'| * ‖x' i - x i‖ ) ( |c' - c| * ‖x i‖ ) ( by positivity ) ( by positivity ) using 1 ; rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ];
      intro c' c x' x
      have h_sum : ∑' i, ‖(c' • x' : ∀ j, ℝ) i - (c • x : ∀ j, ℝ) i‖ ^ p.toReal ≤ ∑' i, (|c'|^p.toReal * ‖x' i - x i‖ ^ p.toReal + |c' - c|^p.toReal * ‖x i‖ ^ p.toReal) := by
        by_cases h : Summable ( fun i => ‖ ( c' • x' : ∀ j, ℝ ) i - ( c • x : ∀ j, ℝ ) i‖ ^ p.toReal ) <;> simp_all +decide [ tsum_eq_zero_of_not_summable ];
        · refine' Summable.tsum_le_tsum ( fun i => h_ineq c' c _ x'.2 _ x.2 i ) _ _;
          · exact h;
          · refine' Summable.add _ _;
            · have := x'.2.sub x.2;
              refine' Summable.mul_left _ _;
              convert this.summable using 1;
              cases p using ENNReal.recTopCoe <;> aesop;
              exact Or.inl Fact.out;
            · have := x.2.summable;
              by_cases hp : p.toReal = 0 <;> aesop;
              exact Summable.mul_left _ ( this ( lt_of_le_of_ne ( ENNReal.toReal_nonneg ) ( Ne.symm hp ) ) );
        · exact tsum_nonneg fun _ => add_nonneg ( mul_nonneg ( Real.rpow_nonneg ( abs_nonneg _ ) _ ) ( Real.rpow_nonneg ( abs_nonneg _ ) _ ) ) ( mul_nonneg ( Real.rpow_nonneg ( abs_nonneg _ ) _ ) ( Real.rpow_nonneg ( abs_nonneg _ ) _ ) );
      rw [ Summable.tsum_add ] at h_sum;
      · convert h_sum using 1;
        simp +decide [ dist_eq_norm, tsum_mul_left ];
        simp +decide [ Dist.dist, lp ];
      · have h_summable : Summable (fun i => ‖(x' : ∀ j, ℝ) i - (x : ∀ j, ℝ) i‖ ^ p.toReal) := by
          have := x'.2.sub x.2;
          convert this.summable using 1;
          by_cases h : 0 < p.toReal <;> aesop;
          exact False.elim <| h.not_lt <| ENNReal.toReal_pos ( ne_of_gt <| Fact.out ) <| ne_of_lt <| lt_of_lt_of_le ( Fact.out : p < 1 ) <| by norm_num;
        exact h_summable.mul_left _;
      · refine' Summable.mul_left _ _;
        have := x.2.summable;
        convert this ( ENNReal.toReal_pos ( ne_of_gt Fact.out ) ( ne_of_lt ( lt_of_lt_of_le Fact.out ( le_top ) ) ) ) using 1;
        exact Fact.mk ( Fact.out : p < 1 );
    -- Let's choose δ such that |c' - c|^p.toReal < ε / 2 and |c'|^p.toReal < 1 + |c|^p.toReal.
    obtain ⟨δ1, hδ1⟩ : ∃ δ1 > 0, ∀ (c' : ℝ), |c' - p_prod.1| < δ1 → |c'|^p.toReal < 1 + |p_prod.1|^p.toReal := by
      have := Metric.continuous_iff.mp ( show Continuous fun x : ℝ => |x| ^ p.toReal from by exact Continuous.rpow_const ( continuous_abs ) fun x => Or.inr <| by exact ENNReal.toReal_nonneg ) p_prod.1;
      exact Exists.elim ( this 1 zero_lt_one ) fun δ hδ => ⟨ δ, hδ.1, fun c' hc' => by linarith [ abs_lt.mp ( hδ.2 c' hc' ) ] ⟩;
    -- Let's choose δ such that |c' - c|^p.toReal < ε / (2 * (1 + |p_prod.1|^p.toReal)) and |x' - x|^p.toReal < ε / (2 * (1 + |p_prod.1|^p.toReal)).
    obtain ⟨δ2, hδ2⟩ : ∃ δ2 > 0, ∀ (x' : ↥(lp (fun _ : ι => ℝ) p)), dist x' p_prod.2 < δ2 → (1 + |p_prod.1|^p.toReal) * dist x' p_prod.2 < ε / 2 := by
      exact ⟨ ε / 2 / ( 1 + |p_prod.1| ^ p.toReal ), div_pos ( half_pos hε ) ( by positivity ), fun x' hx' => by rw [ lt_div_iff₀ ( by positivity ) ] at hx'; linarith ⟩;
    obtain ⟨δ3, hδ3⟩ : ∃ δ3 > 0, ∀ (c' : ℝ), |c' - p_prod.1| < δ3 → |c' - p_prod.1|^p.toReal * dist p_prod.2 0 < ε / 2 := by
      -- Since $|c' - p_prod.1|^p.toReal$ is continuous at $c' = p_prod.1$, we can find $\delta_3$ such that $|c' - p_prod.1|^p.toReal < \frac{\epsilon}{2D}$ for $|c' - p_prod.1| < \delta_3$, where $D = dist p_prod.2 0$.
      have h_cont : ContinuousAt (fun c' : ℝ => |c' - p_prod.1|^p.toReal) p_prod.1 := by
        exact ContinuousAt.rpow ( continuousAt_id.sub continuousAt_const |> ContinuousAt.abs ) continuousAt_const <| Or.inr <| by linarith [ show 0 < p.toReal from ENNReal.toReal_pos ( ne_bot_of_gt <| Fact.out ( p := 0 < p ) ) ( ne_of_lt <| lt_of_lt_of_le ( Fact.out ( p := p < 1 ) ) <| by norm_num ) ] ;
      have := Metric.continuousAt_iff.mp h_cont ( ε / 2 / ( Dist.dist p_prod.2 0 + 1 ) ) ( div_pos ( half_pos hε ) ( add_pos_of_nonneg_of_pos dist_nonneg zero_lt_one ) );
      simp_all +decide [ ne_of_gt ( show 0 < p.toReal from ENNReal.toReal_pos ( ne_of_gt ( Fact.out : 0 < p ) ) ( ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) ) ) ) ];
      exact ⟨ this.choose, this.choose_spec.1, fun c' hc' => by have := this.choose_spec.2 hc'; rw [ abs_of_nonneg ( Real.rpow_nonneg ( abs_nonneg _ ) _ ) ] at this; rw [ lt_div_iff₀ ( by positivity ) ] at this; nlinarith [ abs_nonneg ( c' - p_prod.1 ), Real.rpow_nonneg ( abs_nonneg ( c' - p_prod.1 ) ) p.toReal ] ⟩;
    refine' ⟨ Min.min δ1 ( Min.min δ2 δ3 ), lt_min hδ1.1 ( lt_min hδ2.1 hδ3.1 ), fun a ha => _ ⟩ ; simp_all +decide [ Prod.dist_eq ];
    refine' lt_of_le_of_lt ( h_cont _ _ _ _ _ _ ) _;
    refine' lt_of_le_of_lt ( add_le_add ( mul_le_mul_of_nonneg_right ( le_of_lt ( hδ1.2 _ ( by simpa using ha.1.1 ) ) ) ( dist_nonneg ) ) le_rfl ) _;
    linarith! [ hδ2.2 _ _ ha.2.1.2, hδ3.2 _ ha.2.2.1 ] }

/-
In $\ell^p$ with $0 < p < 1$, one can find a convex combination of vectors arbitrarily close to 0
that has arbitrarily large norm.
-/
open scoped ENNReal

theorem lp_convex_combination_large_norm {p : ℝ≥0∞} [Fact (0 < p)] [Fact (p < 1)] (δ : ℝ) (hδ : 0 < δ) (M : ℝ) :
    ∃ (n : ℕ) (v : Fin n → lp (fun _ : ℕ => ℝ) p) (w : Fin n → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∀ i, dist (v i) 0 < δ) ∧
      dist (∑ i, w i • v i) 0 > M := by
  -- Choose $N$ such that $\frac{\delta}{2} N^{1-p} > M$.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N ≥ 1 ∧ (δ / 2) * (N : ℝ) ^ (1 - p.toReal) > M) := by
    -- Since $p < 1$, we have $1 - p.toReal > 0$, thus $(N : ℝ) ^ (1 - p.toReal)$ grows without bound as $N$ increases.
    have h_growth : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - p.toReal)) Filter.atTop Filter.atTop := by
      convert tendsto_rpow_atTop ( show 0 < 1 - p.toReal from _ ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop using 1;
      rcases p with ( _ | _ | p ) <;> norm_num at *;
      -- Since the Cauchy sequence is less than 1, we can conclude that the real number it represents is also less than 1.
      apply Fact.out;
    exact Filter.eventually_atTop.mp ( h_growth.eventually_gt_atTop ( M / ( δ / 2 ) ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N + 1, by linarith, by have := hN ( N + 1 ) ( by linarith ) ; rw [ div_lt_iff₀ ] at this <;> linarith ⟩;
  refine' ⟨ N, fun i => ⟨ fun j => if j = i then ( δ / 2 ) ^ ( 1 / p.toReal ) else 0, _ ⟩, fun _ => 1 / N, _, _, _, _ ⟩ <;> norm_num <;> aesop;
  any_goals rw [ mul_inv_cancel₀ ( by positivity ) ];
  all_goals norm_num [ Dist.dist ];
  · cases p ; aesop;
    · exact False.elim <| Fact.out;
    · simp +decide [ lp ];
      unfold Memℓp; aesop;
      exact ⟨ _, hasSum_single ( i : ℕ ) fun j hj => by aesop ⟩;
  · rw [ tsum_eq_single ( i : ℕ ) ] <;> aesop;
    · rw [ abs_of_nonneg ( by positivity ), ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ] <;> norm_num;
      · positivity;
      · rw [ ENNReal.toReal_eq_zero_iff ] ; aesop;
        · exact False.elim <| Fact.out;
        · exact False.elim <| Fact.out;
    · -- Since $p$ is a positive real number, $p.toReal$ is also positive. Therefore, $0^{p.toReal} = 0$.
      have h_pos : 0 < p.toReal := by
        cases p using ENNReal.recTopCoe <;> aesop;
        · exact False.elim <| Fact.out;
        · exact Fact.out;
      rw [ Real.zero_rpow h_pos.ne' ];
  · rw [ tsum_eq_sum ];
    any_goals exact Finset.range N;
    · simp_all +decide [ Finset.sum_ite, Fin.val_inj ];
      -- Simplify the expression inside the sum.
      have h_simp : ∀ x ∈ Finset.range N, ((Finset.card (Finset.filter (fun y : Fin N => x = y.val) Finset.univ)) * ((N : ℝ)⁻¹ * |(δ / 2) ^ p.toReal⁻¹|)) ^ p.toReal = (1 / N * |(δ / 2) ^ p.toReal⁻¹|) ^ p.toReal := by
        intro x hx; rw [ show ( Finset.filter ( fun y : Fin N => x = ( y : ℕ ) ) Finset.univ : Finset ( Fin N ) ) = { ⟨ x, by linarith [ Finset.mem_range.mp hx ] ⟩ } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, rfl ⟩, fun y hy => Fin.ext <| by aesop ⟩ ] ; aesop;
      rw [ Finset.sum_congr rfl h_simp ] ; aesop;
      rw [ abs_of_nonneg ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ), Real.inv_rpow ( by positivity ), ← Real.rpow_mul ( by positivity ), inv_mul_eq_div, div_eq_mul_inv ];
      by_cases h : p.toReal = 0 <;> aesop;
      · rw [ ENNReal.toReal_eq_zero_iff ] at h ; aesop;
        · exact False.elim <| Fact.out;
        · exact False.elim <| Fact.out;
      · convert right using 1 ; rw [ Real.rpow_sub ( by positivity ), Real.rpow_one ] ; ring;
    · intro b hb; rw [ Finset.sum_eq_zero ] <;> aesop;
      · -- Since $p$ is positive, $p.toReal$ is also positive. Therefore, $0^{p.toReal} = 0$.
        have h_pos : 0 < p.toReal := by
          cases p <;> aesop;
          · exact False.elim <| Fact.out;
          · exact Fact.out;
        rw [ Real.zero_rpow h_pos.ne' ];
      · linarith [ Fin.is_lt x ]

/-
For every $0 < p < 1$, the space $\ell^{p}$ is not Bolognese.
-/
open scoped ENNReal

theorem lp_not_bolognese (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] :
    ¬ Bolognese (lp (fun _ : ℕ => ℝ) p) := by
      -- Assume that ℓ^p is Bolognese.
      by_contra h_bolognese

      -- Then there exists a convex open set C containing 0 such that C is contained in the unit ball.
      obtain ⟨C, hC_convex, hC_open, hC_zero, hC_unit⟩ : ∃ C : Set (lp (fun _ : ℕ => ℝ) p), IsOpen C ∧ Convex ℝ C ∧ 0 ∈ C ∧ C ⊆ {x : lp (fun _ : ℕ => ℝ) p | dist x 0 < 1} := by
        exact Exists.imp ( by aesop ) ( h_bolognese { x : lp ( fun _ : ℕ => ℝ ) p | Dist.dist x 0 < 1 } 0 ( Metric.isOpen_ball ) ( by norm_num ) );
      -- Since $C$ is open and contains $0$, there exists a $\delta > 0$ such that $B(0, \delta) \subseteq C$.
      obtain ⟨δ, hδ_pos, hδ_ball⟩ : ∃ δ > 0, Metric.ball 0 δ ⊆ C := by
        -- Since $C$ is open and contains $0$, by the definition of open sets in metric spaces, there exists an $\epsilon > 0$ such that the ball of radius $\epsilon$ around $0$ is entirely within $C$.
        apply Metric.isOpen_iff.mp hC_convex 0 hC_zero;
      -- By Lemma~\ref{lem:lp_convex_combination_large_norm}, there exists a convex combination $y = \sum w_i v_i$ of vectors $v_i \in B(0, \delta)$ such that $\|y\| > 1$.
      obtain ⟨n, v, w, hw_nonneg, hw_sum, hvδ, hy⟩ : ∃ n : ℕ, ∃ v : Fin n → lp (fun _ : ℕ => ℝ) p, ∃ w : Fin n → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, dist (v i) 0 < δ) ∧ dist (∑ i, w i • v i) 0 > 1 := by
        -- Apply the lemma `lp_convex_combination_large_norm` with δ and M = 1.
        apply lp_convex_combination_large_norm δ hδ_pos 1;
      -- Since $C$ is convex and contains $0$, the convex combination $y = \sum w_i v_i$ must also be in $C$.
      have hy_in_C : ∑ i, w i • v i ∈ C := by
        exact hC_open.sum_mem ( fun i _ => hw_nonneg i ) hw_sum ( fun i _ => hδ_ball ( hvδ i ) );
      exact hy.not_ge <| le_of_lt <| hC_unit hy_in_C


#synth AddCommGroup (Fin 3 → ℝ)
#synth Module ℝ (Fin 3 → ℝ)
#synth TopologicalSpace ℝ
#synth TopologicalSpace (Fin 3 → ℝ)

/-
Distance on Lp space for 0 < p < 1.
-/
open MeasureTheory ENNReal

noncomputable instance instDistLpOfLtOne {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] : Dist (Lp E p μ) :=
  ⟨fun f g => (eLpNorm (f - g) p μ).toReal ^ p.toReal⟩

/-
Checking for scalar inequalities.
-/
#check NNReal.rpow_add_le_add_rpow
#check ENNReal.rpow_add_le_add_rpow

/-
Integral inequality for p-th powers of norms with 0 < p < 1.
-/
open MeasureTheory ENNReal

lemma lintegral_rpow_add_le_add_lintegral_rpow {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)]
    (f g : α → E) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, (‖f x + g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ ≤ ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ + ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ := by
      -- Apply the integral to both sides of the inequality ‖f x + g x‖ ^ p.toReal ≤ ‖f x‖ ^ p.toReal + ‖g x‖ ^ p.toReal.
      have h_integral : ∫⁻ x, (‖f x + g x‖₊ : ENNReal) ^ p.toReal ∂μ ≤ ∫⁻ x, (‖f x‖₊ + ‖g x‖₊ : ENNReal) ^ p.toReal ∂μ := by
        apply_rules [ MeasureTheory.lintegral_mono_ae ];
        filter_upwards [ ] with x using by gcongr ; exact mod_cast norm_add_le ( f x ) ( g x ) ;
      refine' le_trans h_integral _;
      rw [ ← MeasureTheory.lintegral_add_right' ];
      · refine' MeasureTheory.lintegral_mono fun x => _;
        have := @ENNReal.rpow_add_le_add_rpow;
        exact this _ _ ( ENNReal.toReal_nonneg ) ( ENNReal.toReal_le_of_le_ofReal ( by norm_num ) ( by simpa using Fact.out ( p := p < 1 ) |> le_of_lt ) );
      · exact AEMeasurable.pow_const ( AEMeasurable.coe_nnreal_ennreal ( hg.nnnorm.aemeasurable ) ) _

/-
Simplification of the distance formula for Lp spaces with 0 < p < 1.
-/
open MeasureTheory ENNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)]

lemma dist_eq_lintegral_rpow_of_lt_one (f g : Lp E p μ) :
    dist f g = (∫⁻ x, (‖f x - g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ).toReal := by
      -- By definition of eLpNorm, we have eLpNorm (f - g) p μ = (∫⁻ x, ‖f x - g x‖₊ ^ p.toReal ∂μ) ^ (1 / p.toReal).
      have h_eLpNorm : eLpNorm (f - g) p μ = (∫⁻ x, ‖(f : α → E) x - (g : α → E) x‖₊ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
        rw [ eLpNorm_congr_ae ( Lp.coeFn_sub _ _ ) ];
        rw [ eLpNorm_eq_lintegral_rpow_enorm ];
        · simp +decide [ ← ENNReal.ofReal_coe_nnreal ];
        · exact ne_of_gt Fact.out;
        · exact ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) );
      unfold dist;
      convert congr_arg ( ·.toReal ^ p.toReal ) h_eLpNorm using 1;
      rw [ ENNReal.toReal_rpow ];
      rw [ ← ENNReal.rpow_mul, one_div_mul_cancel ( ne_of_gt <| ENNReal.toReal_pos ( ne_of_gt <| Fact.out ) <| ne_of_lt <| lt_of_lt_of_le ( Fact.out : p < 1 ) <| by norm_num ), ENNReal.rpow_one ]

/-
Triangle inequality for the integral of the p-th power of the distance in Lp.
-/
open MeasureTheory ENNReal

lemma lintegral_dist_triangle_of_lt_one {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] (f g h : Lp E p μ) :
    ∫⁻ x, (‖f x - h x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ ≤
    ∫⁻ x, (‖f x - g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ + ∫⁻ x, (‖g x - h x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ := by
      -- Apply the lemma to the functions f - g and g - h, which are measurable.
      have h_measurable : AEStronglyMeasurable (fun x => f x - g x) μ ∧ AEStronglyMeasurable (fun x => g x - h x) μ := by
        constructor <;> refine' ( Lp.aestronglyMeasurable _ ) |> fun h => h.sub ( Lp.aestronglyMeasurable _ );
      convert lintegral_rpow_add_le_add_lintegral_rpow p ( fun x => f x - g x ) ( fun x => g x - h x ) h_measurable.1 h_measurable.2 using 3 ; simp +decide [ sub_add_sub_cancel ]

/-
Finiteness of the integral of the p-th power of the distance in Lp.
-/
open MeasureTheory ENNReal

lemma lintegral_nnnorm_rpow_sub_lt_top {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] (f g : Lp E p μ) :
    ∫⁻ x, (‖f x - g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ < ⊤ := by
      have h_integrable : ∀ (f : Lp E p μ), ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ < ⊤ := by
        intro f;
        convert f.2 using 1;
        rw [ Lp.mem_Lp_iff_eLpNorm_lt_top ];
        rw [ eLpNorm_eq_lintegral_rpow_enorm ];
        · simp +decide [ ENNReal.rpow_lt_top_iff_of_pos, show p.toReal > 0 from ENNReal.toReal_pos ( ne_of_gt Fact.out ) ( ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) ) ) ];
          simp +decide [ ENorm.enorm ];
        · exact ne_of_gt Fact.out;
        · exact ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) );
      convert h_integrable ( f - g ) using 1;
      erw [ MeasureTheory.lintegral_congr_ae ];
      filter_upwards [ MeasureTheory.Lp.coeFn_sub f g ] with x hx using by aesop

/-
Triangle inequality for the Lp metric when 0 < p < 1.
-/
open MeasureTheory ENNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)]

lemma dist_triangle_of_lt_one (f g h : Lp E p μ) : dist f h ≤ dist f g + dist g h := by
  rw [ dist_eq_lintegral_rpow_of_lt_one, dist_eq_lintegral_rpow_of_lt_one, dist_eq_lintegral_rpow_of_lt_one ];
  convert ENNReal.toReal_mono _ ( lintegral_dist_triangle_of_lt_one p f g h );
  · rw [ ENNReal.toReal_add _ _ ];
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun x => by aesop ) ( lintegral_nnnorm_rpow_sub_lt_top p f g ) );
    · convert ( lintegral_nnnorm_rpow_sub_lt_top p g h ) |> ne_of_lt;
  · refine' ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ _, _ ⟩ );
    · exact?;
    · exact?

/-
Lp space is a metric space for 0 < p < 1.
-/
open MeasureTheory ENNReal

noncomputable instance instMetricSpaceLpOfLtOne {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] : MetricSpace (Lp E p μ) :=
{ dist := Dist.dist
  edist := fun f g => ENNReal.ofReal (dist f g)
  dist_self := by
    -- The distance from any element to itself is zero.
    intros x
    simp [dist];
    rw [ eLpNorm_congr_ae ( MeasureTheory.ae_iff.mpr _ ) ];
    rotate_left;
    -- The zero function is measurable.
    use 0; simp;
    · erw [ MeasureTheory.Lp.coeFn_zero ];
      exact p;
    · -- The eLpNorm of the zero function is zero because the integral of the p-th power of the norm of the zero function is zero.
      simp [eLpNorm];
      split_ifs <;> simp_all +decide [ eLpNorm' ];
      cases eq_or_ne p.toReal 0 <;> simp_all +decide [ ENNReal.toReal ];
      rw [ ← ENNReal.coe_eq_zero ] at * ; aesop
  dist_comm := by
    -- The distance function is symmetric because the norm is symmetric.
    intros x y
    simp [dist_eq_lintegral_rpow_of_lt_one];
    -- Since the norm is symmetric, we have ‖x - y‖ = ‖y - x‖.
    have h_symm : ∀ x y : Lp E p μ, ∀ a : α, ‖x a - y a‖₊ = ‖y a - x a‖₊ := by
      exact fun x y a => by rw [ ← nnnorm_neg, neg_sub ] ;
    simp +decide only [h_symm x y]
  dist_triangle := dist_triangle_of_lt_one p
  edist_dist := by
    -- The equality is trivially true since both sides are the same.
    intros x y
    simp
  eq_of_dist_eq_zero := by
    intros x y hxy;
    -- Since $p < 1$, the integral of the $p$-th power of the norm of $x - y$ being zero implies that $x - y$ is zero almost everywhere.
    have h_ae_zero : ∀ᵐ x_1 ∂μ, ‖x x_1 - y x_1‖₊ = 0 := by
      have h_ae_zero : ∫⁻ x_1, (‖x x_1 - y x_1‖₊ : ℝ≥0∞) ^ p.toReal ∂μ = 0 := by
        rw [ dist_eq_lintegral_rpow_of_lt_one ] at hxy;
        rw [ ENNReal.toReal_eq_zero_iff ] at hxy;
        exact hxy.resolve_right ( ne_of_lt ( lintegral_nnnorm_rpow_sub_lt_top p x y ) );
      rw [ MeasureTheory.lintegral_eq_zero_iff' ] at h_ae_zero;
      · filter_upwards [ h_ae_zero ] with a ha using not_not.mp fun ha' => ha.not_gt <| ENNReal.rpow_pos ( by aesop ) <| by aesop;
      · refine' AEMeasurable.pow_const _ _;
        have h_ae_zero : AEMeasurable (fun x_1 => ‖x x_1 - y x_1‖₊) μ := by
          exact ( x.1.aestronglyMeasurable.sub y.1.aestronglyMeasurable ).nnnorm.aemeasurable;
        exact ENNReal.continuous_coe.measurable.comp_aemeasurable h_ae_zero;
    ext1; simp_all +decide [ sub_eq_zero ] ;
    exact h_ae_zero }

/-
Checking if Bolognese is defined and if Lp has a Module instance.
-/
#check Bolognese
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)]
#synth Module ℝ (MeasureTheory.Lp E p μ)

/-
Checking if ν is available.
-/
#check ν

/-
Lp space is a topological additive group for 0 < p < 1.
-/
open MeasureTheory ENNReal

noncomputable instance instTopologicalAddGroupLpOfLtOne {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] : IsTopologicalAddGroup (Lp E p μ) :=
{ continuous_add := by
    -- Use the triangle inequality to show that addition is continuous.
    have h_add_cont : ∀ (f g f' g' : MeasureTheory.Lp E p μ), dist (f + g) (f' + g') ≤ dist f f' + dist g g' := by
      intro f g f' g'
      have h_triangle : ∫⁻ x, (‖(f + g) x - (f' + g') x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ ≤ ∫⁻ x, (‖f x - f' x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ + ∫⁻ x, (‖g x - g' x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ := by
        convert lintegral_rpow_add_le_add_lintegral_rpow p ( fun x => ( f x - f' x ) ) ( fun x => ( g x - g' x ) ) _ _ using 1;
        · rw [ MeasureTheory.lintegral_congr_ae ];
          filter_upwards [ MeasureTheory.Lp.coeFn_add f g, MeasureTheory.Lp.coeFn_add f' g' ] with x hx₁ hx₂;
          simp +decide [ hx₁, hx₂, sub_add_sub_comm ];
          congr;
        · exact MeasureTheory.AEStronglyMeasurable.sub ( MeasureTheory.Lp.aestronglyMeasurable _ ) ( MeasureTheory.Lp.aestronglyMeasurable _ );
        · exact ( g.1.aestronglyMeasurable.sub g'.1.aestronglyMeasurable );
      rw [ dist_eq_lintegral_rpow_of_lt_one, dist_eq_lintegral_rpow_of_lt_one, dist_eq_lintegral_rpow_of_lt_one ];
      convert ENNReal.toReal_mono _ h_triangle using 1;
      · rw [ ENNReal.toReal_add ];
        · -- Since $f$ and $f'$ are in $L^p$, their difference $f - f'$ is also in $L^p$, and thus the integral of the $p$-th power of the norm of $f - f'$ is finite.
          have h_finite : ∫⁻ x, (‖f x - f' x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ < ⊤ := by
            -- Apply the hypothesis `h_finite` to conclude the proof.
            apply lintegral_nnnorm_rpow_sub_lt_top
          exact ne_of_lt h_finite;
        · exact ne_of_lt ( lintegral_nnnorm_rpow_sub_lt_top p g g' );
      · refine' ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ _, _ ⟩ );
        · convert lintegral_nnnorm_rpow_sub_lt_top p f f' using 1;
        · convert lintegral_nnnorm_rpow_sub_lt_top p g g';
    rw [ Metric.continuous_iff ];
    exact fun x ε εpos => ⟨ ε / 2, half_pos εpos, fun y hy => lt_of_le_of_lt ( h_add_cont _ _ _ _ ) ( by linarith [ show dist y.1 x.1 < ε / 2 from lt_of_le_of_lt ( le_max_left _ _ ) hy, show dist y.2 x.2 < ε / 2 from lt_of_le_of_lt ( le_max_right _ _ ) hy ] ) ⟩
  continuous_neg := by
    rw [ Metric.continuous_iff ];
    intro b ε εpos;
    use ε;
    simp [dist];
    refine' ⟨ εpos, fun a ha h => _ ⟩;
    convert h using 2;
    simp +decide [ neg_add_eq_sub ];
    rw [ ← neg_sub, eLpNorm_congr_ae ( MeasureTheory.AEEqFun.coeFn_neg _ ) ];
    simp +decide [ eLpNorm ];
    split_ifs <;> simp_all +decide [ eLpNormEssSup ] }

/-
Homogeneity of the distance to 0 in Lp space for 0 < p < 1.
-/
open MeasureTheory ENNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)]

lemma dist_smul_eq_mul_dist (c : ℝ) (f : Lp E p μ) :
    dist (c • f) 0 = |c| ^ p.toReal * dist f 0 := by
      simp +decide [ instDistLpOfLtOne ];
      rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ), eLpNorm_congr_ae ( MeasureTheory.Lp.coeFn_smul _ _ ) ];
      rw [ eLpNorm_const_smul ];
      rw [ ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs ];
      rw [ ENNReal.toReal_ofReal ( abs_nonneg c ) ]

/-
Inequality for the distance of scalar multiples in Lp space.
-/
open MeasureTheory ENNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)]

lemma dist_smul_sub_smul_le (c c' : ℝ) (f f' : Lp E p μ) :
    dist (c' • f') (c • f) ≤ |c'| ^ p.toReal * dist f' f + |c' - c| ^ p.toReal * dist f 0 := by
  calc dist (c' • f') (c • f)
    _ ≤ dist (c' • f') (c' • f) + dist (c' • f) (c • f) := dist_triangle _ _ _
    _ = dist (c' • (f' - f)) 0 + dist ((c' - c) • f) 0 := by
      congr 1
      · simp only [dist, sub_zero]
        rw [← smul_sub]
      · simp only [dist, sub_zero]
        rw [← sub_smul]
    _ = |c'| ^ p.toReal * dist (f' - f) 0 + |c' - c| ^ p.toReal * dist f 0 := by
      rw [dist_smul_eq_mul_dist, dist_smul_eq_mul_dist]
    _ = |c'| ^ p.toReal * dist f' f + |c' - c| ^ p.toReal * dist f 0 := by
      congr 2
      simp [dist]

/-
Lp space has continuous scalar multiplication for 0 < p < 1.
-/
open MeasureTheory ENNReal

noncomputable instance instContinuousSMulLpOfLtOne {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] : ContinuousSMul ℝ (Lp E p μ) :=
{ continuous_smul := by
    rw [continuous_iff_continuousAt]
    rintro ⟨c, f⟩
    rw [Metric.continuousAt_iff]
    intro ε hε
    have h_ineq : ∀ (c' : ℝ) (f' : Lp E p μ), dist (c' • f') (c • f) ≤ |c'| ^ p.toReal * dist f' f + |c' - c| ^ p.toReal * dist f 0 := by
      intro c' f'
      exact dist_smul_sub_smul_le p c c' f f'
    -- Choose δ such that |c'|^p.toReal * δ + |c' - c|^p.toReal * dist f 0 < ε for all (c', f') with dist (c', f') (c, f) < δ.
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ c' : ℝ, ∀ f' : Lp E p μ, |c' - c| < δ ∧ dist f' f < δ → |c'|^p.toReal * δ + |c' - c|^p.toReal * dist f 0 < ε := by
      -- Choose δ such that |c'|^p.toReal * δ + |c' - c|^p.toReal * dist f 0 < ε for all (c', f') with dist (c', f') (c, f) < δ. We can use the fact that |c'|^p.toReal is continuous at c and |c' - c|^p.toReal is continuous at 0.
      obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ c' : ℝ, |c' - c| < δ₁ → |c'|^p.toReal ≤ |c|^p.toReal + 1 := by
        have h_cont : ContinuousAt (fun c' : ℝ => |c'|^p.toReal) c := by
          by_cases h : p.toReal = 0 <;> simp_all +decide [ ContinuousAt ];
          exact Filter.Tendsto.rpow ( Filter.tendsto_id.abs ) tendsto_const_nhds ( Or.inr <| by positivity );
        exact Metric.mem_nhds_iff.mp ( h_cont.eventually ( ge_mem_nhds ( lt_add_one _ ) ) );
      -- Choose δ such that |c' - c|^p.toReal * dist f 0 < ε / 2 for all (c', f') with dist (c', f') (c, f) < δ.
      obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ c' : ℝ, |c' - c| < δ₂ → |c' - c|^p.toReal * dist f 0 < ε / 2 := by
        have h_cont : Filter.Tendsto (fun c' : ℝ => |c' - c| ^ p.toReal * dist f 0) (nhds c) (nhds 0) := by
          convert Filter.Tendsto.mul ( Filter.Tendsto.rpow ( Filter.Tendsto.abs ( Filter.tendsto_id.sub tendsto_const_nhds ) ) tendsto_const_nhds _ ) tendsto_const_nhds using 2 <;> norm_num;
          · exact Or.inl ( Real.zero_rpow ( ne_of_gt ( ENNReal.toReal_pos ( ne_bot_of_gt ( Fact.out : 0 < p ) ) ( ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) ) ) ) ) );
          · exact ENNReal.toReal_pos ( ne_of_gt ( Fact.out : 0 < p ) ) ( ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) ) );
        exact Metric.mem_nhds_iff.mp ( h_cont.eventually ( gt_mem_nhds <| half_pos hε ) );
      -- Choose δ such that δ * (|c|^p.toReal + 1) < ε / 2.
      obtain ⟨δ₃, hδ₃_pos, hδ₃⟩ : ∃ δ₃ > 0, δ₃ * (|c|^p.toReal + 1) < ε / 2 := by
        exact ⟨ ( ε / 2 ) / ( |c| ^ p.toReal + 1 ) / 2, by positivity, by nlinarith [ div_mul_cancel₀ ( ε / 2 ) ( by positivity : ( |c| ^ p.toReal + 1 ) ≠ 0 ) ] ⟩;
      exact ⟨ Min.min δ₁ ( Min.min δ₂ δ₃ ), lt_min hδ₁_pos ( lt_min hδ₂_pos hδ₃_pos ), fun c' f' h => by nlinarith [ hδ₁ c' ( lt_of_lt_of_le h.1 ( min_le_left _ _ ) ), hδ₂ c' ( lt_of_lt_of_le h.1 ( min_le_of_right_le ( min_le_left _ _ ) ) ), min_le_right δ₁ ( Min.min δ₂ δ₃ ), min_le_right δ₂ δ₃, min_le_right δ₁ ( Min.min δ₂ δ₃ ), min_le_right δ₂ δ₃, show 0 ≤ |c'| ^ p.toReal by positivity, show 0 ≤ |c' - c| ^ p.toReal * dist f 0 by positivity ] ⟩;
    refine' ⟨ Min.min δ 1, lt_min hδ_pos zero_lt_one, fun x hx => lt_of_le_of_lt ( h_ineq x.1 x.2 ) _ ⟩ ; simp_all +decide [ Prod.dist_eq ];
    refine' lt_of_le_of_lt ( add_le_add ( mul_le_mul_of_nonneg_left hx.1.2.le <| by positivity ) le_rfl ) ( hδ _ _ _ hx.1.1 hx.1.2 ) |> lt_of_lt_of_le <| le_rfl; }

/-
Continuity of scalar multiplication in Lp space at a point.
-/
open MeasureTheory ENNReal

lemma continuousAt_smul_Lp {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)]
    (c : ℝ) (f : Lp E p μ) :
    ContinuousAt (fun (x : ℝ × Lp E p μ) => x.1 • x.2) (c, f) := by
      apply_rules [ ContinuousAt.smul ];
      · exact continuousAt_fst;
      · exact continuous_snd.continuousAt

/-
Checking lp definitions and instances.
-/
#check lp
#check lp.single
variable {p : ℝ≥0∞} [Fact (0 < p)] [Fact (p < 1)]
#check (inferInstance : Dist (lp (fun _ : ℕ => ℝ) p))

/-
Lp space is a metric space for 0 < p < 1.
-/
open MeasureTheory ENNReal

noncomputable instance instMetricSpaceLpOfLtOne' {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] : MetricSpace (Lp E p μ) :=
{ dist := Dist.dist
  edist := fun f g => ENNReal.ofReal (dist f g)
  dist_self := by
    simp +decide [ dist_eq_norm ]
  dist_comm := by
    -- The distance function in Lp space is symmetric because the integral of the p-th power of the norm is symmetric.
    intros x y
    simp [dist_eq_lintegral_rpow_of_lt_one];
    -- Since the norm is symmetric, we have ‖x - y‖ = ‖y - x‖ for all x and y.
    have h_symm : ∀ x y : α → E, ∀ x_1 : α, ‖x x_1 - y x_1‖₊ = ‖y x_1 - x x_1‖₊ := by
      exact fun x y i => by rw [ ← nnnorm_neg, neg_sub ] ;
    simp +decide only [h_symm]
  dist_triangle := dist_triangle_of_lt_one p
  edist_dist := by
    grind
  eq_of_dist_eq_zero := by
    intro x y hxy;
    rw [ eq_comm ] at hxy;
    rw [ eq_comm, dist_eq_zero ] at hxy ; aesop }

/-
Checking if lp.instMetricSpace_of_lt_one is defined.
-/
variable {p : ℝ≥0∞} [Fact (0 < p)] [Fact (p < 1)]
#check lp.instMetricSpace_of_lt_one p

/-
Lp space is a topological additive group for 0 < p < 1.
-/
open MeasureTheory ENNReal

noncomputable instance instTopologicalAddGroupLpOfLtOne' {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] : IsTopologicalAddGroup (Lp E p μ) :=
{ continuous_add := by
    apply_rules [ Continuous.add, continuous_const, continuous_fst, continuous_snd ]
  continuous_neg := by
    -- The negation function is continuous because it is a linear map.
    apply continuous_neg }

/-
Checking for existing instance and defining a new one if needed.
-/
open MeasureTheory ENNReal

#check instContinuousSMulLpOfLtOne

noncomputable instance instContinuousSMulLpOfLtOne' {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] : ContinuousSMul ℝ (Lp E p μ) :=
{ continuous_smul := by
    rw [ continuous_iff_continuousAt ];
    rintro ⟨c, f⟩;
    exact continuousAt_smul_Lp p c f }

#check ν
#check MeasureTheory.Lp

/-
The measure ν on [0,1] has no atoms.
-/
open MeasureTheory ENNReal Set Metric

instance instNoAtoms_ν : NoAtoms ν := by
  -- Since the Lebesgue measure has no atoms, for any singleton set {x} in [0,1], the volume of {x} is zero.
  have h_volume_zero : ∀ x : Icc (0 : ℝ) 1, MeasureTheory.volume {x} = 0 := by
    exact?;
  exact?

/-
There exists a partition of the domain of ν into n sets of equal measure.
-/
open MeasureTheory ENNReal Set Metric Function

lemma exists_partition_measure_eq_ν (n : ℕ) (hn : n > 0) :
    ∃ (A : Fin n → Set (Icc (0 : ℝ) 1)),
      (∀ i, MeasurableSet (A i)) ∧
      (Pairwise (fun i j => Disjoint (A i) (A j))) ∧
      (∀ i, ν (A i) = (ν univ) / n) ∧
      (⋃ i, A i) =ᵐ[ν] univ := by
        -- Define the sets $A_i$ as the pullbacks of the intervals $[i/n, (i+1)/n)$ under the inclusion map.
        set A : Fin n → Set (Icc (0 : ℝ) 1) := fun i => {x : Icc (0 : ℝ) 1 | (i : ℝ) / n ≤ x.val ∧ x.val < ((i + 1) : ℝ) / n};
        refine' ⟨ A, _, _, _, _ ⟩;
        · exact fun i => MeasurableSet.inter ( measurableSet_le ( measurable_const.div_const _ ) ( measurable_subtype_coe ) ) ( measurableSet_lt ( measurable_subtype_coe ) ( measurable_const.div_const _ ) );
        · intro i j hij;
          refine' Set.disjoint_left.mpr fun x hx₁ hx₂ => _;
          exact hij ( Fin.ext <| Nat.le_antisymm ( Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2, show ( n : ℝ ) > 0 by positivity, mul_div_cancel₀ ( ( i : ℝ ) : ℝ ) ( by positivity : ( n : ℝ ) ≠ 0 ), mul_div_cancel₀ ( ( j : ℝ ) : ℝ ) ( by positivity : ( n : ℝ ) ≠ 0 ), mul_div_cancel₀ ( ( i + 1 : ℝ ) : ℝ ) ( by positivity : ( n : ℝ ) ≠ 0 ), mul_div_cancel₀ ( ( j + 1 : ℝ ) : ℝ ) ( by positivity : ( n : ℝ ) ≠ 0 ) ] ) ( Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2, show ( n : ℝ ) > 0 by positivity, mul_div_cancel₀ ( ( i : ℝ ) : ℝ ) ( by positivity : ( n : ℝ ) ≠ 0 ), mul_div_cancel₀ ( ( j : ℝ ) : ℝ ) ( by positivity : ( n : ℝ ) ≠ 0 ), mul_div_cancel₀ ( ( i + 1 : ℝ ) : ℝ ) ( by positivity : ( n : ℝ ) ≠ 0 ), mul_div_cancel₀ ( ( j + 1 : ℝ ) : ℝ ) ( by positivity : ( n : ℝ ) ≠ 0 ) ] ) );
        · -- For each $i$, the measure of $A_i$ is the length of the interval $[i/n, (i+1)/n)$, which is $1/n$.
          intro i
          have h_measure : ν (A i) = ENNReal.ofReal (1 / n) := by
            erw [ MeasureTheory.Measure.comap_apply ];
            · -- The image of $A_i$ under the inclusion map is the interval $[i/n, (i+1)/n)$.
              have h_image : Subtype.val '' A i = Set.Ico ((i : ℝ) / n) ((i + 1) / n) := by
                ext x;
                exact ⟨ fun ⟨ y, hy, hy' ⟩ => ⟨ hy'.symm ▸ hy.1, hy'.symm ▸ hy.2 ⟩, fun hx => ⟨ ⟨ x, ⟨ hx.1.trans' <| by positivity, hx.2.le.trans <| by rw [ div_le_iff₀ <| by positivity ] ; norm_cast; linarith [ Fin.is_lt i ] ⟩ ⟩, ⟨ hx.1, hx.2 ⟩, rfl ⟩ ⟩;
              rw [ h_image, Real.volume_Ico ] ; ring;
            · exact Subtype.coe_injective;
            · intro s hs;
              obtain ⟨ t, ht, rfl ⟩ := hs;
              erw [ show ( Subtype.val '' ( Subtype.val ⁻¹' t ) ) = t ∩ Set.Icc 0 1 by ext; aesop ] ; exact ht.inter ( measurableSet_Icc );
            · exact MeasurableSet.inter ( measurableSet_le ( measurable_const ) ( measurable_subtype_coe ) ) ( measurableSet_lt ( measurable_subtype_coe ) ( measurable_const ) );
          rw [ h_measure, show ν univ = 1 from ?_ ];
          · rw [ ENNReal.ofReal_div_of_pos ] <;> norm_num [ hn ];
          · erw [ MeasureTheory.Measure.comap_apply ] <;> norm_num [ ν ];
            · erw [ Real.volume_Icc ] ; norm_num;
            · intro s hs;
              obtain ⟨ t, ht, rfl ⟩ := hs;
              rw [ Set.image_preimage_eq_inter_range ];
              exact ht.inter ( by rw [ show ( range Subtype.val : Set ℝ ) = Set.Icc 0 1 by ext; aesop ] ; exact measurableSet_Icc );
        · rw [ MeasureTheory.ae_eq_univ ];
          refine' MeasureTheory.measure_mono_null _ ( MeasureTheory.measure_singleton 1 );
          intro x hx;
          contrapose! hx;
          simp +zetaDelta at *;
          refine' ⟨ ⟨ ⌊x.val * n⌋₊, _ ⟩, _, _ ⟩ <;> norm_num;
          · rw [ Nat.floor_lt ] <;> cases lt_or_gt_of_ne hx <;> nlinarith [ x.2.1, x.2.2, show ( n : ℝ ) ≥ 1 by norm_cast, show ( x : ℝ ) < 1 by exact lt_of_le_of_ne x.2.2 ( by aesop ) ];
          · exact div_le_iff₀ ( by positivity ) |>.2 ( Nat.floor_le ( by exact mul_nonneg x.2.1 ( Nat.cast_nonneg _ ) ) );
          · rw [ lt_div_iff₀ ] <;> norm_num <;> linarith [ Nat.lt_floor_add_one ( x.val * n ) ]

/-
The cumulative integral of |f|^p with respect to ν is continuous.
-/
open MeasureTheory ENNReal Set Metric Function Topology

lemma continuous_cumulative_lintegral {p : ℝ≥0∞} [Fact (0 < p)] [Fact (p < 1)]
    (f : Lp ℝ p ν) :
    Continuous (fun (t : Icc (0 : ℝ) 1) => ∫⁻ x in Ioc (0 : Icc (0 : ℝ) 1) t, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν) := by
      refine' continuous_iff_continuousAt.mpr _;
      intro x;
      refine' ContinuousAt.congr _ _;
      exact fun t => ∫⁻ x in Icc 0 1, ( if x ≤ t then ‖f x‖₊ ^ p.toReal else 0 ) ∂ν;
      · refine' MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence _ _ _ _ _;
        use fun a => ‖f a‖₊ ^ p.toReal;
        · refine' Filter.Eventually.of_forall fun n => Measurable.ite _ _ _ <;> norm_num;
          · exact measurableSet_Iic.mem;
          · fun_prop;
        · exact Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun a => by split_ifs <;> simp +decide [ * ] ;
        · have := f.2;
          rw [ MeasureTheory.Lp.mem_Lp_iff_eLpNorm_lt_top ] at this;
          rw [ eLpNorm_eq_lintegral_rpow_enorm ] at this;
          · contrapose! this;
            rw [ MeasureTheory.lintegral_congr_ae ];
            rotate_right;
            use fun a => ‖f a‖₊ ^ p.toReal;
            · rw [ MeasureTheory.Measure.restrict_eq_self_of_ae_mem ] at this;
              · rw [ this ];
                rw [ ENNReal.top_rpow_of_pos ];
                exact one_div_pos.mpr ( ENNReal.toReal_pos ( ne_of_gt ( Fact.out ( p := 0 < p ) ) ) ( ne_of_lt ( Fact.out ( p := p < 1 ) |> lt_of_lt_of_le <| by norm_num ) ) );
              · exact Filter.Eventually.of_forall fun x => x.2;
            · filter_upwards [ ] with x using by norm_cast;
          · exact ne_of_gt Fact.out;
          · exact ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) );
        · refine' MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton x ) |> fun h => h.mono fun a ha => _;
          by_cases ha' : a ≤ x <;> simp_all +decide [ Filter.Tendsto ];
          · exact tendsto_const_nhds.congr' ( by filter_upwards [ Ici_mem_nhds ( show x > a from lt_of_le_of_ne ha' ha ) ] with n hn; aesop );
          · rw [ if_neg ha'.not_le ];
            refine' tendsto_const_nhds.congr' _;
            filter_upwards [ Iio_mem_nhds ha' ] with n hn using by rw [ if_neg hn.out.not_le ];
      · filter_upwards [ ] with t;
        rw [ ← MeasureTheory.lintegral_indicator, ← MeasureTheory.lintegral_indicator ];
        · rw [ MeasureTheory.lintegral_congr_ae ];
          filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton 0 ) ] with x hx;
          simp_all +decide [ Set.indicator ];
          split_ifs <;> simp_all +decide [ le_of_lt ];
          exact False.elim <| ‹1 < x›.not_le <| x.2.2;
        · exact measurableSet_Ioc;
        · exact measurableSet_Icc

/-
For any y between 0 and the total integral of |f|^p, there exists a t such that the integral up to t is y.
-/
open MeasureTheory ENNReal Set Metric Function Topology

lemma exists_integral_eq_of_continuous {p : ℝ≥0∞} [Fact (0 < p)] [Fact (p < 1)]
    (f : Lp ℝ p ν) (y : ℝ) (hy_nonneg : 0 ≤ y)
    (hy_le : y ≤ (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν).toReal) :
    ∃ t : Icc (0 : ℝ) 1, (∫⁻ x in Ioc (0 : Icc (0 : ℝ) 1) t, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν).toReal = y := by
      have h_cont : Continuous (fun t : Icc (0 : ℝ) 1 => ∫⁻ x in Ioc (0 : Icc (0 : ℝ) 1) t, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν) := by
        exact?;
      have h_image : IsConnected (Set.range (fun t : Icc (0 : ℝ) 1 => (∫⁻ x in Ioc (0 : Icc (0 : ℝ) 1) t, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν).toReal)) := by
        apply_rules [ isConnected_range, continuous_iff_continuousAt.mpr ];
        intro t;
        refine' ENNReal.continuousAt_toReal _ |> ContinuousAt.comp <| h_cont.continuousAt;
        refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.setLIntegral_le_lintegral _ _ ) _ );
        convert f.2;
        rw [ MeasureTheory.Lp.mem_Lp_iff_eLpNorm_lt_top ];
        rw [ MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm ];
        · simp +decide [ ENNReal.rpow_lt_top_of_nonneg, Real.toNNReal_of_nonneg, Real.rpow_nonneg, ENNReal.toReal_pos_iff ];
          rw [ ENNReal.rpow_inv_lt_iff ];
          · rw [ ENNReal.top_rpow_of_pos ];
            · rfl;
            · exact ENNReal.toReal_pos ( ne_of_gt ( Fact.out ( p := 0 < p ) ) ) ( ne_of_lt ( lt_of_lt_of_le ( Fact.out ( p := p < 1 ) ) ( by norm_num ) ) );
          · exact ENNReal.toReal_pos ( ne_of_gt ( Fact.out ( p := 0 < p ) ) ) ( ne_of_lt ( lt_of_lt_of_le ( Fact.out ( p := p < 1 ) ) ( by norm_num ) ) );
        · exact ne_of_gt Fact.out;
        · exact ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) );
      refine' h_image.Icc_subset _ _ ⟨ hy_nonneg, hy_le ⟩;
      · use 0; simp;
      · use 1;
        simp +decide [ MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc ];
        rw [ MeasureTheory.Measure.restrict_eq_self_of_ae_mem ];
        exact Filter.Eventually.of_forall fun x => x.2

/-
If f is monotone and f ∘ t is strictly monotone, then t is strictly monotone (for linear orders).
-/
lemma strictMono_of_monotone_of_strictMono_image {α β : Type*} [LinearOrder α] [Preorder β]
    {f : α → β} (hf : Monotone f) {n : ℕ} {t : Fin n → α} (ht : StrictMono (f ∘ t)) :
    StrictMono t := by
      exact fun i j hij => lt_of_not_ge fun h => ht hij |> not_le_of_gt <| hf h

#check StrongDual

#check convexHull

variable {p : ℝ≥0∞} [Fact (0 < p)] [Fact (p < 1)]
#synth Lattice (Lp ℝ p ν)
#check Disjoint
#check Function.support

open MeasureTheory

#check MemLp.toLp
#check MemLp.indicator

open MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
variable (f : α →ₘ[μ] E)

#check f
#check (f : α → E)
#synth CoeFun (α →ₘ[μ] E) (fun _ => α → E)

#print MeasureTheory.AEEqFun

/-
Definition of Lp restriction and its distance property.
-/
open MeasureTheory ENNReal Set Metric Function Topology

variable {p : ℝ≥0∞} [Fact (0 < p)] [Fact (p < 1)]

noncomputable def Lp.restrict (f : Lp ℝ p ν) (s : Set (Icc (0 : ℝ) 1)) (hs : MeasurableSet s) : Lp ℝ p ν :=
  (MemLp.indicator hs (Lp.memLp f)).toLp (s.indicator f)

lemma Lp.restrict_dist (f : Lp ℝ p ν) (s : Set (Icc (0 : ℝ) 1)) (hs : MeasurableSet s) :
    dist (Lp.restrict f s hs) 0 = (∫⁻ x in s, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν).toReal := by
      -- By definition of distance, we have:
      have h_dist_def : dist (restrict f s hs) 0 = (eLpNorm (restrict f s hs) p ν).toReal ^ p.toReal := by
        unfold instDistLpOfLtOne; aesop;
      have h_eLpNorm : eLpNorm (restrict f s hs) p ν = (∫⁻ x, (‖(restrict f s hs) x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν) ^ (1 / p.toReal) := by
        rw [ eLpNorm_eq_lintegral_rpow_enorm ] ; aesop;
        · exact ne_of_gt Fact.out;
        · exact ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) );
      simp_all +decide [ restrict ];
      rw [ MeasureTheory.lintegral_congr_ae ];
      any_goals exact fun x => if x ∈ s then ‖f x‖₊ ^ p.toReal else 0;
      · rw [ ← ENNReal.toReal_rpow ];
        rw [ ← Real.rpow_mul, inv_mul_cancel₀ ( ne_of_gt ( show 0 < p.toReal from _ ) ), Real.rpow_one ];
        · rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
          exact hs;
        · exact ENNReal.toReal_pos ( ne_of_gt ( Fact.out : 0 < p ) ) ( ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) ) );
        · positivity;
      · filter_upwards [ MeasureTheory.MemLp.coeFn_toLp ( show MemLp ( s.indicator ( f : Icc ( 0 : ℝ ) 1 → ℝ ) ) p ν from by
                                                            refine' MemLp.indicator _ _;
                                                            · exact hs;
                                                            · exact Lp.memLp _ ) ] with x hx
        generalize_proofs at *;
        split_ifs <;> simp_all +decide [ Set.indicator ];
        exact ENNReal.toReal_pos ( ne_of_gt ( Fact.out : 0 < p ) ) ( ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) ) )

/-
For any $f \in L^p$ and ratio $r \in [0,1]$, we can split $f$ into $g+h$ such that $\|g\|_p^p = r \|f\|_p^p$ and $\|h\|_p^p = (1-r) \|f\|_p^p$.
-/
open MeasureTheory ENNReal Set Metric Function Topology

variable {p : ℝ≥0∞} [Fact (0 < p)] [Fact (p < 1)]

lemma exists_split_norm_ratio (f : Lp ℝ p ν) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ g h : Lp ℝ p ν, f = g + h ∧
      dist g 0 = r * dist f 0 ∧
      dist h 0 = (1 - r) * dist f 0 := by
        -- Use `exists_integral_eq_of_continuous` to find $t$ such that $\int_0^t |f|^p = r \int_0^1 |f|^p$.
        obtain ⟨t, ht⟩ : ∃ t : Icc (0 : ℝ) 1, (∫⁻ x in Ioc (0 : Icc (0 : ℝ) 1) t, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν).toReal = r * (∫⁻ x in Set.univ, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν).toReal := by
          apply exists_integral_eq_of_continuous;
          · positivity;
          · norm_num +zetaDelta at *;
            exact mul_le_of_le_one_left ( ENNReal.toReal_nonneg ) hr1;
        refine' ⟨ Lp.restrict f ( Ioc 0 t ) ( measurableSet_Ioc ), Lp.restrict f ( Set.univ \ Ioc 0 t ) ( MeasurableSet.univ.diff ( measurableSet_Ioc ) ), _, _, _ ⟩;
        · unfold Lp.restrict;
          rw [ eq_comm, ← MemLp.toLp_add ];
          simp +decide [ Set.indicator_apply, Set.diff_eq ];
        · convert ht using 1;
          · exact?;
          · unfold dist;
            unfold instDistLpOfLtOne;
            simp +decide [ eLpNorm ];
            split_ifs <;> simp_all +decide [ eLpNorm', ENNReal.toReal_ofReal ];
            rw [ ← ENNReal.toReal_rpow ];
            rw [ ← Real.rpow_mul ( ENNReal.toReal_nonneg ), inv_mul_cancel₀ ( ne_of_gt ( ENNReal.toReal_pos ( by aesop ) ( by aesop ) ) ), Real.rpow_one ] ; aesop;
        · rw [ Lp.restrict_dist, mul_comm ];
          -- Use the fact that the integral over the complement of $Ioc 0 t$ is the total integral minus the integral over $Ioc 0 t$.
          have h_complement : (∫⁻ x in Set.univ \ Ioc 0 t, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν).toReal = (∫⁻ x in Set.univ, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν).toReal - (∫⁻ x in Ioc 0 t, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν).toReal := by
            rw [ ← ENNReal.toReal_sub_of_le ];
            · simp +zetaDelta at *;
              rw [ ← MeasureTheory.lintegral_indicator ];
              · rw [ ← MeasureTheory.lintegral_indicator ];
                · rw [ ← MeasureTheory.lintegral_sub ];
                  · congr with x ; by_cases hx : x ∈ Ioc 0 t <;> simp +decide [ hx ];
                  · refine' Measurable.indicator _ _;
                    · have h_measurable : Measurable (fun x => ‖f x‖₊) := by
                        have h_measurable : Measurable (fun x => f x) := by
                          exact f.1.measurable
                        exact h_measurable.nnnorm;
                      exact Measurable.pow_const ( by measurability ) _;
                    · exact measurableSet_Ioc;
                  · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun x => _ ) _ );
                    use fun x => ‖f x‖₊ ^ p.toReal;
                    · by_cases hx : x ∈ Ioc 0 t <;> simp +decide [ hx ];
                    · convert f.2;
                      rw [ Lp.mem_Lp_iff_eLpNorm_lt_top ];
                      rw [ eLpNorm_eq_lintegral_rpow_enorm ];
                      · simp +decide [ ENNReal.rpow_eq_top_iff ];
                        rw [ ENNReal.rpow_lt_top_iff_of_pos ];
                        · norm_num [ ← ENNReal.ofReal_coe_nnreal ];
                          norm_num [ ENNReal.ofReal, Real.enorm_eq_ofReal_abs ];
                        · exact inv_pos.mpr ( ENNReal.toReal_pos ( ne_of_gt ( Fact.out ( p := 0 < p ) ) ) ( ne_of_lt ( Fact.out ( p := p < 1 ) |> lt_of_lt_of_le <| by norm_num ) ) );
                      · exact ne_of_gt Fact.out;
                      · exact ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) );
                  · filter_upwards [ ] with x using by rw [ Set.indicator_apply ] ; aesop;
                · exact measurableSet_Ioc;
              · exact MeasurableSet.univ.diff ( measurableSet_Ioc );
            · exact MeasureTheory.lintegral_mono_set ( Set.subset_univ _ );
            · have := Lp.memLp f;
              have := this.2;
              rw [ MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm ] at this;
              · simp_all +decide [ ENNReal.rpow_eq_top_iff ];
                contrapose! this;
                rw [ show ( ∫⁻ x : Icc ( 0 : ℝ ) 1, ‖f x‖ₑ ^ p.toReal ∂ν ) = ⊤ from ?_ ];
                · field_simp;
                  rw [ ENNReal.top_rpow_of_pos ];
                  exact one_div_pos.mpr ( ENNReal.toReal_pos ( ne_of_gt ( Fact.out ( p := 0 < p ) ) ) ( ne_of_lt ( Fact.out ( p := p < 1 ) |> lt_of_lt_of_le <| by norm_num ) ) );
                · convert this using 1;
              · exact ne_of_gt Fact.out;
              · exact ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) );
          rw [ h_complement, ht ] ; ring;
          rw [ show dist f 0 = ( ∫⁻ x in Set.univ, ( ‖f x‖₊ : ℝ≥0∞ ) ^ p.toReal ∂ν |> ENNReal.toReal ) from ?_ ] ; ring;
          convert Lp.restrict_dist f Set.univ MeasurableSet.univ;
          ext; simp [Lp.restrict]

/-
Any continuous linear functional on $L^p$ ($0< p<1$) is bounded by $C \|f\|_p$.
-/
open MeasureTheory ENNReal Set Metric Function Topology

variable {p : ℝ≥0∞} [Fact (0 < p)] [Fact (p < 1)]

lemma continuous_functional_bounded (phi : Lp ℝ p ν →L[ℝ] ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ p ν, |phi f| ≤ C * (dist f 0) ^ (1 / p.toReal) := by
      -- Since $\phi$ is continuous at 0, there exists $\delta > 0$ such that $\|f\|_p^p < \delta \implies |\phi(f)| < 1$.
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ f : Lp ℝ p ν, dist f 0 < δ → |phi f| < 1 := by
        simpa using Metric.continuous_iff.mp phi.continuous 0 1 zero_lt_one;
      -- Let $C = (2/\delta)^{1/p}$.
      use (2 / δ) ^ (1 / p.toReal);
      -- For any $f \neq 0$, let $c = \left(\frac{\delta}{2 \|f\|_p^p}\right)^{1/p}$.
      have h_c : ∀ (f : Lp ℝ p ν), f ≠ 0 → |phi f| < (2 / δ) ^ (1 / p.toReal) * dist f 0 ^ (1 / p.toReal) := by
        intro f hf_nonzero
        set c := (δ / (2 * dist f 0)) ^ (1 / p.toReal) with hc_def;
        -- Then $\|c f\|_p^p = c^p \|f\|_p^p = \delta/2 < \delta$.
        have h_c_f_norm : dist (c • f) 0 < δ := by
          have h_c_f_norm : dist (c • f) 0 = c ^ p.toReal * dist f 0 := by
            have h_c_f_norm : dist (c • f) 0 = |c| ^ p.toReal * dist f 0 := by
              convert dist_smul_eq_mul_dist p c f using 1;
            rw [ h_c_f_norm, abs_of_nonneg ( Real.rpow_nonneg ( div_nonneg hδ_pos.le ( mul_nonneg zero_le_two ( dist_nonneg ) ) ) _ ) ];
          rw [ h_c_f_norm, ← Real.rpow_mul, one_div_mul_cancel, Real.rpow_one ];
          · rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> nlinarith [ show 0 < dist f 0 from dist_pos.mpr hf_nonzero ];
          · exact ne_of_gt <| ENNReal.toReal_pos ( ne_of_gt <| Fact.out ) ( ne_of_lt <| lt_of_lt_of_le ( Fact.out : p < 1 ) <| by norm_num );
          · positivity;
        have := hδ ( c • f ) h_c_f_norm; simp_all +decide [ abs_mul, abs_div, abs_of_pos ] ;
        rw [ abs_of_nonneg ( Real.rpow_nonneg ( div_nonneg hδ_pos.le ( mul_nonneg zero_le_two ( dist_nonneg ) ) ) _ ) ] at this;
        rw [ Real.div_rpow ( by positivity ) ( by positivity ) ] at *;
        rw [ div_mul_eq_mul_div, div_lt_iff₀ ] at *;
        · rw [ lt_div_iff₀ ( by positivity ) ];
          rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] at this ; linarith;
        · exact Real.rpow_pos_of_pos ( mul_pos zero_lt_two ( dist_pos.mpr hf_nonzero ) ) _;
      exact ⟨ by positivity, fun f => if hf : f = 0 then by simpa [ hf ] using by positivity else le_of_lt ( h_c f hf ) ⟩

/-
We can decompose any $f \in L^p$ into a sum of $n$ functions with disjoint supports and equal $p$-norms.
-/
open MeasureTheory ENNReal Set Metric Function Topology

variable {p : ℝ≥0∞} [Fact (0 < p)] [Fact (p < 1)]

lemma exists_decomposition_norm_eq (f : Lp ℝ p ν) (n : ℕ) (hn : n > 0) :
    ∃ g : Fin n → Lp ℝ p ν, f = ∑ i, g i ∧ ∀ i, dist (g i) 0 = (n : ℝ)⁻¹ * dist f 0 := by
      by_cases h : f = 0;
      · refine' ⟨ fun _ => 0, _, _ ⟩ <;> aesop;
      · -- By induction on $n$, we can split $f$ into $n$ parts with equal norm.
        have h_split : ∀ n : ℕ, n > 0 → ∀ f : Lp ℝ p ν, f ≠ 0 → ∃ g : Fin n → Lp ℝ p ν, f = ∑ i, g i ∧ ∀ i, dist (g i) 0 = (1 / n : ℝ) * dist f 0 := by
          intro n hn f hf
          induction' n with n ih generalizing f;
          · contradiction;
          · -- By the induction hypothesis, we can split $f$ into $n$ parts with equal norm.
            obtain ⟨g, hg⟩ : ∃ g : Lp ℝ p ν, dist g 0 = (n / (n + 1) : ℝ) * dist f 0 ∧ dist (f - g) 0 = (1 / (n + 1) : ℝ) * dist f 0 := by
              have := exists_split_norm_ratio f ( n / ( n + 1 ) ) ( by positivity ) ( by rw [ div_le_iff₀ ] <;> linarith );
              obtain ⟨ g, h, rfl, hg, hh ⟩ := this; exact ⟨ g, hg, by rw [ show ( g + h - g : Lp ℝ p ν ) = h by simp +decide ] ; rw [ hh ] ; rw [ one_sub_div ( by positivity ) ] ; ring ⟩ ;
            by_cases hn : n = 0;
            · exact ⟨ fun _ => f, by simp +decide [ hn ], by simp +decide [ hn ] ⟩;
            · obtain ⟨ g', hg' ⟩ := ih ( Nat.pos_of_ne_zero hn ) g ( by
                intro hg'; simp_all +decide [ dist_eq_norm ] ; );
              use Fin.cons (f - g) g';
              simp_all +decide [ Fin.sum_univ_succ ];
              intro i; induction i using Fin.inductionOn <;> simp_all +decide [ Fin.cons ] ;
              field_simp;
        simpa using h_split n hn f h

/-
The dual space of $L^p$ is zero for $0 < p < 1$.
-/
open MeasureTheory ENNReal Set Metric Function Topology

theorem Lp_dual_zero (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] :
    ∀ (f : Lp ℝ p ν →L[ℝ] ℝ), f = 0 := by
      -- By `continuous_functional_bounded`, there exists $C$ such that $|\phi(h)| \le C \|h\|_p$ for all $h$.
      intro phi
      obtain ⟨C, hC_pos, hC_bound⟩ : ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ p ν, |phi f| ≤ C * (dist f 0) ^ (1 / p.toReal) := by
        exact?;
      -- Fix an arbitrary $f \in L^p$.
      have h_zero (f : Lp ℝ p ν) : phi f = 0 := by
        -- For any $n$, decompose $f = \sum_{i=1}^n g_i$ with $\|g_i\|_p^p = \frac{1}{n} \|f\|_p^p$.
        have h_decomp : ∀ n : ℕ, n > 0 → ∃ g : Fin n → Lp ℝ p ν, f = ∑ i, g i ∧ ∀ i, dist (g i) 0 = (n : ℝ)⁻¹ * dist f 0 := by
          exact?;
        -- By the linearity of $\phi$, we have $|\phi(f)| \leq \sum_{i=1}^n |\phi(g_i)| \leq \sum_{i=1}^n C \|g_i\|_p = \sum_{i=1}^n C n^{-1/p} \|f\|_p = C n^{1-1/p} \|f\|_p$.
        have h_sum_bound (n : ℕ) (hn : n > 0) : |phi f| ≤ C * (n : ℝ) ^ (1 - 1 / p.toReal) * (dist f 0) ^ (1 / p.toReal) := by
          obtain ⟨ g, rfl, hg ⟩ := h_decomp n hn;
          have h_sum_bound : |phi (∑ i, g i)| ≤ ∑ i, |phi (g i)| := by
            simpa only [ map_sum ] using Finset.abs_sum_le_sum_abs _ _;
          refine le_trans h_sum_bound <| le_trans ( Finset.sum_le_sum fun i _ => hC_bound _ ) ?_;
          simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
          rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.inv_rpow ( by positivity ), Real.rpow_sub ( by positivity ), Real.rpow_one ] ; ring_nf ; norm_num [ hn.ne' ];
        -- Since $p < 1$, $1 - 1/p < 0$, so as $n \to \infty$, $n^{1-1/p} \to 0$.
        have h_lim_zero : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - 1 / p.toReal)) Filter.atTop (nhds 0) := by
          convert tendsto_rpow_neg_atTop ( show 0 < - ( 1 - 1 / p.toReal ) from neg_pos_of_neg <| sub_neg_of_lt <| one_lt_one_div ?_ ?_ ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop using 2 ; norm_num;
          · exact ENNReal.toReal_pos ( ne_of_gt ( Fact.out : 0 < p ) ) ( ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) ) );
          · exact ENNReal.toReal_lt_of_lt_ofReal ( by norm_num; exact Fact.out );
        -- Taking the limit as $n \to \infty$, we get $|\phi(f)| \leq 0$, which implies $\phi(f) = 0$.
        have h_lim_zero : Filter.Tendsto (fun n : ℕ => C * (n : ℝ) ^ (1 - 1 / p.toReal) * (dist f 0) ^ (1 / p.toReal)) Filter.atTop (nhds 0) := by
          simpa using Filter.Tendsto.mul ( h_lim_zero.const_mul C ) tendsto_const_nhds;
        exact tendsto_nhds_unique ( tendsto_const_nhds ) ( squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun n hn => by simpa using h_sum_bound n hn ⟩ ) h_lim_zero );
      exact ContinuousLinearMap.ext h_zero

/-
For every $0< p<1$, the space $L^{p}([0,1])$ is not Bolognese.
-/
open MeasureTheory ENNReal Set Metric Function Topology

theorem L_p_not_bolognese (p : ℝ≥0∞) [Fact (0 < p)] [Fact (p < 1)] :
    ¬ Bolognese (Lp ℝ p ν) := by
      -- Assume for contradiction that $L^p$ is Bolognese.
      by_contra h_bolognese;
      -- Since $L^p$ is Bolognese, its dual space is non-trivial.
      have h_dual_nontrivial : ∃ phi : Lp ℝ p ν →L[ℝ] ℝ, phi ≠ 0 := by
        -- Since $L^p$ is Bolognese, its dual space is non-trivial. Use this fact.
        have h_dual_nontrivial : ∀ (v w : Lp ℝ p ν), v ≠ w → ∃ phi : Lp ℝ p ν →L[ℝ] ℝ, phi v ≠ phi w := by
          intro v w hvw;
          apply_rules [ separates_dual_of_bolognese ];
        by_cases h : ∃ v : Lp ℝ p ν, v ≠ 0;
        · obtain ⟨ v, hv ⟩ := h; obtain ⟨ phi, hphi ⟩ := h_dual_nontrivial v 0 hv; use phi; aesop;
        · -- Since $L^p$ is not the zero space, there must exist a non-zero element in $L^p$.
          obtain ⟨f, hf⟩ : ∃ f : Lp ℝ p ν, f ≠ 0 := by
            refine' ⟨ _, _ ⟩;
            refine' ⟨ _, _ ⟩;
            exact MeasureTheory.AEEqFun.mk ( fun _ => 1 ) ( by exact MeasureTheory.aestronglyMeasurable_const );
            simp +decide [ Lp.mem_Lp_iff_eLpNorm_lt_top ];
            simp +decide [ eLpNorm ];
            split_ifs <;> simp_all +decide [ eLpNorm' ];
            any_goals simp_all +decide [ Fact.out ( p := 0 < p ), Fact.out ( p := p < 1 ) ];
            · exact absurd ‹_› ( ne_of_lt ( lt_of_lt_of_le ( Fact.out : p < 1 ) ( by norm_num ) ) );
            · refine' ENNReal.rpow_lt_top_of_nonneg _ _;
              · positivity;
              · unfold ν;
                simp +decide [ Measure.comap ];
                split_ifs <;> simp_all +decide [ MeasureTheory.Measure.restrict_apply ];
                erw [ Real.volume_Icc ] ; norm_num;
            · erw [ AEEqFun.mk_eq_mk ];
              rw [ Filter.EventuallyEq, MeasureTheory.ae_iff ] ; norm_num;
              unfold ν;
              rw [ MeasureTheory.Measure.ext_iff ] ; norm_num;
              refine' ⟨ Set.univ, MeasurableSet.univ, _ ⟩ ; norm_num [ MeasureTheory.Measure.comap ];
              refine' ⟨ _, _ ⟩;
              · intro s hs;
                refine' MeasurableSet.nullMeasurableSet _;
                obtain ⟨ t, ht, rfl ⟩ := hs;
                rw [ Set.image_preimage_eq_inter_range ];
                exact ht.inter ( by rw [ show range Subtype.val = Set.Icc ( 0 : ℝ ) 1 from Set.ext fun x => by aesop ] ; exact measurableSet_Icc );
              · intro H; have := congr_arg ( fun f => f ( Set.univ : Set ( Icc ( 0 : ℝ ) 1 ) ) ) H; norm_num at this;
                erw [ Real.volume_Icc ] at this ; norm_num at this;
          exact False.elim <| h ⟨ f, hf ⟩;
      exact h_dual_nontrivial.elim fun phi hphi => hphi <| Lp_dual_zero p phi

#check lp.single
#check lp.norm_single
