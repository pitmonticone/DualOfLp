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
