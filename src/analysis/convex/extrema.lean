/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.calculus.local_extr
import topology.algebra.affine

/-!
# Minima and maxima of convex functions

We show that if a function `f : E → ℝ` is convex, then a local minimum is also
a global minimum.
-/

universes u

variables {E : Type u} [add_comm_group E] [topological_space E]
  [module ℝ E] [topological_add_group E] [topological_vector_space ℝ E]
  {s : set E}

open set filter
open_locale classical

/--
Helper lemma for the more general case: `is_min_on.of_is_local_min_on_of_convex_on`.
-/
lemma is_min_on.of_is_local_min_on_of_convex_on_Icc {f : ℝ → ℝ} {a b : ℝ}
  (a_lt_b : a < b) (h_local_min : is_local_min_on f (Icc a b) a) (h_conv : convex_on (Icc a b) f) :
  ∀ x ∈ Icc a b, f a ≤ f x :=
begin
  by_contradiction H_cont,
  push_neg at H_cont,
  rcases H_cont with ⟨x, ⟨h_ax, h_xb⟩, fx_lt_fa⟩,
  obtain ⟨z, hz, ge_on_nhd⟩ : ∃ z > a, ∀ y ∈ (Icc a z), f y ≥ f a,
  { rcases eventually_iff_exists_mem.mp h_local_min with ⟨U, U_in_nhds_within, fy_ge_fa⟩,
    rw [nhds_within_Icc_eq_nhds_within_Ici a_lt_b, mem_nhds_within_Ici_iff_exists_Icc_subset]
        at U_in_nhds_within,
    rcases U_in_nhds_within with ⟨ε, ε_in_Ioi, Ioc_in_U⟩,
    exact ⟨ε, mem_Ioi.mp ε_in_Ioi, λ y y_in_Ioc, fy_ge_fa y $ Ioc_in_U y_in_Ioc⟩ },
  have a_lt_x : a < x := lt_of_le_of_ne h_ax (λ H, by subst H ; linarith),
  have lt_on_nhd : ∀ y ∈ Ioc a x, f y < f a,
  { intros y y_in_Ioc,
    rcases (convex.mem_Ioc a_lt_x).mp y_in_Ioc with ⟨ya, yx, ya_pos, yx_pos, yax, y_combo⟩,
    calc
      f y = f (ya * a + yx * x)       : by rw [y_combo]
      ... ≤ ya * f a + yx * f x
                : h_conv.2 (left_mem_Icc.mpr (le_of_lt a_lt_b)) ⟨h_ax, h_xb⟩ (ya_pos)
                    (le_of_lt yx_pos) yax
      ... < ya * f a + yx * f a       : by linarith [(mul_lt_mul_left yx_pos).mpr fx_lt_fa]
      ... = f a                       : by rw [←add_mul, yax, one_mul] },
  by_cases h_xz : x ≤ z,
  { linarith [ge_on_nhd x (show x ∈ Icc a z, by exact ⟨h_ax, h_xz⟩)] },
  { have h₁ : z ∈ Ioc a x := ⟨hz, le_of_not_ge h_xz⟩,
    have h₂ : z ∈ Icc a z := ⟨le_of_lt hz, le_refl z⟩,
    linarith [lt_on_nhd z h₁, ge_on_nhd z h₂] }
end

/--
A local minimum of a convex function is a global minimum, restricted to a set `s`.
-/
lemma is_min_on.of_is_local_min_on_of_convex_on {f : E → ℝ} {a : E}
  (a_in_s : a ∈ s) (h_localmin: is_local_min_on f s a) (h_conv : convex_on s f) :
  ∀ x ∈ s, f a ≤ f x :=
begin
  by_contradiction H_cont,
  push_neg at H_cont,
  rcases H_cont with ⟨x, ⟨x_in_s, fx_lt_fa⟩⟩,
  let g : affine_map ℝ ℝ ℝ E E := affine_map.line_map a (x - a),
  have hg0 : g 0 = a := affine_map.line_map_apply_zero a (x - a),
  have hg1 : g 1 = x := by simp [affine_map.line_map_apply, one_smul],
  have fg_local_min_on : is_local_min_on (f ∘ g) (g ⁻¹' s) 0,
  { rw ←hg0 at h_localmin,
    refine is_local_min_on.comp_continuous_on h_localmin subset.rfl
      (continuous.continuous_on (affine_map.line_map_continuous)) _,
    simp [mem_preimage, hg0, a_in_s] },
  have fg_min_on : ∀ x ∈ (Icc 0 1 : set ℝ), (f ∘ g) 0 ≤ (f ∘ g) x,
  { have Icc_in_s' : Icc 0 1 ⊆ (g ⁻¹' s),
    { have h0 : (0 : ℝ) ∈ (g ⁻¹' s) := by simp [mem_preimage, a_in_s],
      have h1 : (1 : ℝ) ∈ (g ⁻¹' s) := by simp [mem_preimage, hg1, x_in_s],
      rw ←segment_eq_Icc (show (0 : ℝ) ≤ 1, by linarith),
      exact (convex.affine_preimage g h_conv.1).segment_subset
        (by simp [mem_preimage, hg0, a_in_s]) (by simp [mem_preimage, hg1, x_in_s]) },
    have fg_local_min_on' : is_local_min_on (f ∘ g) (Icc 0 1) 0 :=
      is_local_min_on.on_subset fg_local_min_on Icc_in_s',
    refine is_min_on.of_is_local_min_on_of_convex_on_Icc (by linarith) fg_local_min_on' _,
    exact (convex_on.comp_affine_map g h_conv).subset Icc_in_s' (convex_Icc 0 1) },
  have gx_lt_ga : (f ∘ g) 1 < (f ∘ g) 0 := by simp [hg1, fx_lt_fa, hg0],
  linarith [fg_min_on 1 (mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩)],
end

/-- A local minimum of a convex function is a global minimum. -/
lemma is_min_on.of_is_local_min_of_convex_univ {f : E → ℝ} {a : E}
  (h_local_min : is_local_min f a) (h_conv : convex_on univ f) : ∀ x, f a ≤ f x :=
λ x, (is_min_on.of_is_local_min_on_of_convex_on (mem_univ a)
        (is_local_min.on h_local_min univ) h_conv) x (mem_univ x)
