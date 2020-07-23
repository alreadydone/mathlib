/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.mv_polynomial
import ring_theory.ideals
import ring_theory.ideal_operations
import ring_theory.jacobson_ideal

/-!
# Jacobson Rings

The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its jacobson radical

Any ring satisfying any of these equivalent conditions is said to be Jacobson.

## Main definitions

Let `R` be a commutative ring. Jacobson Rings are defined using the first of the above conditions

* `is_jacobson R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.radical = I` implies `I.jacobson = I`.

## Main statements

* `is_jacobson_iff_prime_eq` is the equivalence between conditions 1 and 3 above.

* `is_jacobson_iff_Inf_maximal` is the equivalence between conditions 1 and 2 above.

## Tags

Jacobson, Jacobson Ring

-/

universes u v

namespace ideal
section is_jacobson
variables {R : Type u} [comm_ring R] {I : ideal R}
variables {S : Type v} [comm_ring S]

/-- A ring is a Jacobson ring if for every radical ideal `I`,
 the Jacobson radical of `I` is equal to `I`.
 See `is_jacobson_iff_prime_eq` and `is_jacobson_iff_Inf_maximal` for equivalent definitions. -/
@[class] def is_jacobson (R : Type u) [comm_ring R] :=
    ∀ (I : ideal R), I.radical = I → I.jacobson = I

/--  A ring is a Jacobson ring if and only if for all prime ideals `P`,
 the Jacobson radical of `P` is equal to `P`. -/
lemma is_jacobson_iff_prime_eq : is_jacobson R ↔ ∀ P : ideal R, is_prime P → P.jacobson = P :=
begin
  split,
  { exact λ h I hI, h I (is_prime.radical hI) },
  { refine λ h I hI, le_antisymm (λ x hx, _) (λ x hx, mem_Inf.mpr (λ _ hJ, hJ.left hx)),
    erw mem_Inf at hx,
    rw [← hI, radical_eq_Inf I, mem_Inf],
    intros P hP,
    rw set.mem_set_of_eq at hP,
    erw [← h P hP.right, mem_Inf],
    exact λ J hJ, hx ⟨le_trans hP.left hJ.left, hJ.right⟩ }
end

/-- A ring `R` is Jacobson if and only if for every radical ideal `I`,
 `I` can be written as the infimum of some collection of maximal ideals. -/
lemma is_jacobson_iff_Inf_maximal : is_jacobson R ↔
  ∀ {I : ideal R}, I.is_prime → ∃ M ⊆ {J : ideal R | J.is_maximal ∨ J = ⊤}, I = Inf M :=
⟨λ H I h, eq_jacobson_iff_Inf_maximal.1 (H _ (is_prime.radical h)),
  λ H , is_jacobson_iff_prime_eq.2 (λ P hP, eq_jacobson_iff_Inf_maximal.2 (H hP))⟩

lemma radical_eq_jacobson (H : is_jacobson R) (I : ideal R) : I.radical = I.jacobson :=
le_antisymm (le_Inf (λ J ⟨hJ, hJ_max⟩, (is_prime.radical_le_iff hJ_max.is_prime).mpr hJ))
            ((H I.radical (radical_idem I)) ▸ (jacobson_mono le_radical))

/-- Fields have only two ideals, and the condition holds for both of them -/
@[priority 100]
instance is_jacobson_field {K : Type u} [field K] : is_jacobson K :=
λ I hI, or.rec_on (eq_bot_or_top I)
(λ h, le_antisymm
  (Inf_le ⟨le_of_eq rfl, (eq.symm h) ▸ bot_is_maximal⟩)
  ((eq.symm h) ▸ bot_le))
(λ h, by rw [h, jacobson_eq_top_iff])

theorem is_jacobson_of_surjective [H : is_jacobson R] :
  (∃ (f : R →+* S), function.surjective f) → is_jacobson S :=
begin
  rintros ⟨f, hf⟩,
  rw is_jacobson_iff_Inf_maximal,
  intros p hp,
  use map f '' {J : ideal R | comap f p ≤ J ∧ J.is_maximal },
  use λ j ⟨J, hJ, hmap⟩, hmap ▸ or.symm (map_eq_top_or_is_maximal_of_surjective f hf hJ.right),
  have : p = map f ((comap f p).jacobson),
  from (H (comap f p) (by rw [← comap_radical, is_prime.radical hp])).symm
    ▸ (map_comap_of_surjective f hf p).symm,
  exact eq.trans this (map_Inf hf (λ J ⟨hJ, _⟩, le_trans (ideal.ker_le_comap f) hJ)),
end

@[priority 100]
instance is_jacobson_quotient [is_jacobson R] : is_jacobson (quotient I) :=
is_jacobson_of_surjective ⟨quotient.mk I, (by rintro ⟨x⟩; use x; refl)⟩

lemma is_jacobson_iso (e : R ≃+* S) : is_jacobson R ↔ is_jacobson S :=
⟨λ h, @is_jacobson_of_surjective _ _ _ _ h ⟨(e : R →+* S), e.surjective⟩,
  λ h, @is_jacobson_of_surjective _ _ _ _ h ⟨(e.symm : S →+* R), e.symm.surjective⟩⟩

end is_jacobson

section polynomial
variables {R : Type u} [comm_ring R] {I : ideal R}
open polynomial

noncomputable theory

lemma coeff_zero_mem_of_mem_span_C {f : polynomial R} :
  f ∈ span (C '' (I : set R)) → coeff f 0 ∈ I :=
begin
  intro h,
  apply submodule.span_induction h,
  { intros g hg,
    rw set.mem_image at hg,
    rcases hg with ⟨x, ⟨hx, hxg⟩⟩,
    rwa [← hxg, coeff_C_zero] },
  { exact I.zero_mem },
  { intros g g' hg hg',
    simp,
    exact I.add_mem hg hg' },
  { intros x g hg,
    simp,
    exact I.smul_mem _ hg }
end

theorem polynomial_exists_downshift (f : polynomial R) : ∃ g, f = g * X + C (coeff f 0) :=
begin
  use f.sum (λn a, if n > 0 then C a * X^(n - 1) else 0),
  ext,
  cases n,
  { simp },
  { rw [coeff_add, coeff_C_succ, add_zero, coeff_mul_X],
    simp only [coeff_X_pow, coeff_sum, coeff_C_mul],
    rw [finsupp.sum, finset.sum_eq_single (n + 1)],
    { simp,
      exact congr_fun rfl n.succ },
    { intros m hm h,
      cases m,
      { exact trans (by refl) (coeff_zero n) },
      { have : n ≠ m := λ h', h (by rw h'),
        simp [this, coeff_X_pow] } },
    { simp_intros hn,
      exact hn } }
end

/-- `restrict_const_coeff I` is the ideal of polynomials with constant coefficient in I -/
def restrict_const_coeff (I : ideal R) : ideal (polynomial R) := span (insert X (C '' (I : set R)))

lemma mem_restrict_const_coeff_iff_coeff_zero_mem {f : polynomial R} :
  f ∈ restrict_const_coeff I ↔ coeff f 0 ∈ I :=
begin
  split,
  { intro h,
    rcases mem_span_insert.1 h with ⟨f', g, hg, hf⟩,
    simp [hf, coeff_zero_mem_of_mem_span_C hg] },
  { cases polynomial_exists_downshift f with g hg,
    exact λ h, mem_span_insert.2 ⟨g, C (f.coeff 0), mem_map_of_mem h, hg⟩ }
end

lemma restrict_const_coeff.is_prime [H : is_prime I] : is_prime (restrict_const_coeff I) :=
begin
  split,
  { refine λ h, H.left _,
    rw eq_top_iff,
    intros x _,
    have : C x ∈ restrict_const_coeff I := h.symm ▸ submodule.mem_top,
    rwa [mem_restrict_const_coeff_iff_coeff_zero_mem, coeff_C] at this },
  { intros f g hfg,
    rw mem_restrict_const_coeff_iff_coeff_zero_mem at hfg,
    simp at hfg,
    cases H.right hfg,
    { left,
      rwa mem_restrict_const_coeff_iff_coeff_zero_mem },
    { right,
      rwa mem_restrict_const_coeff_iff_coeff_zero_mem } }
end

theorem is_jacobson_polynomial_iff_is_jacobson : is_jacobson R ↔ is_jacobson (polynomial R) :=
begin
  split; intro H,
  {
    sorry,
  },
  { rw is_jacobson_iff_prime_eq,
    introsI P₀ hP₀,
    refine le_antisymm _ le_jacobson,
    intros x hx,
    suffices : coeff (C x) 0 ∈ P₀, by rwa coeff_C_zero at this,
    rw [← mem_restrict_const_coeff_iff_coeff_zero_mem,
      ← H (restrict_const_coeff P₀) (is_prime.radical restrict_const_coeff.is_prime)],
    rw mem_jacobson_iff at ⊢ hx,
    intros f,
    cases hx (coeff f 0) with y hy,
    use C y,
    simp [mem_restrict_const_coeff_iff_coeff_zero_mem, hy] }
end

end polynomial

end ideal
