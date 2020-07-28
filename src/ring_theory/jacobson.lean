/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.mv_polynomial
import data.polynomial.ring_division
import ring_theory.ideals
import ring_theory.ideal_operations
import ring_theory.localization
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

lemma help [H : is_jacobson R] (P : ideal (polynomial R)) (hP : is_prime P)
  (h : (comap C P : ideal R) = ⊥) (hR : is_integral_domain R)
  : ∃ M ⊆ {J : ideal (polynomial R) | J.is_maximal ∨ J = ⊤}, P = Inf M :=
begin
  refine @classical.by_cases (P = ⊥) _ _ _,
  {
    intro hP_bot,
    use {J : ideal (polynomial R) | J.is_maximal },
    refine ⟨λ _ hx, or.inl hx, _⟩,
    -- Remains that nilradical (radical of ⊥) of integral domain is ⊥
    sorry
  },
  {
    intro hP_bot,
    use { J : ideal (polynomial R) | P ≤ J ∧ J.is_maximal },
    refine ⟨λ _ hx, or.inl hx.right, _⟩,
    refine le_antisymm (le_Inf (λ _ hJ, hJ.left)) _,
    intros f hf,
    let a := f.leading_coeff,

    -- let K := @fraction_ring R (is_integral_domain.to_integral_domain R hR),
    -- let e : polynomial R →+* polynomial K := sorry,
    -- have hf : irreducible (e f) := sorry,
    -- haveI hK : euclidean_domain (polynomial K) := sorry,
    sorry,
  }
end

theorem is_jacobson_polynomial_iff_is_jacobson : is_jacobson R ↔ is_jacobson (polynomial R) :=
begin
  split; introI H,
  {
    rw is_jacobson_iff_Inf_maximal,
    introsI P hP,
    let P₀ : ideal R := comap C P,
    have hP₀ : is_prime P₀ := comap.is_prime C P,
    let Q : ideal (polynomial R) := map C P₀,
    let R' := ideal.quotient P₀,
    have e : (ideal.quotient Q) ≃+* polynomial R' := by {
      sorry,
    },
    let ϕ : polynomial R →+* polynomial R' := e.to_ring_hom.comp (quotient.mk Q),
    have hϕ : function.surjective ϕ := function.surjective.comp e.surjective (submodule.quotient.mk_surjective Q),
    let P' : ideal (polynomial R') := map ϕ P,
    have hR' : is_integral_domain R' := sorry,
    have hR'_jac : is_jacobson R' := by apply_instance,
    have hP' : is_prime P' := sorry,
    rcases help P' hP' _ hR' with ⟨M, hM, hMP'⟩,
    let M' : set (ideal (polynomial R)) := (λ J, comap ϕ J) '' M,
    use M',
    split,
    {
      sorry,
    },
    {
      have : P = comap ϕ P' := sorry,
      rw [this, hMP'],
      rw Inf_image,
      rw comap_Inf,
    },
    {
      rw eq_bot_iff,
      rintros ⟨x⟩ hx,
      rw mem_comap at hx,
      rw submodule.mem_bot,
      erw quotient.eq_zero_iff_mem,
      erw mem_comap,
      rw mem_map_iff_of_surjective _ hϕ at hx,
      cases hx with f hf,
      have : f = C x := sorry, -- from hf.right
      rw ← this,
      exact hf.left,
    }
  },
  { exact is_jacobson_of_surjective ⟨eval₂_ring_hom (ring_hom.id _) 1, λ x, ⟨C x, by simp⟩⟩ }
end

theorem radical_bot_of_integral_domain (R : Type u) [comm_ring R] [integral_domain R]
  : (radical (⊥ : ideal R)) = ⊥ := sorry

theorem is_jacobson_polynomial_iff_is_jacobson' : is_jacobson R ↔ is_jacobson (polynomial R) :=
begin
  split; introI H,
  {
    rw is_jacobson_iff_prime_eq,
    introsI P hP,
    rw eq_jacobson_iff_quotient_radical,
    refine le_antisymm radical_le_jacobson _,
    haveI : integral_domain (P.quotient) := sorry,
    rw radical_bot_of_integral_domain,
    intros x hx,
    sorry,
  },
  { exact is_jacobson_of_surjective ⟨eval₂_ring_hom (ring_hom.id _) 1, λ x, ⟨C x, by simp⟩⟩ }
end

theorem is_jacobson_polynomial_iff_is_jacobson'' : is_jacobson R ↔ is_jacobson (polynomial R) :=
begin
  split; introI H,
  {
    rw is_jacobson_iff_prime_eq,
    introsI I hI,
    rw eq_jacobson_iff_not_mem,
    intros f hf,
    let K := localization (submonoid.closure {f} : submonoid (polynomial R)),
    cases exists_le_maximal (⊥ : ideal K) _ with M' hM',
    have ϕ : polynomial R →+* K := sorry,
    -- refine ⟨comap ϕ M', _⟩,
    --use (comap ϕ M' : ideal (polynomial R)),
    sorry, sorry,
  },
  { exact is_jacobson_of_surjective ⟨eval₂_ring_hom (ring_hom.id _) 1, λ x, ⟨C x, by simp⟩⟩ }
end

-- lemma is_jacobson_mv_polynomial (H : is_jacobson R) (n : ℕ) :
--   is_jacobson (mv_polynomial (fin n) R) :=
-- nat.rec_on n
--   ((is_jacobson_iso
--     ((mv_polynomial.ring_equiv_of_equiv R (equiv.equiv_pempty $ fin.elim0)).trans
--     (mv_polynomial.pempty_ring_equiv R))).mpr H)
--   (λ n hn, (is_jacobson_iso (mv_polynomial.fin_succ_equiv R n)).2 (is_jacobson_polynomial_iff_is_jacobson.1 hn))

end polynomial

end ideal
