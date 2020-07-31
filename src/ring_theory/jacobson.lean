/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.mv_polynomial
import data.polynomial.ring_division
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
variables {R : Type u} [comm_ring R] {I : ideal R}
variables {S : Type v} [comm_ring S]

section is_jacobson

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


section localization
open localization_map
variables {M : submonoid R}

local attribute [instance] classical.prop_decidable

/-- If `S` is the localization of `R` at a submonoid, the maximal ideals of `S` are in
bijection with maximla ideals of `R` that are disjoint from `M` -/
lemma is_maximal_localization_iff_of_jacobson [is_jacobson R] (f : localization_map M S) (J : ideal S) :
  J.is_maximal ↔ (comap f.to_map J).is_maximal ∧ disjoint (M : set R) ↑(ideal.comap f.to_map J) :=
begin
  sorry,
end

lemma is_maximal_local_iff [is_jacobson R] (f : localization_map M S) (I : ideal R) :
  I.is_maximal ∧ disjoint (M : set R) ↑I ↔ (map f.to_map I).is_maximal := sorry

/-- Localization to a set with a single generator is jacobson -/
lemma is_jacobson_localization [H : is_jacobson R]
  {y : R} (f : localization_map (submonoid.closure {y} : submonoid R) S) : is_jacobson S :=
begin
  let H' := H,
  rw is_jacobson_iff_prime_eq at H' ⊢,
  intros P' hP',
  let P := comap f.to_map P',
  refine le_antisymm _ le_jacobson,
  rw localization_map.is_prime_iff_is_prime_disjoint f P' at hP',
  cases hP' with hP' hPM,
  have hP : P.jacobson = P := H' _ hP',
  refine le_trans _ (le_of_eq (localization_map.map_comap f P')),
  refine le_trans (le_of_eq (localization_map.map_comap f P'.jacobson).symm) _,
  refine map_mono _,
  show comap f.to_map P'.jacobson ≤ P,
  let M : submonoid R := submonoid.closure {y},
  let I₁ := Inf { I : ideal R | P ≤ I ∧ I.is_maximal ∧ disjoint (M : set R) ↑I },
  let I₂ := Inf { I : ideal R | I.is_maximal ∧ ¬ disjoint (M : set R) ↑I },
  have : I₁ ⊓ I₂ ≤ P.jacobson, {
    refine le_Inf (λ J hJ, _),
    cases (classical.em (disjoint (M : set R) ↑J)),
    { refine inf_le_left_of_le (Inf_le ⟨hJ.1, hJ.2, h⟩) },
    { refine inf_le_right_of_le (Inf_le ⟨hJ.2, h⟩) }
  },
  have : Inf { I : ideal R | P ≤ I ∧ I.is_maximal ∧ disjoint (M : set R) ↑I } ≤ P, {
    intros x hx,
    have hxy : x * y ∈ P.jacobson, {
      refine this ⟨_, _⟩,
      exact (mul_comm y x) ▸ I₁.smul_mem y hx,
      refine I₂.smul_mem x _,
      rw mem_Inf,
      rintros J ⟨hJ_max, hJ⟩,
      rw set.not_disjoint_iff at hJ,
      rcases hJ with ⟨a, ⟨ha, ha'⟩⟩,
      erw submonoid.mem_closure_singleton at ha,
      cases ha with _ hn,
      rw ← hn at ha',
      refine is_prime.mem_of_pow_mem (is_maximal.is_prime hJ_max) _ ha',
    },
    rw hP at hxy,
    cases hP'.right hxy with hxy hxy,
    { exact hxy },
    { exfalso,
      refine hPM ⟨_, hxy⟩,
      erw submonoid.mem_closure_singleton,
      use 1,
      rw pow_one }
  },
  refine le_trans _ this,
  rw [ideal.jacobson, comap_Inf', Inf_eq_infi],
  refine infi_le_infi_of_subset _,
  rintros I ⟨hI, hI'⟩,
  simp,
  refine ⟨map f.to_map I, _⟩,
  split,
  {
    split,
    { refine le_trans (le_of_eq ((localization_map.map_comap f P').symm)) (map_mono hI) },
    { rwa ← is_maximal_local_iff f }
  },
  {
    exact localization_map.comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI'.left) hI'.right,
  }
end

end localization

section polynomial
open polynomial

theorem is_jacobson_polynomial_iff_is_jacobson : is_jacobson R ↔ is_jacobson (polynomial R) :=
begin
  split; introI H,
  {
    rw is_jacobson_iff_prime_eq,
    introsI I hI,
    rw eq_jacobson_iff_quotient,
    let R' := map ((quotient.mk I).comp C) (⊤ : ideal R),
    sorry,
  },
  { exact is_jacobson_of_surjective ⟨eval₂_ring_hom (ring_hom.id _) 1, λ x, ⟨C x, by simp⟩⟩ }
end

lemma is_jacobson_mv_polynomial (H : is_jacobson R) (n : ℕ) :
  is_jacobson (mv_polynomial (fin n) R) :=
nat.rec_on n
  ((is_jacobson_iso
    ((mv_polynomial.ring_equiv_of_equiv R (equiv.equiv_pempty $ fin.elim0)).trans
    (mv_polynomial.pempty_ring_equiv R))).mpr H)
  (λ n hn, (is_jacobson_iso (mv_polynomial.fin_succ_equiv R n)).2 (is_jacobson_polynomial_iff_is_jacobson.1 hn))

end polynomial

end ideal
