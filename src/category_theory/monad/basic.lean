/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta, Adam Topaz
-/
import category_theory.functor_category

namespace category_theory
open category

universes v₁ u₁ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v₁} C]

/--
The data of a monad on C consists of an endofunctor T together with natural transformations
η : 𝟭 C ⟶ T and μ : T ⋙ T ⟶ T satisfying three equations:
- T μ_X ≫ μ_X = μ_(TX) ≫ μ_X (associativity)
- η_(TX) ≫ μ_X = 1_X (left unit)
- Tη_X ≫ μ_X = 1_X (right unit)
-/
class monad (T : C ⥤ C) :=
(η [] : 𝟭 _ ⟶ T)
(μ [] : T ⋙ T ⟶ T)
(assoc' : ∀ X : C, T.map (nat_trans.app μ X) ≫ μ.app _ = μ.app (T.obj X) ≫ μ.app _ . obviously)
(left_unit' : ∀ X : C, η.app (T.obj X) ≫ μ.app _ = 𝟙 _  . obviously)
(right_unit' : ∀ X : C, T.map (η.app X) ≫ μ.app _ = 𝟙 _  . obviously)

restate_axiom monad.assoc'
restate_axiom monad.left_unit'
restate_axiom monad.right_unit'
attribute [simp] monad.left_unit monad.right_unit

notation `η_` := monad.η
notation `μ_` := monad.μ

/--
The data of a comonad on C consists of an endofunctor G together with natural transformations
ε : G ⟶ 𝟭 C and δ : G ⟶ G ⋙ G satisfying three equations:
- δ_X ≫ G δ_X = δ_X ≫ δ_(GX) (coassociativity)
- δ_X ≫ ε_(GX) = 1_X (left counit)
- δ_X ≫ G ε_X = 1_X (right counit)
-/
class comonad (G : C ⥤ C) :=
(ε [] : G ⟶ 𝟭 _)
(δ [] : G ⟶ (G ⋙ G))
(coassoc' : ∀ X : C, nat_trans.app δ _ ≫ G.map (δ.app X) = δ.app _ ≫ δ.app _ . obviously)
(left_counit' : ∀ X : C, δ.app X ≫ ε.app (G.obj X) = 𝟙 _ . obviously)
(right_counit' : ∀ X : C, δ.app X ≫ G.map (ε.app X) = 𝟙 _ . obviously)

restate_axiom comonad.coassoc'
restate_axiom comonad.left_counit'
restate_axiom comonad.right_counit'
attribute [simp] comonad.left_counit comonad.right_counit

notation `ε_` := comonad.ε
notation `δ_` := comonad.δ

/-- A morphisms of monads is a natural transformation compatible with η and μ. -/
structure monad_hom (M N : C ⥤ C) [monad M] [monad N] extends nat_trans M N :=
(app_η' {X} : (η_ M).app X ≫ app X = (η_ N).app X . obviously)
(app_μ' {X} : (μ_ M).app X ≫ app X = (M.map (app X) ≫ app (N.obj X)) ≫ (μ_ N).app X . obviously)

namespace monad_hom
variables {M N L K : C ⥤ C} [monad M] [monad N] [monad L] [monad K]

@[ext]
theorem ext (f g : monad_hom M N) :
  f.to_nat_trans = g.to_nat_trans → f = g := by {cases f, cases g, simp}

variable (M)
/-- The identity natural transformations is a morphism of monads. -/
def ident : monad_hom M M :=
{ app_η' := by tidy,
  app_μ' := by tidy,
  ..𝟙 M }
variable {M}

instance : inhabited (monad_hom M M) := ⟨ident _⟩

/-- The composition of two morphisms of monads. -/
def comp (f : monad_hom M N) (g : monad_hom N L) : monad_hom M L :=
{ app := λ X, (f.app X) ≫ (g.app X),
  app_η' := λ X, by {rw ←assoc, simp [app_η']},
  app_μ' := λ X, by {rw ←assoc, simp [app_μ']} }

@[simp] lemma ident_comp (f : monad_hom M N) : (monad_hom.ident M).comp f = f :=
  by {ext, apply id_comp}
@[simp] lemma comp_ident (f : monad_hom M N) : f.comp (monad_hom.ident N) = f :=
  by {ext, apply comp_id}
lemma comp_assoc (f : monad_hom M N) (g : monad_hom N L) (h : monad_hom L K) :
  (f.comp g).comp h = f.comp (g.comp h) := by {ext, apply assoc}

end monad_hom

restate_axiom monad_hom.app_η'
restate_axiom monad_hom.app_μ'
attribute [simp] monad_hom.app_η monad_hom.app_μ

namespace monad
instance : monad (𝟭 C) :=
{ η := 𝟙 _,
  μ := 𝟙 _ }
end monad

end category_theory
