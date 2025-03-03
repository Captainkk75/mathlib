/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import category_theory.eq_to_hom
import category_theory.functor.const

/-!
# Cartesian products of categories

We define the category instance on `C × D` when `C` and `D` are categories.

We define:
* `sectl C Z` : the functor `C ⥤ C × D` given by `X ↦ ⟨X, Z⟩`
* `sectr Z D` : the functor `D ⥤ C × D` given by `Y ↦ ⟨Z, Y⟩`
* `fst`       : the functor `⟨X, Y⟩ ↦ X`
* `snd`       : the functor `⟨X, Y⟩ ↦ Y`
* `swap`      : the functor `C × D ⥤ D × C` given by `⟨X, Y⟩ ↦ ⟨Y, X⟩`
    (and the fact this is an equivalence)

We further define `evaluation : C ⥤ (C ⥤ D) ⥤ D` and `evaluation_uncurried : C × (C ⥤ D) ⥤ D`,
and products of functors and natural transformations, written `F.prod G` and `α.prod β`.
-/

namespace category_theory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section
variables (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D]

/--
`prod C D` gives the cartesian product of two categories.

See <https://stacks.math.columbia.edu/tag/001K>.
-/
@[simps {not_recursive := []}] -- the generates simp lemmas like `id_fst` and `comp_snd`
instance prod : category.{max v₁ v₂} (C × D) :=
{ hom     := λ X Y, ((X.1) ⟶ (Y.1)) × ((X.2) ⟶ (Y.2)),
  id      := λ X, ⟨ 𝟙 (X.1), 𝟙 (X.2) ⟩,
  comp    := λ _ _ _ f g, (f.1 ≫ g.1, f.2 ≫ g.2) }

/-- Two rfl lemmas that cannot be generated by `@[simps]`. -/
@[simp] lemma prod_id (X : C) (Y : D) : 𝟙 (X, Y) = (𝟙 X, 𝟙 Y) := rfl
@[simp] lemma prod_comp {P Q R : C} {S T U : D} (f : (P, S) ⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) :
  f ≫ g = (f.1 ≫ g.1, f.2 ≫ g.2) := rfl

lemma is_iso_prod_iff {P Q : C} {S T : D} {f : (P, S) ⟶ (Q, T)} :
  is_iso f ↔ is_iso f.1 ∧ is_iso f.2 :=
begin
  split,
  { rintros ⟨g, hfg, hgf⟩,
    simp at hfg hgf,
    rcases hfg with ⟨hfg₁, hfg₂⟩,
    rcases hgf with ⟨hgf₁, hgf₂⟩,
    exact ⟨⟨⟨g.1, hfg₁, hgf₁⟩⟩, ⟨⟨g.2, hfg₂, hgf₂⟩⟩⟩ },
  { rintros ⟨⟨g₁, hfg₁, hgf₁⟩, ⟨g₂, hfg₂, hgf₂⟩⟩,
    dsimp at hfg₁ hgf₁ hfg₂ hgf₂,
    refine ⟨⟨(g₁, g₂), _, _⟩⟩; { simp; split; assumption } }
end

section
variables {C D}

/-- Construct an isomorphism in `C × D` out of two isomorphisms in `C` and `D`. -/
@[simps]
def iso.prod {P Q : C} {S T : D} (f : P ≅ Q) (g : S ≅ T) : (P, S) ≅ (Q, T) :=
{ hom := (f.hom, g.hom),
  inv := (f.inv, g.inv), }

end

end

section
variables (C : Type u₁) [category.{v₁} C] (D : Type u₁) [category.{v₁} D]
/--
`prod.category.uniform C D` is an additional instance specialised so both factors have the same
universe levels. This helps typeclass resolution.
-/
instance uniform_prod : category (C × D) := category_theory.prod C D
end

-- Next we define the natural functors into and out of product categories. For now this doesn't
-- address the universal properties.
namespace prod

/-- `sectl C Z` is the functor `C ⥤ C × D` given by `X ↦ (X, Z)`. -/
@[simps] def sectl
  (C : Type u₁) [category.{v₁} C] {D : Type u₂} [category.{v₂} D] (Z : D) : C ⥤ C × D :=
{ obj := λ X, (X, Z),
  map := λ X Y f, (f, 𝟙 Z) }

/-- `sectr Z D` is the functor `D ⥤ C × D` given by `Y ↦ (Z, Y)` . -/
@[simps] def sectr
  {C : Type u₁} [category.{v₁} C] (Z : C) (D : Type u₂) [category.{v₂} D] : D ⥤ C × D :=
{ obj := λ X, (Z, X),
  map := λ X Y f, (𝟙 Z, f) }

variables (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D]

/-- `fst` is the functor `(X, Y) ↦ X`. -/
@[simps] def fst : C × D ⥤ C :=
{ obj := λ X, X.1,
  map := λ X Y f, f.1 }

/-- `snd` is the functor `(X, Y) ↦ Y`. -/
@[simps] def snd : C × D ⥤ D :=
{ obj := λ X, X.2,
  map := λ X Y f, f.2 }

/-- The functor swapping the factors of a cartesian product of categories, `C × D ⥤ D × C`. -/
@[simps] def swap : C × D ⥤ D × C :=
{ obj := λ X, (X.2, X.1),
  map := λ _ _ f, (f.2, f.1) }

/--
Swapping the factors of a cartesion product of categories twice is naturally isomorphic
to the identity functor.
-/
@[simps] def symmetry : swap C D ⋙ swap D C ≅ 𝟭 (C × D) :=
{ hom := { app := λ X, 𝟙 X },
  inv := { app := λ X, 𝟙 X } }

/--
The equivalence, given by swapping factors, between `C × D` and `D × C`.
-/
@[simps]
def braiding : C × D ≌ D × C :=
equivalence.mk (swap C D) (swap D C)
  (nat_iso.of_components (λ X, eq_to_iso (by simp)) (by tidy))
  (nat_iso.of_components (λ X, eq_to_iso (by simp)) (by tidy))

instance swap_is_equivalence : is_equivalence (swap C D) :=
(by apply_instance : is_equivalence (braiding C D).functor)

end prod

section
variables (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D]

/--
The "evaluation at `X`" functor, such that
`(evaluation.obj X).obj F = F.obj X`,
which is functorial in both `X` and `F`.
-/
@[simps] def evaluation : C ⥤ (C ⥤ D) ⥤ D :=
{ obj := λ X,
  { obj := λ F, F.obj X,
    map := λ F G α, α.app X, },
  map := λ X Y f,
  { app := λ F, F.map f,
    naturality' := λ F G α, eq.symm (α.naturality f) } }

/--
The "evaluation of `F` at `X`" functor,
as a functor `C × (C ⥤ D) ⥤ D`.
-/
@[simps] def evaluation_uncurried : C × (C ⥤ D) ⥤ D :=
{ obj := λ p, p.2.obj p.1,
  map := λ x y f, (x.2.map f.1) ≫ (f.2.app y.1),
  map_comp' := λ X Y Z f g,
  begin
    cases g, cases f, cases Z, cases Y, cases X,
    simp only [prod_comp, nat_trans.comp_app, functor.map_comp, category.assoc],
    rw [←nat_trans.comp_app, nat_trans.naturality, nat_trans.comp_app,
        category.assoc, nat_trans.naturality],
  end }

variables {C}

/-- The constant functor followed by the evalutation functor is just the identity. -/
@[simps] def functor.const_comp_evaluation_obj (X : C) :
  functor.const C ⋙ (evaluation C D).obj X ≅ 𝟭 D :=
nat_iso.of_components (λ Y, iso.refl _) (λ Y Z f, by simp)

end

variables {A : Type u₁} [category.{v₁} A]
          {B : Type u₂} [category.{v₂} B]
          {C : Type u₃} [category.{v₃} C]
          {D : Type u₄} [category.{v₄} D]

namespace functor
/-- The cartesian product of two functors. -/
@[simps] def prod (F : A ⥤ B) (G : C ⥤ D) : A × C ⥤ B × D :=
{ obj := λ X, (F.obj X.1, G.obj X.2),
  map := λ _ _ f, (F.map f.1, G.map f.2) }

/- Because of limitations in Lean 3's handling of notations, we do not setup a notation `F × G`.
   You can use `F.prod G` as a "poor man's infix", or just write `functor.prod F G`. -/

/-- Similar to `prod`, but both functors start from the same category `A` -/
@[simps] def prod' (F : A ⥤ B) (G : A ⥤ C) : A ⥤ (B × C) :=
{ obj := λ a, (F.obj a, G.obj a),
  map := λ x y f, (F.map f, G.map f), }

section
variable (C)

/-- The diagonal functor. -/
def diag : C ⥤ C × C := (𝟭 C).prod' (𝟭 C)

@[simp] lemma diag_obj (X : C) : (diag C).obj X = (X, X) := rfl

@[simp] lemma diag_map {X Y : C} (f : X ⟶ Y) : (diag C).map f = (f, f) := rfl

end

end functor

namespace nat_trans

/-- The cartesian product of two natural transformations. -/
@[simps] def prod {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) :
  F.prod H ⟶ G.prod I :=
{ app         := λ X, (α.app X.1, β.app X.2),
  naturality' := λ X Y f,
  begin
    cases X, cases Y,
    simp only [functor.prod_map, prod.mk.inj_iff, prod_comp],
    split; rw naturality
  end }

/- Again, it is inadvisable in Lean 3 to setup a notation `α × β`;
   use instead `α.prod β` or `nat_trans.prod α β`. -/

end nat_trans

/-- `F.flip` composed with evaluation is the same as evaluating `F`. -/
@[simps]
def flip_comp_evaluation (F : A ⥤ B ⥤ C) (a) :
  F.flip ⋙ (evaluation _ _).obj a ≅ F.obj a :=
nat_iso.of_components (λ b, eq_to_iso rfl) $ by tidy

end category_theory
