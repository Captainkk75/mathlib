/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import category_theory.single_obj
import category_theory.equivalence

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

The prototypical example is `V = Module R`,
where `Action (Module R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (single_obj G ⥤ V)`,
and construct the restriction functors `res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G`.
-/

universes u

open category_theory

variables (V : Type (u+1)) [large_category V]

/--
An `Action V G` represents a bundled action of
the monoid `G` on an object of some category `V`.

As an example, when `V = Module R`, this is an `R`-linear representation of `G`,
while when `V = Type` this is a `G`-action.
-/
-- Note: this is _not_ a categorical action of `G` on `V`.
structure Action (G : Mon.{u}) :=
(V : V)
(ρ : G ⟶ Mon.of (End V))

namespace Action
variable {V}

@[simp]
lemma ρ_one {G : Mon.{u}} (A : Action V G) : A.ρ 1 = 𝟙 A.V :=
by { rw [monoid_hom.map_one], refl, }

/-- When a group acts, we can lift the action to the group of automorphisms. -/
@[simps]
def ρ_Aut {G : Group.{u}} (A : Action V (Mon.of G)) : G ⟶ Group.of (Aut A.V) :=
{ to_fun := λ g,
  { hom := A.ρ g,
    inv := A.ρ (g⁻¹ : G),
    hom_inv_id' := ((A.ρ).map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_self, ρ_one]),
    inv_hom_id' := ((A.ρ).map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_self, ρ_one]), },
  map_one' := by { ext, exact A.ρ.map_one },
  map_mul' := λ x y, by { ext, exact A.ρ.map_mul x y }, }

variable (G : Mon.{u})

section

/-- The trivial representation of a group. -/
def trivial : Action AddCommGroup G :=
{ V := AddCommGroup.of punit,
  ρ := 1, }

instance : inhabited (Action AddCommGroup G) := ⟨trivial G⟩
end

variables {G V}

/--
A homomorphism of `Action V G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
structure hom (M N : Action V G) :=
(hom : M.V ⟶ N.V)
(comm' : ∀ g : G, M.ρ g ≫ hom = hom ≫ N.ρ g . obviously)

restate_axiom hom.comm'

namespace hom

/-- The identity morphism on a `Action V G`. -/
@[simps]
def id (M : Action V G) : Action.hom M M :=
{ hom := 𝟙 M.V }

instance (M : Action V G) : inhabited (Action.hom M M) := ⟨id M⟩

/--
The composition of two `Action V G` homomorphisms is the composition of the underlying maps.
-/
@[simps]
def comp {M N K : Action V G} (p : Action.hom M N) (q : Action.hom N K) :
  Action.hom M K :=
{ hom := p.hom ≫ q.hom,
  comm' := λ g, by rw [←category.assoc, p.comm, category.assoc, q.comm, ←category.assoc] }

end hom

instance : category (Action V G) :=
{ hom := λ M N, hom M N,
  id := λ M, hom.id M,
  comp := λ M N K f g, hom.comp f g, }

@[simp]
lemma id_hom (M : Action V G) : (𝟙 M : hom M M).hom = 𝟙 M.V := rfl
@[simp]
lemma comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
  (f ≫ g : hom M K).hom = f.hom ≫ g.hom :=
rfl

/-- Construct an isomorphism of `G` actions/representations
from an isomorphism of the the underlying objects,
where the forward direction commutes with the group action. -/
@[simps]
def mk_iso {M N : Action V G} (f : M.V ≅ N.V) (comm : ∀ g : G, M.ρ g ≫ f.hom = f.hom ≫ N.ρ g) :
  M ≅ N :=
{ hom :=
  { hom := f.hom,
    comm' := comm, },
  inv :=
  { hom := f.inv,
    comm' := λ g, by { have w := comm g =≫ f.inv, simp at w, simp [w], }, }}

namespace functor_category_equivalence

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def functor : Action V G ⥤ (single_obj G ⥤ V) :=
{ obj := λ M,
  { obj := λ _, M.V,
    map := λ _ _ g, M.ρ g,
    map_id' := λ _, M.ρ.map_one,
    map_comp' := λ _ _ _ g h, M.ρ.map_mul h g, },
  map := λ M N f,
  { app := λ _, f.hom,
    naturality' := λ _ _ g, f.comm g, } }

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def inverse : (single_obj G ⥤ V) ⥤ Action V G :=
{ obj := λ F,
  { V := F.obj punit.star,
    ρ :=
    { to_fun := λ g, F.map g,
      map_one' := F.map_id punit.star,
      map_mul' := λ g h, F.map_comp h g, } },
  map := λ M N f,
  { hom := f.app punit.star,
    comm' := λ g, f.naturality g, } }.

/-- Auxilliary definition for `functor_category_equivalence`. -/
def unit_iso : 𝟭 (Action V G) ≅ functor ⋙ inverse :=
nat_iso.of_components (λ M, mk_iso ((iso.refl _)) (by tidy)) (by tidy).

/-- Auxilliary definition for `functor_category_equivalence`. -/
def counit_iso : inverse ⋙ functor ≅ 𝟭 (single_obj G ⥤ V) :=
nat_iso.of_components (λ M, nat_iso.of_components (by tidy) (by tidy)) (by tidy).

end functor_category_equivalence

section
open functor_category_equivalence

/--
The category of actions of `G` in the category `V`
is equivalent to the functor category `single_obj G ⥤ V`.
-/
def functor_category_equivalence : Action V G ≌ (single_obj G ⥤ V) :=
{ functor := functor,
  inverse := inverse,
  unit_iso := unit_iso,
  counit_iso := counit_iso, }

end

section forget

/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `category_theory.forget` API provided by the `concrete_category` instance below,
rather than using this directly.
-/
def forget : Action V G ⥤ V :=
{ obj := λ M, M.V,
  map := λ M N f, f.hom, }

instance [concrete_category V] : concrete_category (Action V G) :=
{ forget := forget ⋙ (concrete_category.forget V),
  forget_faithful :=
  { map_injective' := λ M N f g w,
      hom.ext _ _ (faithful.map_injective (concrete_category.forget V) w), } }

instance has_forget_to_V [concrete_category V] : has_forget₂ (Action V G) V :=
{ forget₂ := forget }

end forget

/-- Actions/representations of the trivial group are just objects in the ambient category. -/
def Action_punit_equivalence : Action V (Mon.of punit) ≌ V :=
{ functor := forget,
  inverse :=
  { obj := λ X, ⟨X, 1⟩,
    map := λ X Y f, ⟨f, λ ⟨⟩, by simp⟩, },
  unit_iso := nat_iso.of_components (λ X, mk_iso (iso.refl _) (λ ⟨⟩, by simpa using ρ_one X))
    (by tidy),
  counit_iso := nat_iso.of_components (λ X, iso.refl _) (by tidy), }

variables (V)
/--
The "restriction" functor along a monoid homomorphism `f : G ⟶ H`,
taking actions of `H` to actions of `G`.

(This makes sense for any homomorphism, but the name is natural when `f` is a monomorphism.)
-/
@[simps]
def res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G :=
{ obj := λ M,
  { V := M.V,
    ρ := f ≫ M.ρ },
  map := λ M N p,
  { hom := p.hom,
    comm' := λ g, p.comm (f g) } }

/--
The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
@[simps]
def res_id {G : Mon} : res V (𝟙 G) ≅ 𝟭 (Action V G) :=
{ hom := { app := λ M, ⟨𝟙 M.V⟩ },
  inv := { app := λ M, ⟨𝟙 M.V⟩ }, }

/--
The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
@[simps]
def res_comp {G H K : Mon} (f : G ⟶ H) (g : H ⟶ K) : res V g ⋙ res V f ≅ res V (f ≫ g) :=
{ hom := { app := λ M, ⟨𝟙 M.V⟩ },
  inv := { app := λ M, ⟨𝟙 M.V⟩ },
  hom_inv_id' := by { ext, dsimp, simp, },
  inv_hom_id' := by { ext, dsimp, simp, }, }

-- TODO promote `res` to a pseudofunctor from
-- the locally discrete bicategory constructed from `Monᵒᵖ` to `Cat`, sending `G` to `Action V G`.

-- TODO limits, colimits, images, etc, when `V` has them
-- TODO (symmetric) monoidal category structure when `V` has one

end Action

namespace category_theory.functor

variables {V} {W : Type (u+1)} [large_category W]

/-- A functor between categories induces a functor between
the categories of `G`-actions within those categories. -/
@[simps]
def map_Action (F : V ⥤ W) (G : Mon.{u₁}) : Action V G ⥤ Action W G :=
{ obj := λ M,
  { V := F.obj M.V,
    ρ :=
    { to_fun := λ g, F.map (M.ρ g),
      map_one' := by tidy,
      map_mul' := by simp, }},
  map := λ M N f,
  { hom := F.map f.hom,
    comm' := λ g, by { dsimp, rw [←F.map_comp, f.comm, F.map_comp] } }, }

end category_theory.functor
