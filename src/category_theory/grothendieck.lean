/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Junyan Xu
-/

import category_theory.lax_functor
import category_theory.elements
import category_theory.over
import category_theory.limits.preserves.basic
import category_theory.adjunction.limits

/-!
# The Grothendieck construction for lax functors

Given a lax functor `F` from a 1-category `C` to the 2-category `Cat`,
the objects of `grothendieck F` consist of dependent pairs `(b, f)`,
where `b : C` and `f : F.obj c`, and a morphism `(b, f) ⟶ (b', f')` is a
pair `β : b ⟶ b'` in `C`, and `φ : (F.map β).obj f ⟶ f'`. The forgetful
functor `grothendieck F ⥤ C` can be seen as a fibration of categories,
with base category `C`, total category `grothendieck F`, and fiber categories
`F.obj b`, `b : C`. When `F` is a pseudofunctor, this is a Grothendieck
fibration.

Notice that `F` gives a functor `F.map β` between fiber categories `F.obj b`
and `F.obj b'` for each morphism `β : b ⟶ b'` in `C`, which we call a component
functor. We show that if `F` is a pseudofunctor, the base category and all fiber
categories have colimits and the component functors all preserve colimits, then
the total category also has colimits.

https://ncatlab.org/nlab/show/Grothendieck+construction#limits_and_colimits

In case all component functors have right adjoints, we can transfer the
lax functor structure of `F` across the adjunctions to obtain a lax functor
`G` from `Cᵒᵖ` to `Cat` with component functors opposites (`functor.op`) of
the right adjoints. We show that `grothendieck G` is isomorphic to the
opposite of `grothenieck F`, and we may show that `grothendieck F` has
limits by showing that `grothendieck G` has colimits.

(what about left adjoints?)

This will be used to construct the category `PrimedPreringedSpace` and
to show that `PresheafedSpace`, `SheafedSpace` and `PrimedPreringedSpace` has
(co)limits. Fibrations of categories such as `Top` over `Type`, or `PresheafedSpace`
over `Top` are also examples of this construction, and it may be preferable to
have the existence of (co)limits in `Top` refactored to use results here.

## References

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

See also `category_theory.elements` for the category of elements of functor `F : C ⥤ Type`.

-/

universes v u₁ u₂

namespace category_theory

variables {C : Type*} [category.{v} C] (F : lax_functor_to_Cat C)

/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
@[nolint has_inhabited_instance]
structure grothendieck :=
(base : C)
(fiber : F.obj base)

namespace grothendieck

variables {F}

/--
A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure hom (X Y : grothendieck F) :=
(base : X.base ⟶ Y.base)
(fiber : (F.map base).obj X.fiber ⟶ Y.fiber)

@[ext] lemma ext {X Y : grothendieck F} (f g : hom X Y)
  (w_base : f.base = g.base) (w_fiber : eq_to_hom (by rw w_base) ≫ f.fiber = g.fiber) : f = g :=
begin
  cases f; cases g,
  congr,
  dsimp at w_base,
  induction w_base,
  refl,
  dsimp at w_base,
  induction w_base,
  simpa using w_fiber,
end

/--
The identity morphism in the Grothendieck category.
-/
@[simps]
def id (X : grothendieck F) : hom X X :=
{ base := 𝟙 X.base,
  fiber := (F.map_id X.base).app X.fiber }

instance (X : grothendieck F) : inhabited (hom X X) := ⟨id X⟩


variables {W X Y : grothendieck F} {Z : C}

section fiber_push_map

variables (e : hom W X) (f : hom X Y) (g : Y.base ⟶ Z)

def fiber_push_map : (F.map (f.base ≫ g)).obj X.fiber ⟶ (F.map g).obj Y.fiber :=
(F.map_comp f.base g).app X.fiber ≫ (F.map g).map f.fiber

/--
Composition of morphisms in the Grothendieck category.
-/
@[simps]
def comp : hom W Y :=
{ base := e.base ≫ f.base,
  fiber := fiber_push_map e f.base ≫ f.fiber }

instance : category (grothendieck F) :=
{ hom := λ X Y, grothendieck.hom X Y,
  id := λ X, grothendieck.id X,
  comp := λ X Y Z f g, grothendieck.comp f g,
  id_comp' := λ X Y f, by { ext, { dsimp [fiber_push_map], simp }, simp },
  comp_id' := λ X Y f, by { ext, { dsimp [fiber_push_map], simp }, simp },
  assoc' := λ W X Y Z e f g, by { ext, { dsimp [fiber_push_map], simp }, simp } }

end fiber_push_map

@[simp] lemma id_base' : hom.base (𝟙 X) = 𝟙 X.base := rfl

@[simp] lemma id_fiber' (X : grothendieck F) :
  hom.fiber (𝟙 X) = (F.map_id X.base).app X.fiber := rfl

lemma congr {X Y : grothendieck F} {f g : X ⟶ Y} (h : f = g) :
  f.fiber = eq_to_hom (by rw h) ≫ g.fiber := by { subst h, simp }

section fiber_push_map

variables {Z' : C} (e : W ⟶ X) (f : X ⟶ Y) (g : Y.base ⟶ Z) (h : Z ⟶ Z')

@[simp] lemma comp_base' : (e ≫ f).base = e.base ≫ f.base := rfl

@[simp] lemma comp_fiber' : (e ≫ f).fiber = fiber_push_map e f.base ≫ f.fiber := rfl

@[simp]
lemma fiber_push_map_id_left : fiber_push_map (𝟙 Y) g = eq_to_hom (by simp) :=
by { dsimp [fiber_push_map], simpa }

@[simp]
lemma fiber_push_map_id_right : (f ≫ 𝟙 Y).fiber = eq_to_hom (by simp) ≫ f.fiber :=
congr (by simp)

@[simp, reassoc]
lemma fiber_push_map_comp_left : fiber_push_map (e ≫ f) g =
  eq_to_hom (by simp) ≫ fiber_push_map e (f.base ≫ g) ≫ fiber_push_map f g :=
by { dsimp [fiber_push_map], simp }

@[simp, reassoc]
lemma fiber_push_map_comp_right : fiber_push_map f (g ≫ h) ≫ (F.map_comp _ _).app _ =
  eq_to_hom (by simp) ≫ (F.map_comp _ _).app _ ≫ (F.map h).map (fiber_push_map f g) :=
by { dsimp [fiber_push_map], simp }

end fiber_push_map


section
variables (F)

/-- The forgetful functor from `grothendieck F` to the source category. -/
@[simps]
def forget : grothendieck F ⥤ C :=
{ obj := λ X, X.1,
  map := λ X Y f, f.1 }

@[simps obj]
def fiber_push (X : C) : costructured_arrow (forget F) X ⥤ (F.obj X).1 :=
{ obj := λ f, (F.map f.hom).obj f.left.fiber,
  map := λ f₁ f₂ g, eq_to_hom (by erw costructured_arrow.w g) ≫ fiber_push_map g.left f₂.hom,
  map_id' := λ f, by { dsimp, simp },
  map_comp' := λ _ _ _ g₁ g₂, by { rw eq_to_hom.family_congr
    (fiber_push_map g₁.left) (costructured_arrow.w g₂).symm, dsimp, simp } }

def fiber_push_over (X : grothendieck F) : over X ⥤ over X.fiber :=
{ obj := λ f, over.mk f.hom.fiber,
  map := λ _ _ g, over.hom_mk
    ((fiber_push F X.base).map ((costructured_arrow.post _ (forget F) _).map g))
    (by {rw congr (over.w g).symm, dsimp [fiber_push], simpa}) }

/-- A 2-natural transformation. -/
def fiber_push_comp {X Y : C} (f : X ⟶ Y) :
  costructured_arrow.map f ⋙ fiber_push F Y ⟶ fiber_push F X ⋙ F.map f :=
{ app := λ _, (F.map_comp _ _).app _, -- λ e, (F.map_comp e.hom f).app e.left.fiber,
  naturality' := λ f₁ f₂ g, by { let fn := λ g, F.map_comp g f,
    have := eq_to_hom.family_congr fn (costructured_arrow.w g).symm,
    dsimp [fn, fiber_push] at ⊢ this, simp [this] } }

end

section colimit

open limits

variables {J : Type*} [category J] {𝒟 : J ⥤ grothendieck F}
(cb : cocone (𝒟 ⋙ forget F)) (c : cocone 𝒟)

def fiber_diagram : J ⥤ (F.obj cb.X).1 :=
costructured_arrow.of_cocone _ _ cb.ι ⋙ costructured_arrow.pre _ _ _ ⋙ fiber_push _ _

lemma fiber_diagram_map {j j' : J} (f : j ⟶ j') :
  (fiber_diagram ((forget F).map_cocone c)).map f =
  (@functor.map _ _ _ _ (fiber_push_over F c.X)
    (over.mk (c.ι.app j)) (over.mk (c.ι.app j')) (over.hom_mk (𝒟.map f))).left := rfl

def fiber_cocone : cocone (fiber_diagram ((forget F).map_cocone c)) :=
{ X := c.X.fiber,
  ι := { app := λ j, ((fiber_push_over _ _).obj (over.mk (c.ι.app j))).hom,
    naturality' := λ j j' f, by { dsimp [fiber_diagram_map], simp } } }


variable (cf : cocone (fiber_diagram cb))

@[simps]
def total_cocone : cocone 𝒟 :=
{ X := { base := cb.X, fiber := cf.X },
  ι := { app := λ j, { base := cb.ι.app j, fiber := cf.ι.app j },
    naturality' := λ j j' f, by { erw category.comp_id, ext,
    { erw ← category.assoc, exact cocone.w cf f }, exact cocone.w cb f } } }

variables {cb} (lb : is_colimit cb)

def desc_base : cb.X ⟶ c.X.base := lb.desc ((forget F).map_cocone c)

def fiber_trans :
  fiber_diagram ((forget F).map_cocone c) ⟶
  fiber_diagram cb ⋙ F.map (desc_base c lb) :=
{ app := λ j, eq_to_hom (by {dsimp, erw lb.fac, refl}) ≫ (fiber_push_comp F _).app _,
  naturality' := λ j j' f, by { rw category.assoc,
    erw ← nat_trans.naturality, dsimp [fiber_diagram, fiber_push],
    erw eq_to_hom.family_congr (fiber_push_map _) (lb.fac _ j'), simpa } }

variable [∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), is_iso (F.map_comp f g)]

instance {X Y : C} (f : X ⟶ Y) : is_iso (fiber_push_comp F f) :=
by { fapply nat_iso.is_iso_of_is_iso_app _, dsimp [fiber_push_comp], apply_instance }

instance : is_iso (fiber_trans c lb) :=
by { fapply nat_iso.is_iso_of_is_iso_app _, dsimp [fiber_trans], apply_instance }

lemma fiber_push_total_cocone (j : J) :
  fiber_push_map ((total_cocone cb cf).ι.app j) (desc_base c lb) =
  eq_to_hom (by {erw lb.fac, refl}) ≫
  (fiber_trans c lb).app j ≫ (F.map (desc_base c lb)).map (cf.ι.app j) :=
by { dsimp [fiber_trans], simpa }

variables {cf} (lf : ∀ {c : C} (f : cb.X ⟶ c), is_colimit (functor.map_cocone (F.map f) cf))

noncomputable def total_cocone_is_colimit : is_colimit (total_cocone cb cf) :=
let cf' := λ c, (cocones.precompose (inv (fiber_trans c lb))).obj (fiber_cocone c) in
{ desc := λ c,
  { base := desc_base c lb,
    fiber := (lf (desc_base c lb)).desc (cf' c) },
  fac' := λ c j, by { ext, swap, apply lb.fac,
    { dsimp, simp only [fiber_push_total_cocone, category.assoc], erw (lf _).fac, simpa } },
  uniq' := λ c f h, by {
    have := lb.uniq ((forget F).map_cocone c) f.base (λ j, by {dsimp, rw ← h, refl}),
    ext, swap, exact this,
    { apply (lf _).uniq (cf' c), intro j,
      change _ = _ ≫ (c.ι.app j).fiber, rw congr (h j).symm, dsimp,
      rw eq_to_hom.family_congr (fiber_push_map _) this, erw fiber_push_total_cocone, simpa } } }

/-- forgetful functor preserves colimit .. whenever colimit exist?
    or whenever both the base and fiber categories has colimits ...
    whenever Hb Hf Hp all holds .. -/

variables [Hb : has_colimits_of_shape J C]
[Hf : ∀ X : C, has_colimits_of_shape J (F.obj X).1]
(Hp : ∀ {X Y : C} (f : X ⟶ Y), preserves_colimits_of_shape J (F.map f))

include Hb Hf Hp
lemma has_colimits_of_shape : has_colimits_of_shape J (grothendieck F) :=
{ has_colimit := λ 𝒟, { exists_colimit := ⟨ { cocone := _, is_colimit :=
  let base := get_colimit_cocone (𝒟 ⋙ forget F) in
  total_cocone_is_colimit base.is_colimit (λ _ f,
    is_colimit_of_preserves _ (get_colimit_cocone (fiber_diagram base.cocone)).is_colimit ) } ⟩ } }
omit Hp

open adjunction

lemma has_colimits_of_shape_of_left_adjoint
  (H : ∀ {X Y : C} (f : X ⟶ Y), is_left_adjoint (F.map f)) :
  limits.has_colimits_of_shape J (grothendieck F) :=
has_colimits_of_shape
  (λ _ _ f, by apply (left_adjoint_preserves_colimits (of_left_adjoint (F.map f))).1)

end colimit

#set_option pp.universes true

#check has_colimits_of_shape_of_left_adjoint

/-
section

variables (G : pseudofunctor_to_Cat C) (X : grothendieck G.to_lax_functor_to_Cat)

@[simps obj map]
noncomputable def cleavage : under X.base ⥤ under X :=
{ obj := λ f, ⟨punit.star, ⟨f.right, (G.map f.hom).obj X.fiber⟩, ⟨f.hom, 𝟙 _⟩⟩,
  map := λ f₁ f₂ g, ⟨𝟙 _,
    ⟨g.right, (inv (G.map_comp f₁.hom g.right) ≫ eq_to_hom (by rw under.w g)).app X.fiber⟩,
    by { erw category.id_comp, ext1, {erw comp_fiber, dsimp, simpa}, exact (under.w g).symm }⟩,
  map_id' := λ f, by {ext1, ext1, {dsimp, simpa}, refl},
  map_comp' := λ f₁ f₂ f₃ g₁ g₂, by { congr, dsimp,
    have h := (G.1.assoc_components f₁.hom g₁.right g₂.right X.fiber).symm,
    let a := λ f, G.map_comp f g₂.right, have b := under.w g₁,
    have h' := eq_to_hom.family_congr a b, dsimp [a] at h',
    rw [h', ← category.assoc, ← is_iso.eq_comp_inv, ← is_iso.inv_eq_inv] at h,
    convert eq_whisker h (eq_to_hom (by simp : _ = (G.map f₃.hom).obj X.fiber)) using 1,
    simp, simpa } }

def cleavage_forget_counit : under.post (forget G.1) ⋙ cleavage G X ⟶ 𝟭 (under X) :=
{ app := λ f, ⟨eq_to_hom (by simp), ⟨𝟙 _, (G.map_id _).app _ ≫ f.hom.fiber⟩,
    by { dsimp, rw category.id_comp, ext,
      { erw comp_fiber, dsimp, simpa }, { erw comp_base, simp } }⟩,
  naturality' := λ f₁ f₂ g, by { ext,
    { dsimp, erw [comp_fiber, comp_fiber], dsimp, simp, } }}


def cleavage_forget_adjunction :
  cleavage G X ⊣ under.post (forget G.1) := adjunction.mk_of_unit_counit
{ unit := eq_to_hom $ by { apply functor.hext, { rintro ⟨⟨_⟩,_⟩, refl },
    { rintros ⟨⟨_⟩,_⟩ ⟨⟨_⟩,_⟩ ⟨⟨_⟩,_⟩, dsimp, congr } },
  counit := ,
  left_triangle' := ,
  right_triangle' := }

end
-/
universe w
variables (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps]
def grothendieck_Type_to_Cat_functor : grothendieck (G ⋙ Type_to_Cat).to_lax ⥤ G.elements :=
{ obj := λ X, ⟨X.1, X.2⟩,
  map := λ X Y f, ⟨f.1, f.2.1.1⟩ }

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps]
def grothendieck_Type_to_Cat_inverse : G.elements ⥤ grothendieck (G ⋙ Type_to_Cat).to_lax :=
{ obj := λ X, ⟨X.1, X.2⟩,
  map := λ X Y f, ⟨f.1, ⟨⟨f.2⟩⟩⟩ }

/--
The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
@[simps]
def grothendieck_Type_to_Cat : grothendieck (G ⋙ Type_to_Cat).to_lax ≌ G.elements :=
{ functor := grothendieck_Type_to_Cat_functor G,
  inverse := grothendieck_Type_to_Cat_inverse G,
  unit_iso := nat_iso.of_components (λ X, by { cases X, exact iso.refl _, })
    (by { rintro ⟨⟩ ⟨⟩ ⟨base, ⟨⟨f⟩⟩⟩, dsimp at *, subst f, ext, simp, }),
  counit_iso := nat_iso.of_components (λ X, by { cases X, exact iso.refl _, })
    (by { rintro ⟨⟩ ⟨⟩ ⟨f, e⟩, dsimp at *, subst e, ext, simp, }),
  functor_unit_iso_comp' := by { rintro ⟨⟩, dsimp, simp, refl, } }

end grothendieck

end category_theory
