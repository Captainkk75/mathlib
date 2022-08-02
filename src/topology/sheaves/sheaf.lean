/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.sheaf_condition.equalizer_products
import category_theory.full_subcategory
import category_theory.limits.unit
import category_theory.sites.sheaf
import category_theory.sites.spaces
import category_theory.sites.sheafification

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category.

A presheaf on a topological space `X` is a sheaf presicely when it is a sheaf under the
grothendieck topology on `opens X`, which expands out to say: For each open cover `{ Uᵢ }` of
`U`, and a family of compatible functions `A ⟶ F(Uᵢ)` for an `A : X`, there exists an unique
gluing `A ⟶ F(U)` compatible with the restriction.

See the docstring of `Top.presheaf.is_sheaf` for an explanation on the design descisions and a list
of equivalent conditions.

We provide the instance `category (sheaf C X)` as the full subcategory of presheaves,
and the fully faithful functor `sheaf.forget : sheaf C X ⥤ presheaf C X`.

-/

universes w v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C]
variables {X : Top.{w}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace presheaf

open sheaf_condition_equalizer_products

/--
The sheaf condition has several different equivalent formulations.
The official definition chosen here is in terms of grothendieck topologies so that the results on
sites could be applied here easily, and this condition does not require additional constraints on
the value category.
The equivalent formulations of the sheaf condition on `presheaf C X` are as follows :

1. `Top.presheaf.is_sheaf`: (the official definition)
  It is a sheaf with respect to the grothendieck topology on `opens X`, which is to say:
  For each open cover `{ Uᵢ }` of `U`, and a family of compatible functions `A ⟶ F(Uᵢ)` for an
  `A : X`, there exists an unique gluing `A ⟶ F(U)` compatible with the restriction.

2. `Top.presheaf.is_sheaf_equalizer_products`: (requires `C` to have all products)
  For each open cover `{ Uᵢ }` of `U`, `F(U) ⟶ ∏ F(Uᵢ)` is the equalizer of the two morphisms
  `∏ F(Uᵢ) ⟶ ∏ F(Uᵢ ∩ Uⱼ)`.
  See `Top.presheaf.is_sheaf_iff_is_sheaf_equalizer_products`.

3. `Top.presheaf.is_sheaf_opens_le_cover`:
  Each `F(U)` is the (inverse) limit of all `F(V)` with `V ⊆ U`.
  See `Top.presheaf.is_sheaf_iff_is_sheaf_opens_le_cover`.

4. `Top.presheaf.is_sheaf_pairwise_intersections`:
  For each open cover `{ Uᵢ }` of `U`, `F(U)` is the limit of all `F(Uᵢ)` and all `F(Uᵢ ∩ Uⱼ)`.
  See `Top.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections`.

The following requires `C` to be concrete and complete, and `forget C` to reflect isomorphisms and
preserve limits. This applies to most "algebraic" categories, e.g. groups, abelian groups and rings.

5. `Top.presheaf.is_sheaf_unique_gluing`:
  (requires `C` to be concrete and complete; `forget C` to reflect isomorphisms and preserve limits)
  For each open cover `{ Uᵢ }` of `U`, and a compatible family of elements `x : F(Uᵢ)`, there exists
  a unique gluing `x : F(U)` that restricts to the given elements.
  See `Top.presheaf.is_sheaf_iff_is_sheaf_unique_gluing`.

6. The underlying sheaf of types is a sheaf.
  See `Top.presheaf.is_sheaf_iff_is_sheaf_comp` and
  `category_theory.presheaf.is_sheaf_iff_is_sheaf_forget`.
-/
def is_sheaf (F : presheaf.{w v u} C X) : Prop :=
presheaf.is_sheaf (opens.grothendieck_topology X) F

/--
The presheaf valued in `unit` over any topological space is a sheaf.
-/
lemma is_sheaf_unit (F : presheaf (category_theory.discrete unit) X) : F.is_sheaf :=
λ x U S hS x hx, ⟨eq_to_hom (subsingleton.elim _ _), by tidy, by tidy⟩

lemma is_sheaf_iso_iff {F G : presheaf C X} (α : F ≅ G) : F.is_sheaf ↔ G.is_sheaf :=
presheaf.is_sheaf_of_iso_iff α

/--
Transfer the sheaf condition across an isomorphism of presheaves.
-/
lemma is_sheaf_of_iso {F G : presheaf C X} (α : F ≅ G) (h : F.is_sheaf) : G.is_sheaf :=
(is_sheaf_iso_iff α).1 h

end presheaf

variables (C X)

/--
A `sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
@[derive category]
def sheaf : Type (max u v w) := Sheaf (opens.grothendieck_topology X) C

variables {C X}

/-- The underlying presheaf of a sheaf -/
abbreviation sheaf.presheaf (F : X.sheaf C) : Top.presheaf C X := F.1

variables (C X)

-- Let's construct a trivial example, to keep the inhabited linter happy.
instance sheaf_inhabited : inhabited (sheaf (category_theory.discrete punit) X) :=
⟨⟨functor.star _, presheaf.is_sheaf_unit _⟩⟩

namespace sheaf

/--
The forgetful functor from sheaves to presheaves.
-/
@[derive [full, faithful]]
def forget : Top.sheaf C X ⥤ Top.presheaf C X :=
Sheaf_to_presheaf _ _

-- Note: These can be proved by simp.
lemma id_app (F : sheaf C X) (t) : (𝟙 F : F ⟶ F).1.app t = 𝟙 _ := rfl
lemma comp_app {F G H : sheaf C X} (f : F ⟶ G) (g : G ⟶ H) (t) :
  (f ≫ g).1.app t = f.1.app t ≫ g.1.app t := rfl

instance presheaf_mono_of_mono {D : Type u} [category.{w u} D] [concrete_category.{w} D]
  [preserves_limits (category_theory.forget D)]
  [Π (U : opens X),
    preserves_colimits_of_shape ((opens.grothendieck_topology X).cover U)ᵒᵖ (category_theory.forget D)]
  [reflects_isomorphisms (category_theory.forget D)]
  [has_colimits D]
  [∀ (P : (opens X)ᵒᵖ ⥤ D) (U : opens X) (S : (opens.grothendieck_topology X).cover U), has_multiequalizer (S.index P)]
  {F G : sheaf D X} (f : F ⟶ G) [mono f] : mono f.1 :=
{ right_cancellation := λ P g h eq₀,
  begin
    set P_plus : sheaf D X := (presheaf_to_Sheaf (opens.grothendieck_topology X) D).obj P,
    set g_plus : P_plus ⟶ F := ⟨grothendieck_topology.sheafify_lift (opens.grothendieck_topology X) g F.2⟩ with g_plus_def,
    set h_plus : P_plus ⟶ F := ⟨grothendieck_topology.sheafify_lift (opens.grothendieck_topology X) h F.2⟩ with h_plus_def,
    have eq₁ : g_plus ≫ f = h_plus ≫ f,
    { ext1,
      dsimp,
      apply grothendieck_topology.sheafify_hom_ext (opens.grothendieck_topology X),
      { exact G.2 },
      { simp [eq₀] }, },
    have eq₂ : g_plus = h_plus,
    { rwa cancel_mono at eq₁, },
    rw [g_plus_def, h_plus_def, Sheaf.hom.ext_iff] at eq₂,
    dsimp at eq₂,
    have := grothendieck_topology.to_sheafify_sheafify_lift (opens.grothendieck_topology X) g F.2,
    rw ←this,
    clear this,
    have := grothendieck_topology.to_sheafify_sheafify_lift (opens.grothendieck_topology X) h F.2,
    rw ←this,
    clear this,
    rw eq₂,
  end }


end sheaf

end Top
