/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.sheaf
import category_theory.limits.kan_extension
import category_theory.flat_functors

universes v₁ v₂ u₁ u₂
noncomputable theory

open category_theory
open opposite
open category_theory.presieve.family_of_elements
open category_theory.presieve
open category_theory.limits

namespace category_theory
section cover_lifting
variables {C : Type*} [category C] {D : Type*} [category D] {E : Type*} [category E]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables {L : grothendieck_topology E}

/--
A functor `u : (C, J) ⥤ (D, K)` between sites is called to have the cover-preserving property
if for all covering sieves `R` in `D`, `R.pushforward u` is a covering sieve in `C`.
-/
@[nolint has_inhabited_instance]
structure cover_preserving (J : grothendieck_topology C) (K : grothendieck_topology D) (u : C ⥤ D) :=
(cover_preserve : ∀ {U : C} {S : sieve U} (hS : S ∈ J U), S.functor_pushforward u ∈ K (u.obj U))

lemma compatible.functor_pushforward {C : Type*} {D : Type*} [category.{v₁} C] [category.{v₁} D]
  {u : C ⥤ D} [representably_flat u] {P : Dᵒᵖ ⥤ Type _} {Z : C} {T : presieve Z}
  {x : family_of_elements (u.op ⋙ P) T} (h : x.compatible) :
  (x.functor_pushforward u).compatible :=
begin
  /-
  It suffices to show that for each `g₁ : W ⟶ Z₁`, `g₂ : W ⟶ Z₂`, the restriction of
  `x.functor_pushforward u` along `g₁` and `g₂` are the same.
  Note that by the definition of `functor_pushforward`, `Z₁` and `Z₂` are in the images of `u`,
  i.e. `g₁`, `g₂` are costructured arrows over `W`.
   -/
  intros Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq,

  /- First, `g₁` and `g₂` forms a cone over `cospan f₁ f₂`. -/
  have : cospan f₁ f₂ = cospan h₁.premap h₂.premap ⋙ u,
  { fapply functor.ext,
    { intro X, cases X, simp, cases X; simp },
    { intros X Y f, cases f, cases X, simpa,
      { simp, erw category.id_comp, simp },
      { cases f_1; simp } } },
  let c := ((cones.postcompose (eq_to_hom this)).obj (pullback_cone.mk g₁ g₂ eq) : _),

  /-
  This cone viewed as a cone over `cospan _ _ ⋙ u` (since `f₁` `f₂` has preimages) can then be
  viewed as a cospan of structured arrows, and we may obtain an arbitrary cone over it since
  `structured_arrow W u` is cofiltered. Then, to prove that `x` is compatible when restricted onto
  `W`, it suffices to prove that it is compatible when restricted onto `u(c'.X.right)`.
  -/
  let c' := is_cofiltered.cone (structured_arrow_cone.to_diagram c ⋙ structured_arrow.pre _ _ _),
  have eq₁ : g₁ = (c'.X.hom ≫ u.map (c'.π.app walking_cospan.left).right) ≫ eq_to_hom (by simp),
  { erw ← (c'.π.app walking_cospan.left).w, dsimp, simp },
  have eq₂ : g₂ = (c'.X.hom ≫ u.map (c'.π.app walking_cospan.right).right) ≫ eq_to_hom (by simp),
  { erw ← (c'.π.app walking_cospan.right).w, dsimp, simp },
  conv_lhs { rw eq₁ },
  conv_rhs { rw eq₂ },
  simp only [op_comp, functor.map_comp, types_comp_apply, eq_to_hom_op, eq_to_hom_map],
  congr' 1,

  /-
  Now, since everything now falls in the image of `u`,
  the result follows from the compatibleness of `x`.
  -/
  have : (c'.π.app walking_cospan.left).right ≫ h₁.premap =
    (c'.π.app walking_cospan.right).right ≫ h₂.premap,
  { injection c'.π.naturality walking_cospan.hom.inl with _ e₁,
    injection c'.π.naturality walking_cospan.hom.inr with _ e₂,
    exact e₁.symm.trans e₂ },
  convert h (c'.π.app walking_cospan.left).right (c'.π.app walking_cospan.right).right
    h₁.premap_cover h₂.premap_cover this,
  { change (eq_to_hom _ ≫ eq_to_hom _ : (u.op ⋙ P).obj _ ⟶ _) (x h₁.premap _) = x h₁.premap _,
    simp },
  { change (eq_to_hom _ ≫ eq_to_hom _ : (u.op ⋙ P).obj _ ⟶ _) (x h₂.premap _) = x h₂.premap _,
    simp },
end


/-- The identity functor on a site is cover-preserving. -/
def id_cover_preserving : cover_preserving J J (𝟭 _) := sorry

/-- The composition of two cover-preserving functors are cover-lifting -/
def comp_cover_preserving {u} (hu : cover_preserving J K u) {v} (hv : cover_preserving K L v) :
  cover_preserving J L (u ⋙ v) := sorry

end cover_lifting

variables {C D : Type u₁} [category.{v₁} C] [category.{v₁} D]
variables {A : Type u₂} [category.{v₁} A] [has_limits A]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
/--
If `u` is cover_lifting, then `Ran u.op` pushes sheaves to sheaves.

This result is basically https://stacks.math.columbia.edu/tag/00XK,
but without the condition that `C` or `D` has pullbacks.
-/
theorem pullback_is_sheaf_of_cover_preserving {u : C ⥤ D} [representably_flat u]
  (hu : cover_preserving J K u) (ℱ : Sheaf K A) :
  presheaf.is_sheaf J (((whiskering_left _ _ _).obj u.op).obj ℱ.val) :=
begin
  intros X U S hS x hx,
  split, swap,
  { change family_of_elements (u.op ⋙ ℱ.val ⋙ coyoneda.obj (op X)) ⇑S at x,
    apply (ℱ.2 X _ (hu.cover_preserve hS)).amalgamate (x.functor_pushforward u).sieve_extend,
    apply family_of_elements.compatible.sieve_extend,
    exact compatible.functor_pushforward hx,
  },
  split,
  { sorry },
  { sorry }
end

end category_theory
