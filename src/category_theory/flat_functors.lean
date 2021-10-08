/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.kan_extension
import category_theory.limits.filtered_colimit_commutes_finite_limit
import category_theory.limits.preserves.functor_category
import category_theory.limits.presheaf
import category_theory.limits.yoneda
import category_theory.limits.preserves.shapes.equalizers
import category_theory.bicones

/-!
# Representably flat functors

Define representably flat functors as functors such that the catetory of structured arrows over `X`
is cofiltered for each `X`. This concept is also knows as flat functors as in [Elephant], or
Remark C2.3.7, and this name is suggested by Mike Shulman in
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to differentiate
this concept from other notions of flatness.

## Main results
* If `F : C ⥤ D` preserves finite limits and `C` has all finite limits, then `F` is flat.
* If `F : C ⥤ D` is a flat functor between small categories, then both `Lan F.op` and `F`
preserves finite limits.

## Future work

* Presumably flat functors still preserves finite limits in big categories under certain
constraints, such as

-/

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory
open category_theory.limits
open opposite

namespace category_theory

section representably_flat
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

class representably_flat (u : C ⥤ D) : Prop :=
(cofiltered : ∀ (X : D), is_cofiltered (structured_arrow X u))

lemma functor.flat_cofiltered (u : C ⥤ D) [representably_flat u] (X : D) :
 is_cofiltered (structured_arrow X u) := representably_flat.cofiltered X

variables (u : C ⥤ D) [representably_flat u] {X : D} (Y₁ Y₂ : costructured_arrow u X)

instance cofiltered_of_flat := u.flat_cofiltered X

end representably_flat

section has_limit
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]

lemma flat_of_preserves_finite_limit [has_limits C] (F : C ⥤ D)
  (H : ∀ (J : Type v₁) [h : small_category J] [h' : @fin_category J h],
    @preserves_limits_of_shape _ _ _ _ J h F) : representably_flat F := ⟨λ X,
{ cocone_objs := λ A B, by
  { let fn := limits.binary_fan.mk A.hom B.hom,
    let is_lim := is_limit_of_has_binary_product_of_preserves_limit F A.right B.right,
    use structured_arrow.mk (is_lim.lift fn),
    use structured_arrow.hom_mk limits.prod.fst (is_lim.fac fn walking_pair.left),
    use structured_arrow.hom_mk limits.prod.snd (is_lim.fac fn walking_pair.right) },
  cocone_maps := λ A B f g, by
  { let fn : fork (F.map f.right) (F.map g.right) := limits.fork.of_ι A.hom (f.w.symm.trans g.w),
    let is_lim := is_limit_of_has_equalizer_of_preserves_limit F f.right g.right,
    use structured_arrow.mk (is_lim.lift fn),
    use structured_arrow.hom_mk (equalizer.ι f.right g.right)
      (is_lim.fac fn walking_parallel_pair.zero),
    ext,
    exact equalizer.condition f.right g.right },
  nonempty := by
  { haveI := has_terminal_of_has_terminal_of_preserves_limit F,
    exact nonempty.intro (structured_arrow.mk
      (terminal.from X ≫ (preserves_terminal.iso F).inv)) } }⟩

open category_theory.limits.walking_parallel_pair_hom


namespace preserves_finite_limit_of_flat
@[simps]
def cone_to_diagram_of_structured_arrows {J : Type*} [category J] {K : J ⥤ C}
(F : C ⥤ D) (c : cone (K ⋙ F)) : (J ⥤ structured_arrow c.X F) :=
{ obj := λ X, structured_arrow.mk (c.π.app X),
  map := λ X Y f, structured_arrow.hom_mk (K.map f)
    (by { convert (c.π.naturality f).symm, exact (category.id_comp _).symm }) }

lemma cone_diagram_proj {J : Type*} [category J] {K : J ⥤ C}
(F : C ⥤ D) (c : cone (K ⋙ F)) :
  cone_to_diagram_of_structured_arrows F c ⋙ structured_arrow.proj c.X F = K := by
{ apply functor.hext; tidy }

variables (J : Type v₁) [small_category J] [fin_category J]

-- noncomputable
section end
variable {J}
@[simps]
def diagram_of_structured_arrows_of_extend {K : J ⥤ C} (F : C ⥤ D) (c : cone (K ⋙ F)) {X : D}
  (f : X ⟶ c.X) : J ⥤ structured_arrow X F :=
{ obj := λ j, structured_arrow.mk (f ≫ c.π.app j),
  map := λ j k g, structured_arrow.hom_mk (K.map g)
    (by simp only [structured_arrow.mk_hom_eq_self, category.assoc, @category.id_comp _ _ c.X,
      ← c.π.naturality g, ← functor.comp_map, functor.const.obj_map]),
  map_id' := λ X, by simpa,
  map_comp' := λ X Y Z g h, by { ext, simp } }

-- variables (F : C ⥤ D) [representably_flat F] [fin_category J]
variables {K : J ⥤ C} (F : C ⥤ D) (c : cone K)

@[simps]
def cone_of_structured_arrows_of_extend {X : D} (f : X ⟶ F.obj c.X) :
  cone (diagram_of_structured_arrows_of_extend F (F.map_cone c) f) :=
{ X := structured_arrow.mk f,
  π := { app := λ j, structured_arrow.hom_mk (c.π.app j) rfl,
         naturality' := λ j k g, by { ext, dsimp, simp } } }

variables [representably_flat F] {c} (hc : is_limit c) (s : cone (K ⋙ F))
include hc

noncomputable def lift : s.X ⟶ F.obj c.X :=
begin
let s' := is_cofiltered.cone (cone_to_diagram_of_structured_arrows F s),
exact s'.X.hom ≫ F.map (hc.lift ((cones.postcompose (eq_to_hom (cone_diagram_proj F s))).obj
  ((structured_arrow.proj s.X F).map_cone s'))),
end

lemma fac (x : J) : lift F hc s ≫ (F.map_cone c).π.app x = s.π.app x :=
by { unfold lift, simpa [←F.map_comp] }


lemma uniq {K : J ⥤ C} {c : cone K} (hc : is_limit c)
  (s : cone (K ⋙ F)) (f₁ f₂ : s.X ⟶ F.obj c.X)
  (h₁ : ∀ (j : J), f₁ ≫ (F.map_cone c).π.app j = s.π.app j)
  (h₂ : ∀ (j : J), f₂ ≫ (F.map_cone c).π.app j = s.π.app j) : f₁ = f₂ :=
begin
let c₁ := cone_of_structured_arrows_of_extend F c f₁,
let c₂ := cone_of_structured_arrows_of_extend F c f₂,
let eq_hom : diagram_of_structured_arrows_of_extend F (F.map_cone c) f₂ ⟶
  diagram_of_structured_arrows_of_extend F (F.map_cone c) f₁ :=
  { app := λ j, structured_arrow.hom_mk (𝟙 (K.obj j))
      (by { erw [F.map_id, category.comp_id], exact (h₂ j).trans (h₁ j).symm }),
    naturality' := λ j k f, by
      { ext, simp[@category.comp_id _ _ _ (K.obj k), @category.id_comp _ _ (K.obj j)] } },
let bicone := bicones_mk _ c₁ ((cones.postcompose eq_hom).obj c₂),
let c₀ := is_cofiltered.cone bicone,
let g₁ : c₀.X ⟶ c₁.X := c₀.π.app (bicones.left),
let g₂ : c₀.X ⟶ c₂.X := c₀.π.app (bicones.right),
have extend_eq : c.extend g₁.right = c.extend g₂.right,
{ unfold cone.extend, congr' 1,
  ext x, change g₁.right ≫ c.π.app x = g₂.right ≫ c.π.app x,
  injection (c₀.π.naturality (bicones_hom.left x)).symm.trans
    (c₀.π.naturality (bicones_hom.right x) : _) with _ h,
  convert h, exact (category.comp_id (c.π.app x)).symm },
have : g₁.right = g₂.right,
{ rw hc.uniq (c.extend g₁.right) g₁.right (λ j, by simp),
  rw hc.uniq (c.extend g₂.right) g₂.right (λ j, by simp),
  congr,
  exact extend_eq },
calc f₁ = 𝟙 _ ≫ f₁ : by simp
    ... = c₀.X.hom ≫ F.map g₁.right : g₁.w
    ... = c₀.X.hom ≫ F.map g₂.right : by { congr, exact this }
    ... = 𝟙 _ ≫ f₂ : g₂.w.symm
    ... = f₂ : by simp
end

end preserves_finite_limit_of_flat

noncomputable
def preserves_finite_limit_of_flat (F : C ⥤ D) [representably_flat F]
(J : Type v₁) [small_category J] [fin_category J]
: preserves_limits_of_shape J F := ⟨λ K, ⟨λ c hc,
{ lift := preserves_finite_limit_of_flat.lift F hc,
  fac' := preserves_finite_limit_of_flat.fac F hc,
  uniq' := λ s m h, by
  { apply preserves_finite_limit_of_flat.uniq F hc,
    exact h,
    exact preserves_finite_limit_of_flat.fac F hc s } }⟩⟩

end has_limit

section small_category
variables {C D : Type u₁} [small_category C] [small_category D]

/--
(Implementation)
The evaluation of `Lan F` at `X` is the colimit over the costrucuted arrows over `X`.
-/
lemma Lan_evaluation_eq_colim (E : Type u₂) [category.{u₁} E] (F : C ⥤ D) (X : D)
  [∀ (X : D), has_colimits_of_shape (costructured_arrow F X) E] :
  Lan F ⋙ (evaluation D E).obj X =
  ((whiskering_left _ _ E).obj (costructured_arrow.proj F X)) ⋙ colim :=
begin
  apply functor.hext,
  { intro Y, simp },
  intros Y₁ Y₂ f,
  simp only [functor.comp_map, evaluation_obj_map, whiskering_left_obj_map, Lan_map_app, heq_iff_eq],
  symmetry,
  apply (colimit.is_colimit (Lan.diagram F Y₁ X)).uniq { X := colimit _, ι := _ }
    (colim.map (whisker_left (costructured_arrow.proj F X) f)),
  intro Z,
  simp only [colimit.ι_map, colimit.cocone_ι, whisker_left_app, category.comp_id, category.assoc],
  transitivity f.app Z.left ≫ (colimit.ι (costructured_arrow.map Z.hom ⋙ Lan.diagram F Y₂ X :
    costructured_arrow F _ ⥤ _) (costructured_arrow.mk (𝟙 (F.obj Z.left))) : _)
    ≫ (colimit.pre (Lan.diagram F Y₂ X) (costructured_arrow.map Z.hom)),
  { rw colimit.ι_pre,
    congr,
    simp only [category.id_comp, costructured_arrow.map_mk],
    apply costructured_arrow.eq_mk },
  { congr }
end

/--
If `F : C ⥤ D` is a representably flat functor between small categories, then the functor
`Lan F.op` that takes presheaves over `C` to presheaves over `D` preserves finite limits.
-/
noncomputable
def Lan_presesrves_finite_limit_of_flat (F : C ⥤ D) [representably_flat F]
  (J : Type u₁) [small_category J] [fin_category J] :
  preserves_limits_of_shape J (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u₁)) :=
begin
  apply preserves_limits_of_shape_if_evaluation (Lan F.op : (Cᵒᵖ ⥤ Type u₁) ⥤ (Dᵒᵖ ⥤ Type u₁)) J,
  intro K,
  rw Lan_evaluation_eq_colim,
  haveI : is_filtered (costructured_arrow F.op K) :=
    is_filtered.of_equivalence (structured_arrow_op_equivalence F (unop K)),
  apply_instance
end

noncomputable
def extend_of_comp_yoneda_iso_Lan (F : C ⥤ D) :
  colimit_adj.extend_along_yoneda (F ⋙ yoneda) ≅ Lan F.op :=
adjunction.nat_iso_of_right_adjoint_nat_iso
  (colimit_adj.yoneda_adjunction (F ⋙ yoneda))
  (Lan.adjunction (Type u₁) F.op)
  (iso_whisker_right curried_yoneda_lemma' ((whiskering_left Cᵒᵖ Dᵒᵖ (Type u₁)).obj F.op : _))

noncomputable
def yoneda_comp_Lan (F : C ⥤ D) : F ⋙ yoneda ≅ yoneda ⋙ Lan F.op :=
(colimit_adj.is_extension_along_yoneda (F ⋙ yoneda)).symm ≪≫
  iso_whisker_left yoneda (extend_of_comp_yoneda_iso_Lan F)

noncomputable
def preserves_finite_limit_of_flat (F : C ⥤ D) [representably_flat F]
  (J : Type u₁) [small_category J] [fin_category J] :
  preserves_limits_of_shape J F := by {
  apply preserves_limits_of_shape_of_reflects_of_preserves F yoneda,
  haveI := Lan_presesrves_finite_limit_of_flat F J,
  exact preserves_limits_of_shape_of_nat_iso (yoneda_comp_Lan F).symm,
  apply_instance
}

-- local attribute[ext] functor.hext

end small_category

end category_theory
