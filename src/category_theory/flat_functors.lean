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

lemma flat_preserves_products [has_equalizers C] (F : C ⥤ D) [representably_flat F]
: preserves_limits_of_shape walking_parallel_pair F :=
begin
  apply preserves_equalizers_mk,
  intros X Y f g,
  apply preserves_equalizer_mk,
  intros Z h w is_lim,
  apply (is_limit_map_cone_fork_equiv F w).2,
  apply fork.is_limit.mk',
  intro s,
  let c0 : structured_arrow _ F := structured_arrow.mk s.ι,
  let c1 : structured_arrow _ F := structured_arrow.mk (s.π.app walking_parallel_pair.one),
  let f' : c0 ⟶ c1 := structured_arrow.hom_mk f sorry,
    -- (by { convert (s.π.naturality left).symm, erw category.id_comp, refl }),
  let g' : c0 ⟶ c1 := structured_arrow.hom_mk g sorry,
    -- (by { convert (s.π.naturality right).symm, erw category.id_comp, refl }),
  let W := is_cofiltered.eq f' g', simp at W,
  let s' := (fork.of_ι (is_cofiltered.eq_hom f' g').right
    (by injection is_cofiltered.eq_condition f' g')),
  -- let eq : structured_arrow _ F := structured_arrow.mk
  --   ((is_cofiltered.eq f' g').hom ≫ F.map (is_lim.lift s')),
  use (is_cofiltered.eq f' g').hom ≫ F.map (is_lim.lift s'),
  split, admit,
  -- { simp,
  --   rw ← F.map_comp,
  --   have := is_lim.fac s' walking_parallel_pair.zero, simp at this,
  --   rw this,
  --   rw ← (is_cofiltered.eq_hom f' g').w,
  --   erw category.id_comp,
  --   refl },
  { intros m hm,
  let W' : structured_arrow _ F := structured_arrow.mk m,
  let h' : W' ⟶ c0 := structured_arrow.hom_mk h hm,
  let V := is_cofiltered.cone (cospan h' (is_cofiltered.eq_hom f' g')),
  -- have := (is_cofiltered.min_to_left m' (is_cofiltered.eq f' g') : min ⟶ m').right ≫ h,
  let V_fork : fork f'.right g'.right := fork.of_ι
    ((V.π.app walking_cospan.left).right ≫ h) (by simp[w]),
  have := is_lim.uniq V_fork,
  }
end


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
