/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import category_theory.monoidal.coherence_lemmas
import category_theory.closed.monoidal
import tactic.apply_fun

/-!
# Rigid (autonomous) monoidal categories

This file defines rigid (autonomous) monoidal categories and the necessary theory about
exact pairings and duals.

## Main definitions

* `exact_pairing` of two objects of a monoidal category
* Type classes `has_left_dual` and `has_right_dual` that capture that a pairing exists
* The `right_adjoint_mate f` as a morphism `fᘁ : Yᘁ ⟶ Xᘁ` for a morphism `f : X ⟶ Y`
* The classes of `right_rigid_category`, `left_rigid_category` and `rigid_category`

## Main statements

* `comp_right_adjoint_mate`: The adjoint mates of the composition is the composition of
  adjoint mates.

## Notations

* `η_` and `ε_` denote the coevaluation and evaluation morphism of an exact pairing.
* `Xᘁ` and `ᘁX` denote the right and left dual of an object, as well as the adjoint
  mate of a morphism.

## Future work

* Show that `X ⊗ Y` and `Yᘁ ⊗ Xᘁ` form an exact pairing.
* Show that the left adjoint mate of the right adjoint mate of a morphism is the morphism itself.
* Simplify constructions in the case where a symmetry or braiding is present.
* Show that `ᘁ` gives an equivalence of categories `C ≅ (Cᵒᵖ)ᴹᵒᵖ`.
* Define pivotal categories (rigid categories equipped with a natural isomorphism `ᘁᘁ ≅ 𝟙 C`).

## Notes

Although we construct the adjunction `tensor_left Y ⊣ tensor_left X` from `exact_pairing X Y`,
this is not a bijective correspondence.
I think the correct statement is that `tensor_left Y` and `tensor_left X` are
module endofunctors of `C` as a right `C` module category,
and `exact_pairing X Y` is in bijection with adjunctions compatible with this right `C` action.

## References

* <https://ncatlab.org/nlab/show/rigid+monoidal+category>

## Tags

rigid category, monoidal category

-/
open category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃
noncomputable theory

namespace category_theory

variables {C : Type u₁} [category.{v₁} C] [monoidal_category C]

/-- An exact pairing is a pair of objects `X Y : C` which admit
  a coevaluation and evaluation morphism which fulfill two triangle equalities. -/
class exact_pairing (X Y : C) :=
(coevaluation [] : 𝟙_ C ⟶ X ⊗ Y)
(evaluation [] : Y ⊗ X ⟶ 𝟙_ C)
(coevaluation_evaluation' [] :
  (𝟙 Y ⊗ coevaluation) ≫ (α_ _ _ _).inv ≫ (evaluation ⊗ 𝟙 Y)
  = (ρ_ Y).hom ≫ (λ_ Y).inv . obviously)
(evaluation_coevaluation' [] :
  (coevaluation ⊗ 𝟙 X) ≫ (α_ _ _ _).hom ≫ (𝟙 X ⊗ evaluation)
  = (λ_ X).hom ≫ (ρ_ X).inv . obviously)

open exact_pairing

notation `η_` := exact_pairing.coevaluation
notation `ε_` := exact_pairing.evaluation

restate_axiom coevaluation_evaluation'
attribute [simp, reassoc] exact_pairing.coevaluation_evaluation
restate_axiom evaluation_coevaluation'
attribute [simp, reassoc] exact_pairing.evaluation_coevaluation

instance exact_pairing_unit : exact_pairing (𝟙_ C) (𝟙_ C) :=
{ coevaluation := (ρ_ _).inv,
  evaluation := (ρ_ _).hom,
  coevaluation_evaluation' := by coherence,
  evaluation_coevaluation' := by coherence, }

/-- A class of objects which have a right dual. -/
class has_right_dual (X : C) :=
(right_dual : C)
[exact : exact_pairing X right_dual]

/-- A class of objects with have a left dual. -/
class has_left_dual (Y : C) :=
(left_dual : C)
[exact : exact_pairing left_dual Y]

attribute [instance] has_right_dual.exact
attribute [instance] has_left_dual.exact

open exact_pairing has_right_dual has_left_dual monoidal_category

prefix `ᘁ`:1025 := left_dual
postfix `ᘁ`:1025 := right_dual

instance has_right_dual_unit : has_right_dual (𝟙_ C) :=
{ right_dual := 𝟙_ C }

instance has_left_dual_unit : has_left_dual (𝟙_ C) :=
{ left_dual := 𝟙_ C }

instance has_right_dual_left_dual {X : C} [has_left_dual X] : has_right_dual (ᘁX) :=
{ right_dual := X }

instance has_left_dual_right_dual {X : C} [has_right_dual X] : has_left_dual Xᘁ :=
{ left_dual := X }

@[simp]
lemma left_dual_right_dual {X : C} [has_right_dual X] : ᘁ(Xᘁ) = X := rfl

@[simp]
lemma right_dual_left_dual {X : C} [has_left_dual X] : (ᘁX)ᘁ = X := rfl

/-- The right adjoint mate `fᘁ : Xᘁ ⟶ Yᘁ` of a morphism `f : X ⟶ Y`. -/
def right_adjoint_mate {X Y : C} [has_right_dual X] [has_right_dual Y] (f : X ⟶ Y) : Yᘁ ⟶ Xᘁ :=
(ρ_ _).inv ≫ (𝟙 _ ⊗ η_ _ _) ≫ (𝟙 _ ⊗ (f ⊗ 𝟙 _))
 ≫ (α_ _ _ _).inv ≫ ((ε_ _ _) ⊗ 𝟙 _) ≫ (λ_ _).hom

/-- The left adjoint mate `ᘁf : ᘁY ⟶ ᘁX` of a morphism `f : X ⟶ Y`. -/
def left_adjoint_mate {X Y : C} [has_left_dual X] [has_left_dual Y] (f : X ⟶ Y) : ᘁY ⟶ ᘁX :=
(λ_ _).inv ≫ (η_ (ᘁX) X ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ f) ⊗ 𝟙 _)
 ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).hom

notation f `ᘁ` := right_adjoint_mate f
notation `ᘁ` f := left_adjoint_mate f

@[simp]
lemma right_adjoint_mate_id {X : C} [has_right_dual X] : (𝟙 X)ᘁ = 𝟙 (Xᘁ) :=
by simp only [right_adjoint_mate, monoidal_category.tensor_id, category.id_comp,
  coevaluation_evaluation_assoc, category.comp_id, iso.inv_hom_id]

@[simp]
lemma left_adjoint_mate_id {X : C} [has_left_dual X] : ᘁ(𝟙 X) = 𝟙 (ᘁX) :=
by simp only [left_adjoint_mate, monoidal_category.tensor_id, category.id_comp,
  evaluation_coevaluation_assoc, category.comp_id, iso.inv_hom_id]

lemma right_adjoint_mate_comp {X Y Z : C} [has_right_dual X]
  [has_right_dual Y] {f : X ⟶ Y} {g : Xᘁ ⟶ Z} :
  fᘁ ≫ g
  = (ρ_ Yᘁ).inv ≫ (𝟙 _ ⊗ η_ X Xᘁ) ≫ (𝟙 _ ⊗ f ⊗ g)
    ≫ (α_ Yᘁ Y Z).inv ≫ (ε_ Y Yᘁ ⊗ 𝟙 _) ≫ (λ_ Z).hom :=
begin
  dunfold right_adjoint_mate,
  rw [category.assoc, category.assoc, associator_inv_naturality_assoc,
    associator_inv_naturality_assoc, ←tensor_id_comp_id_tensor g, category.assoc, category.assoc,
    category.assoc, category.assoc, id_tensor_comp_tensor_id_assoc, ←left_unitor_naturality,
    tensor_id_comp_id_tensor_assoc],
end

lemma left_adjoint_mate_comp {X Y Z : C} [has_left_dual X] [has_left_dual Y]
  {f : X ⟶ Y} {g : ᘁX ⟶ Z} :
  ᘁf ≫ g
  = (λ_ _).inv ≫ (η_ (ᘁX) X ⊗ 𝟙 _) ≫ ((g ⊗ f) ⊗ 𝟙 _)
    ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).hom :=
begin
  dunfold left_adjoint_mate,
  rw [category.assoc, category.assoc, associator_naturality_assoc, associator_naturality_assoc,
  ←id_tensor_comp_tensor_id _ g, category.assoc, category.assoc, category.assoc, category.assoc,
  tensor_id_comp_id_tensor_assoc, ←right_unitor_naturality, id_tensor_comp_tensor_id_assoc],
end

/-- The composition of right adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
lemma comp_right_adjoint_mate {X Y Z : C}
  [has_right_dual X] [has_right_dual Y] [has_right_dual Z] {f : X ⟶ Y} {g : Y ⟶ Z} :
  (f ≫ g)ᘁ = gᘁ ≫ fᘁ :=
begin
  rw right_adjoint_mate_comp,
  simp only [right_adjoint_mate, comp_tensor_id, iso.cancel_iso_inv_left, id_tensor_comp,
    category.assoc],
  symmetry, iterate 5 { transitivity, rw [←category.id_comp g, tensor_comp] },
  rw ←category.assoc,
  symmetry, iterate 2 { transitivity, rw ←category.assoc }, apply eq_whisker,
  repeat { rw ←id_tensor_comp }, congr' 1,
  rw [←id_tensor_comp_tensor_id (λ_ Xᘁ).hom g, id_tensor_right_unitor_inv, category.assoc,
    category.assoc, right_unitor_inv_naturality_assoc, ←associator_naturality_assoc, tensor_id,
    tensor_id_comp_id_tensor_assoc, ←associator_naturality_assoc],
  slice_rhs 2 3 { rw [←tensor_comp, tensor_id, category.comp_id,
    ←category.id_comp (η_ Y Yᘁ), tensor_comp] },
  rw [←id_tensor_comp_tensor_id _ (η_ Y Yᘁ), ←tensor_id],
  repeat { rw category.assoc },
  rw [pentagon_hom_inv_assoc, ←associator_naturality_assoc, associator_inv_naturality_assoc],
  slice_rhs 5 7 { rw [←comp_tensor_id, ←comp_tensor_id, evaluation_coevaluation, comp_tensor_id] },
  rw associator_inv_naturality_assoc,
  slice_rhs 4 5 { rw [←tensor_comp, left_unitor_naturality, tensor_comp] },
  repeat { rw category.assoc },
  rw [triangle_assoc_comp_right_inv_assoc, ←left_unitor_tensor_assoc,
    left_unitor_naturality_assoc, unitors_equal, ←category.assoc, ←category.assoc], simp
end

/-- The composition of left adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
lemma comp_left_adjoint_mate {X Y Z : C}
  [has_left_dual X] [has_left_dual Y] [has_left_dual Z] {f : X ⟶ Y} {g : Y ⟶ Z} :
  ᘁ(f ≫ g) = ᘁg ≫ ᘁf :=
begin
  rw left_adjoint_mate_comp,
  simp only [left_adjoint_mate, id_tensor_comp, iso.cancel_iso_inv_left,
    comp_tensor_id, category.assoc],
  symmetry, iterate 5 { transitivity, rw [←category.id_comp g, tensor_comp] },
  rw ← category.assoc,
  symmetry, iterate 2 { transitivity, rw ←category.assoc }, apply eq_whisker,
  repeat { rw ←comp_tensor_id }, congr' 1,
  rw [←tensor_id_comp_id_tensor g (ρ_ (ᘁX)).hom, left_unitor_inv_tensor_id, category.assoc,
    category.assoc, left_unitor_inv_naturality_assoc, ←associator_inv_naturality_assoc, tensor_id,
    id_tensor_comp_tensor_id_assoc, ←associator_inv_naturality_assoc],
  slice_rhs 2 3 { rw [←tensor_comp, tensor_id, category.comp_id,
    ←category.id_comp (η_ (ᘁY) Y), tensor_comp] },
  rw [←tensor_id_comp_id_tensor (η_ (ᘁY) Y), ←tensor_id],
  repeat { rw category.assoc },
  rw [pentagon_inv_hom_assoc, ←associator_inv_naturality_assoc, associator_naturality_assoc],
  slice_rhs 5 7 { rw [←id_tensor_comp, ←id_tensor_comp, coevaluation_evaluation, id_tensor_comp ]},
  rw associator_naturality_assoc,
  slice_rhs 4 5 { rw [←tensor_comp, right_unitor_naturality, tensor_comp] },
  repeat { rw category.assoc },
  rw [triangle_assoc_comp_left_inv_assoc, ←right_unitor_tensor_assoc,
    right_unitor_naturality_assoc, ←unitors_equal, ←category.assoc, ←category.assoc], simp
end

/-- Transport an exact pairing across an isomorphism in the first argument. -/
def exact_pairing_congr_left {X X' Y : C} [exact_pairing X' Y] (i : X ≅ X') : exact_pairing X Y :=
{ evaluation := (𝟙 Y ⊗ i.hom) ≫ ε_ _ _,
  coevaluation := η_ _ _ ≫ (i.inv ⊗ 𝟙 Y),
  evaluation_coevaluation' := begin
    rw [id_tensor_comp, comp_tensor_id],
    slice_lhs 2 3 { rw [associator_naturality], },
    slice_lhs 3 4 { rw [tensor_id, tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id], },
    slice_lhs 4 5 { rw [tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id], },
    slice_lhs 2 3 { rw [←associator_naturality], },
    slice_lhs 1 2 { rw [tensor_id, tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id], },
    slice_lhs 2 4 { rw [evaluation_coevaluation], },
    slice_lhs 1 2 { rw [left_unitor_naturality], },
    slice_lhs 3 4 { rw [←right_unitor_inv_naturality], },
    simp,
  end,
  coevaluation_evaluation' := begin
    rw [id_tensor_comp, comp_tensor_id],
    simp only [iso.inv_hom_id_assoc, associator_conjugation, category.assoc],
    slice_lhs 2 3 { rw [←tensor_comp], simp, },
    simp,
  end, }

/-- Transport an exact pairing across an isomorphism in the second argument. -/
def exact_pairing_congr_right {X Y Y' : C} [exact_pairing X Y'] (i : Y ≅ Y') : exact_pairing X Y :=
{ evaluation := (i.hom ⊗ 𝟙 X) ≫ ε_ _ _,
  coevaluation := η_ _ _ ≫ (𝟙 X ⊗ i.inv),
  evaluation_coevaluation' := begin
    rw [id_tensor_comp, comp_tensor_id],
    simp only [iso.inv_hom_id_assoc, associator_conjugation, category.assoc],
    slice_lhs 3 4 { rw [←tensor_comp], simp, },
    simp,
  end,
  coevaluation_evaluation' := begin
    rw [id_tensor_comp, comp_tensor_id],
    slice_lhs 3 4 { rw [←associator_inv_naturality], },
    slice_lhs 2 3 { rw [tensor_id, id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
    slice_lhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
    slice_lhs 3 4 { rw [associator_inv_naturality], },
    slice_lhs 4 5 { rw [tensor_id, id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
    slice_lhs 2 4 { rw [coevaluation_evaluation], },
    slice_lhs 1 2 { rw [right_unitor_naturality], },
    slice_lhs 3 4 { rw [←left_unitor_inv_naturality], },
    simp,
  end, }

/-- Transport an exact pairing across isomorphisms. -/
def exact_pairing_congr {X X' Y Y' : C} [exact_pairing X' Y'] (i : X ≅ X') (j : Y ≅ Y') :
  exact_pairing X Y :=
begin
  haveI : exact_pairing X' Y := exact_pairing_congr_right j,
  exact exact_pairing_congr_left i,
end

/-- The bijection on hom-sets `(Yᘁ ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)`
given by "pulling the string on the left" down or up, using right duals. -/
def exact_pairing_tensor_left_hom_equiv (X Y Y' Z : C) [exact_pairing Y Y'] :
  (Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z) :=
begin
  letI : has_right_dual Y := ⟨Y'⟩,
  change (Yᘁ ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z),
  exact
  { to_fun := λ f, (λ_ _).inv ≫ (η_ _ _ ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ f),
    inv_fun := λ f, (𝟙 Yᘁ ⊗ f) ≫ (α_ _ _ _).inv ≫ (ε_ _ _ ⊗ 𝟙 _) ≫ (λ_ _).hom,
    left_inv := λ f, begin
      dsimp,
      simp only [id_tensor_comp],
      slice_lhs 4 5 { rw associator_inv_naturality, },
      slice_lhs 5 6 { rw [tensor_id, id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
      slice_lhs 2 5 { simp only [←tensor_id, associator_inv_conjugation], },
      have c : (α_ Yᘁ (Y ⊗ Yᘁ) X).hom ≫ (𝟙 Yᘁ ⊗ (α_ Y Yᘁ X).hom) ≫ (α_ Yᘁ Y (Yᘁ ⊗ X)).inv ≫
        (α_ (Yᘁ ⊗ Y) Yᘁ X).inv = (α_ _ _ _).inv ⊗ 𝟙 _, pure_coherence,
      slice_lhs 4 7 { rw c, },
      slice_lhs 3 5 { rw [←comp_tensor_id, ←comp_tensor_id, coevaluation_evaluation], },
      simp only [left_unitor_conjugation],
      coherence,
    end,
    right_inv := λ f, begin
      dsimp,
      simp only [id_tensor_comp],
      slice_lhs 3 4 { rw ←associator_naturality, },
      slice_lhs 2 3 { rw [tensor_id, tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id], },
      slice_lhs 3 6 { simp only [←tensor_id, associator_inv_conjugation], },
      have c : (α_ (Y ⊗ Yᘁ) Y Z).hom ≫ (α_ Y Yᘁ (Y ⊗ Z)).hom ≫ (𝟙 Y ⊗ (α_ Yᘁ Y Z).inv) ≫
        (α_ Y (Yᘁ ⊗ Y) Z).inv = (α_ _ _ _).hom ⊗ 𝟙 Z, pure_coherence,
      slice_lhs 5 8 { rw c, },
      slice_lhs 4 6 { rw [←comp_tensor_id, ←comp_tensor_id, evaluation_coevaluation], },
      simp only [left_unitor_conjugation],
      coherence,
    end, }
end

/-- The bijection on hom-sets `(Yᘁ ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)`
given by "pulling the string on the left" down or up, using right duals. -/
def right_dual_tensor_left_hom_equiv (X Y Z : C) [has_right_dual Y] :
  (Yᘁ ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z) :=
exact_pairing_tensor_left_hom_equiv X Y Yᘁ Z

lemma right_dual_tensor_left_hom_equiv_symm_naturality {X X' Y Z : C} [has_right_dual Y]
  (f : X ⟶ X') (g : X' ⟶ Y ⊗ Z) :
  (right_dual_tensor_left_hom_equiv X Y Z).symm (f ≫ g) =
    (𝟙 _ ⊗ f) ≫ (right_dual_tensor_left_hom_equiv X' Y Z).symm g :=
begin
  dsimp [right_dual_tensor_left_hom_equiv, exact_pairing_tensor_left_hom_equiv],
  simp only [id_tensor_comp, category.assoc],
end

lemma right_dual_tensor_left_hom_equiv_naturality
  {X Y Z Z' : C} [has_right_dual Y] (f : Yᘁ ⊗ X ⟶ Z) (g : Z ⟶ Z') :
  (right_dual_tensor_left_hom_equiv X Y Z') (f ≫ g) =
    (right_dual_tensor_left_hom_equiv X Y Z) f ≫ (𝟙 Y ⊗ g) :=
begin
  dsimp [right_dual_tensor_left_hom_equiv, exact_pairing_tensor_left_hom_equiv],
  simp only [id_tensor_comp, category.assoc],
end

/--
If `Y` has a right dual, then the functor `tensor_left Yᘁ` is left adjoint to `tensor_left Y`.
-/
def right_dual_tensor_left_adjunction (Y : C) [has_right_dual Y] : tensor_left Yᘁ ⊣ tensor_left Y :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Z, right_dual_tensor_left_hom_equiv X Y Z,
  hom_equiv_naturality_left_symm' :=
    λ X X' Z f g, right_dual_tensor_left_hom_equiv_symm_naturality f g,
  hom_equiv_naturality_right' :=
    λ X Z Z' f g, right_dual_tensor_left_hom_equiv_naturality f g, }

/--
If `Y` has a left dual, then the functor `tensor_left Yᘁ` is right adjoint to `tensor_left Y`.
-/
def left_dual_tensor_left_adjunction (Y : C) [has_left_dual Y] : tensor_left Y ⊣ tensor_left (ᘁY) :=
by { change tensor_left (ᘁY)ᘁ ⊣ tensor_left (ᘁY), apply right_dual_tensor_left_adjunction, }

@[priority 100]
instance closed_of_has_left_dual (Y : C) [has_left_dual Y] : closed Y :=
{ is_adj := ⟨_, left_dual_tensor_left_adjunction Y⟩, }

lemma right_dual_tensor_left_hom_equiv_tensor {X X' Y Z Z' : C} [has_right_dual Y]
  (f : X ⟶ Y ⊗ Z) (g : X' ⟶ Z') :
  (right_dual_tensor_left_hom_equiv (X ⊗ X') Y (Z ⊗ Z')).symm ((f ⊗ g) ≫ (α_ _ _ _).hom) =
    (α_ _ _ _).inv ≫ ((right_dual_tensor_left_hom_equiv X Y Z).symm f ⊗ g) :=
begin
  dsimp [right_dual_tensor_left_hom_equiv, exact_pairing_tensor_left_hom_equiv],
  simp only [id_tensor_comp],
  simp only [associator_inv_conjugation],
  slice_lhs 2 2 { rw ←id_tensor_comp_tensor_id, },
  conv_rhs { rw [←id_tensor_comp_tensor_id, comp_tensor_id, comp_tensor_id], },
  simp, coherence,
end

@[simp]
lemma right_dual_tensor_left_hom_equiv_symm_coevaluation_comp_id_tensor
  {Y Z : C} [has_right_dual Y] (f : Yᘁ ⟶ Z) :
  (right_dual_tensor_left_hom_equiv _ _ _).symm (η_ _ _ ≫ (𝟙 Y ⊗ f)) = (ρ_ _).hom ≫ f :=
begin
  dsimp [right_dual_tensor_left_hom_equiv, exact_pairing_tensor_left_hom_equiv],
  rw id_tensor_comp,
  slice_lhs 2 3 { rw associator_inv_naturality, },
  slice_lhs 3 4 { rw tensor_id, rw id_tensor_comp_tensor_id, rw ← tensor_id_comp_id_tensor, },
  slice_lhs 1 3 { rw coevaluation_evaluation, },
  simp,
end

@[simp]
lemma right_dual_tensor_left_hom_equiv_symm_coevaluation_comp_tensor_id
  {X Y : C} [has_right_dual X] [has_right_dual Y] (f : X ⟶ Y) :
  (right_dual_tensor_left_hom_equiv _ _ _).symm (η_ _ _ ≫ (f ⊗ 𝟙 Xᘁ)) = (ρ_ _).hom ≫ fᘁ :=
begin
  dsimp [right_dual_tensor_left_hom_equiv, exact_pairing_tensor_left_hom_equiv, right_adjoint_mate],
  simp,
end

-- Next two lemmas passing `fᘁ` through (co)evaluations.

lemma coevaluation_comp_right_adjoint_mate_comp
  {X Y : C} [has_right_dual X] [has_right_dual Y] (f : X ⟶ Y) :
  η_ Y Yᘁ ≫ (𝟙 _ ⊗ fᘁ) = η_ _ _ ≫ (f ⊗ 𝟙 _) :=
begin
  apply_fun (right_dual_tensor_left_hom_equiv _ Y _).symm,
  simp,
end

-- It feels like we shouldn't have to work so hard at this point,
-- but I've failed to deduce this from facts above more easily than doing it from scratch.
lemma right_adjoint_mate_comp_evaluation
  {X Y : C} [has_right_dual X] [has_right_dual Y] (f : X ⟶ Y) :
  (fᘁ ⊗ 𝟙 X) ≫ ε_ _ _ = (𝟙 _ ⊗ f) ≫ ε_ _ _ :=
begin
  dunfold right_adjoint_mate,
  simp only [comp_tensor_id, category.assoc],
  rw [←left_unitor_tensor', category.assoc, ←left_unitor_naturality],
  slice_lhs 5 6 { rw associator_naturality, },
  slice_lhs 6 7 { rw tensor_id, rw tensor_id_comp_id_tensor, rw ←id_tensor_comp_tensor_id, },
  slice_lhs 3 4 { rw [←comp_tensor_id], rw [associator_inv_naturality], rw [comp_tensor_id], },
  slice_lhs 4 5 { rw [associator_naturality], },
  slice_lhs 5 6 { rw [tensor_id], rw tensor_id_comp_id_tensor, rw ←id_tensor_comp_tensor_id, },
  slice_lhs 2 5 { simp only [←tensor_id, associator_conjugation], },
  have c : (α_ Yᘁ (X ⊗ Xᘁ) X).inv ≫ ((α_ Yᘁ X Xᘁ).inv ⊗ 𝟙 X) ≫ (α_ (Yᘁ ⊗ X) Xᘁ X).hom ≫
    (α_ Yᘁ X (Xᘁ ⊗ X)).hom = 𝟙 _ ⊗ (α_ _ _ _).hom, pure_coherence,
  slice_lhs 4 7 { rw c, },
  slice_lhs 3 5 { rw ←id_tensor_comp, rw ←id_tensor_comp, rw evaluation_coevaluation, },
  simp only [associator_conjugation, right_unitor_conjugation],
  coherence,
end

/-- Right duals are isomorphic. -/
def right_dual_iso {X Y₁ Y₂ : C} (_ : exact_pairing X Y₁) (_ : exact_pairing X Y₂) :
  Y₁ ≅ Y₂ :=
{ hom := @right_adjoint_mate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X),
  inv := @right_adjoint_mate C _ _ X X ⟨Y₁⟩ ⟨Y₂⟩ (𝟙 X),
  hom_inv_id' := by rw [←comp_right_adjoint_mate, category.comp_id, right_adjoint_mate_id],
  inv_hom_id' := by rw [←comp_right_adjoint_mate, category.comp_id, right_adjoint_mate_id] }

/-- Left duals are isomorphic. -/
def left_dual_iso {X₁ X₂ Y : C} (p₁ : exact_pairing X₁ Y) (p₂ : exact_pairing X₂ Y) :
  X₁ ≅ X₂ :=
{ hom := @left_adjoint_mate C _ _ Y Y ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y),
  inv := @left_adjoint_mate C _ _ Y Y ⟨X₁⟩ ⟨X₂⟩ (𝟙 Y),
  hom_inv_id' := by rw [←comp_left_adjoint_mate, category.comp_id, left_adjoint_mate_id],
  inv_hom_id' := by rw [←comp_left_adjoint_mate, category.comp_id, left_adjoint_mate_id] }

@[simp]
lemma right_dual_iso_id {X Y : C} (p : exact_pairing X Y) :
  right_dual_iso p p = iso.refl Y :=
by { ext, simp only [right_dual_iso, iso.refl_hom, right_adjoint_mate_id] }

@[simp]
lemma left_dual_iso_id {X Y : C} (p : exact_pairing X Y) :
  left_dual_iso p p = iso.refl X :=
by { ext, simp only [left_dual_iso, iso.refl_hom, left_adjoint_mate_id] }

/-- A right rigid monoidal category is one in which every object has a right dual. -/
class right_rigid_category (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
[right_dual : Π (X : C), has_right_dual X]

/-- A left rigid monoidal category is one in which every object has a right dual. -/
class left_rigid_category (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
[left_dual : Π (X : C), has_left_dual X]

attribute [instance, priority 100] right_rigid_category.right_dual
attribute [instance, priority 100] left_rigid_category.left_dual

@[priority 100]
instance monoidal_closed_of_left_rigid_category
  (C : Type u) [category.{v} C] [monoidal_category.{v} C] [left_rigid_category C] :
  monoidal_closed C :=
{ closed' := λ X, by apply_instance, }

/-- A rigid monoidal category is a monoidal category which is left rigid and right rigid. -/
class rigid_category (C : Type u) [category.{v} C] [monoidal_category.{v} C]
  extends right_rigid_category C, left_rigid_category C

end category_theory
