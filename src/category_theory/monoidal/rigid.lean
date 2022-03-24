/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Yuma Mizuno
-/

import tactic.coherence


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
* Connect this definition to `monoidal_closed`: an object with a (left?) dual is
  a closed object `X` such that the right adjoint of `X ⊗ -` is given by `Y ⊗ -` for some `Y`.
* Show that `ᘁ` gives an equivalence of categories `C ≅ (Cᵒᵖ)ᴹᵒᵖ`.
* Define pivotal categories (rigid categories equipped with a natural isomorphism `ᘁᘁ ≅ 𝟙 C`).

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
attribute [reassoc, simp] exact_pairing.coevaluation_evaluation
restate_axiom evaluation_coevaluation'
attribute [reassoc, simp] exact_pairing.evaluation_coevaluation

instance exact_pairing_unit : exact_pairing (𝟙_ C) (𝟙_ C) :=
{ coevaluation := (ρ_ _).inv,
  evaluation := (ρ_ _).hom,
  coevaluation_evaluation' := by
  { rw[monoidal_category.triangle_assoc_comp_right,
      monoidal_category.unitors_inv_equal,
      monoidal_category.unitors_equal], simp },
  evaluation_coevaluation' := by
  { rw[monoidal_category.triangle_assoc_comp_right_inv_assoc,
      monoidal_category.unitors_inv_equal,
      monoidal_category.unitors_equal], simp } }

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

/-- A rigid monoidal category is a monoidal category which is left rigid and right rigid. -/
class rigid_category (C : Type u) [category.{v} C] [monoidal_category.{v} C]
  extends right_rigid_category C, left_rigid_category C

section tensor
variables {X₁ Y₁ X₂ Y₂ : C}

open category

/-- Auxiliary definition for `exact_pairing_tensor`. -/
def tensor_evaluation (p₁ : exact_pairing X₁ Y₁) (p₂ : exact_pairing X₂ Y₂) :
  (Y₂ ⊗ Y₁) ⊗ X₁ ⊗ X₂ ⟶ 𝟙_ C :=
(α_ Y₂ Y₁ (X₁ ⊗ X₂)).hom ≫ (𝟙 Y₂ ⊗ (α_ Y₁ X₁ X₂).inv) ≫ (𝟙 Y₂ ⊗ p₁.evaluation ⊗ 𝟙 X₂) ≫
  ((𝟙 Y₂ ⊗ ((p₂.coevaluation ⊗ 𝟙 X₂) ≫ (α_ X₂ Y₂ X₂).hom ≫ (𝟙 X₂ ⊗ p₂.evaluation))) ≫
    (α_ Y₂ X₂ (𝟙_ C)).inv) ≫ (p₂.evaluation ⊗ 𝟙 (𝟙_ C)) ≫ (ρ_ (𝟙_ C)).hom

lemma tensor_evaluation_eq (p₁ : exact_pairing X₁ Y₁) (p₂ : exact_pairing X₂ Y₂) :
tensor_evaluation p₁ p₂ =
  (α_ Y₂ Y₁ (X₁ ⊗ X₂)).hom ≫ (𝟙 Y₂ ⊗ (α_ Y₁ X₁ X₂).inv) ≫ (𝟙 Y₂ ⊗ p₁.evaluation ⊗ 𝟙 X₂) ≫
    ((𝟙 Y₂ ⊗ ((p₂.coevaluation ⊗ 𝟙 X₂) ≫ (α_ X₂ Y₂ X₂).hom ≫ (𝟙 X₂ ⊗ p₂.evaluation))) ≫
      (α_ Y₂ X₂ (𝟙_ C)).inv) ≫ (p₂.evaluation ⊗ 𝟙 (𝟙_ C)) ≫ (ρ_ (𝟙_ C)).hom :=
rfl

/-- Another expression for `tensor_evaluation`. -/
lemma tensor_evaluation_eq' (p₁ : exact_pairing X₁ Y₁) (p₂ : exact_pairing X₂ Y₂) :
  tensor_evaluation p₁ p₂ = (α_ Y₂ Y₁ (X₁ ⊗ X₂)).hom ≫ (𝟙 Y₂ ⊗ (α_ Y₁ X₁ X₂).inv) ≫
    (𝟙 Y₂ ⊗ p₁.evaluation ⊗ 𝟙 X₂) ≫ (α_ Y₂ (𝟙_ C) X₂).inv ≫
      (((𝟙 Y₂ ⊗ p₂.coevaluation) ≫ (α_ Y₂ X₂ Y₂).inv ≫ (p₂.evaluation ⊗ 𝟙 Y₂)) ⊗ 𝟙 X₂) ≫
        (α_ (𝟙_ C) Y₂ X₂).hom ≫ (𝟙 (𝟙_ C) ⊗ p₂.evaluation) ≫ (λ_ (𝟙_ C)).hom :=
begin
  rw [tensor_evaluation_eq, left_unitor_naturality, right_unitor_naturality,
    coevaluation_evaluation, evaluation_coevaluation],
  congr' 3, simp_rw ←assoc, congr' 1,
  coherence
end

/-- Auxiliary definition for `tensor_coevaluation`. -/
def tensor_coevaluation (p₁ : exact_pairing X₁ Y₁) (p₂ : exact_pairing X₂ Y₂) :
  𝟙_ C ⟶ (X₁ ⊗ X₂) ⊗ Y₂ ⊗ Y₁ :=
(λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ p₁.coevaluation) ≫ (α_ (𝟙_ C) X₁ Y₁).inv ≫
  (((p₁.coevaluation ⊗ 𝟙 X₁) ≫ (α_ X₁ Y₁ X₁).hom ≫ (𝟙 X₁ ⊗ p₁.evaluation)) ⊗ 𝟙 Y₁) ≫
    (α_ X₁ (𝟙_ C) Y₁).hom ≫ (𝟙 X₁ ⊗ p₂.coevaluation ⊗ 𝟙 Y₁) ≫
      (𝟙 X₁ ⊗ (α_ X₂ Y₂ Y₁).hom) ≫ (α_ X₁ X₂ (Y₂ ⊗ Y₁)).inv

lemma tensor_coevaluation_eq (p₁ : exact_pairing X₁ Y₁) (p₂ : exact_pairing X₂ Y₂) :
  tensor_coevaluation p₁ p₂ =
    (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ p₁.coevaluation) ≫ (α_ (𝟙_ C) X₁ Y₁).inv ≫
      (((p₁.coevaluation ⊗ 𝟙 X₁) ≫ (α_ X₁ Y₁ X₁).hom ≫ (𝟙 X₁ ⊗ p₁.evaluation)) ⊗ 𝟙 Y₁) ≫
        (α_ X₁ (𝟙_ C) Y₁).hom ≫ (𝟙 X₁ ⊗ p₂.coevaluation ⊗ 𝟙 Y₁) ≫
          (𝟙 X₁ ⊗ (α_ X₂ Y₂ Y₁).hom) ≫ (α_ X₁ X₂ (Y₂ ⊗ Y₁)).inv :=
rfl

/-- Another expression for `tensor_coevaluation`. -/
lemma tensor_coevaluation_eq' (p₁ : exact_pairing X₁ Y₁) (p₂ : exact_pairing X₂ Y₂) :
  tensor_coevaluation p₁ p₂ = (ρ_ (𝟙_ C)).inv ≫
    (p₁.coevaluation ⊗ 𝟙 (𝟙_ C)) ≫ (α_ X₁ Y₁ (𝟙_ C)).hom ≫
      (𝟙 X₁ ⊗ ((𝟙 Y₁ ⊗ p₁.coevaluation) ≫ (α_ Y₁ X₁ Y₁).inv ≫ (p₁.evaluation ⊗ 𝟙 Y₁))) ≫
        (𝟙 X₁ ⊗ p₂.coevaluation ⊗ 𝟙 Y₁) ≫ (𝟙 X₁ ⊗ (α_ X₂ Y₂ Y₁).hom) ≫ (α_ X₁ X₂ (Y₂ ⊗ Y₁)).inv :=
begin
  rw [tensor_coevaluation_eq, ←left_unitor_inv_naturality_assoc, ←right_unitor_inv_naturality_assoc,
    coevaluation_evaluation, evaluation_coevaluation],
  congr' 1, simp_rw ←assoc, congr' 3,
  coherence
end

lemma tensor_coevaluation_evaluation_aux (p₁ : exact_pairing X₁ Y₁) (p₂ : exact_pairing X₂ Y₂) :
  (𝟙 (Y₂ ⊗ Y₁) ⊗ tensor_coevaluation p₁ p₂) ≫ (α_ (Y₂ ⊗ Y₁) (X₁ ⊗ X₂) (Y₂ ⊗ Y₁)).inv ≫
    (tensor_evaluation p₁ p₂ ⊗ 𝟙 (Y₂ ⊗ Y₁)) = (ρ_ (Y₂ ⊗ Y₁)).hom ≫ (λ_ (Y₂ ⊗ Y₁)).inv :=
begin
  calc _ =
  (𝟙 _ ⊗ (ρ_ _).inv) ≫ (𝟙 _ ⊗ p₁.coevaluation ⊗ 𝟙 _) ≫ (𝟙 _ ⊗ (α_ _ _ _).hom) ≫
    (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (α_ _ _ _).inv) ≫ (α_ _ _ _).inv ≫
      (𝟙 _ ⊗ ((ρ_ Y₁).hom ≫ (λ_ Y₁).inv ≫ (p₂.coevaluation ⊗ 𝟙 Y₁) ≫ (α_ _ _ _).hom)) ≫
        (((𝟙 Y₂ ⊗ p₁.evaluation) ≫ (ρ_ Y₂).hom ≫ (λ_ Y₂).inv) ⊗ 𝟙 _) ≫ (α_ _ _ _).inv ≫
          ((α_ _ _ _).hom ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ p₂.evaluation) ⊗ 𝟙 _) ≫ ((λ_ _).hom ⊗ 𝟙 _) : _
  ... = _ : _,
  { simp_rw [tensor_coevaluation_eq', tensor_evaluation_eq', coevaluation_evaluation,
      associator_inv_naturality_assoc, comp_tensor_id, id_tensor_comp, assoc,
      ←associator_conjugation_assoc _ (𝟙 X₂), pentagon_inv_hom_assoc,
      ←tensor_id Y₂, ←associator_conjugation_assoc (𝟙 Y₂), iso.inv_hom_id_assoc,
      ←id_tensor_comp_assoc Y₂, ←associator_inv_conjugation_assoc (𝟙 Y₁), iso.hom_inv_id_assoc,
      id_tensor_comp_assoc, ←associator_inv_conjugation_assoc (𝟙 Y₂), iso.hom_inv_id_assoc,
      tensor_id],
    congr' 15, simp_rw ←assoc, congr' 8, coherence },
  { simp_rw [tensor_exchange_assoc, comp_tensor_id, id_tensor_comp, assoc,
      ←tensor_id (𝟙_ C), ←associator_conjugation_assoc (𝟙 (𝟙_ C)), iso.inv_hom_id_assoc,
      pentagon_inv_inv_hom_inv_inv_assoc, iso.inv_hom_id_assoc,
      ←id_tensor_comp_assoc (𝟙_ C), ←tensor_id, ←associator_inv_conjugation p₂.evaluation,
      pentagon_hom_inv_inv_inv_inv_assoc, associator_inv_naturality_assoc _ p₂.coevaluation,
      ←comp_tensor_id_assoc _ _ Y₁, coevaluation_evaluation, ←associator_conjugation_assoc (𝟙 Y₂),
      iso.inv_hom_id_assoc, ←id_tensor_comp_assoc Y₂,
      ←associator_inv_conjugation p₁.evaluation, pentagon_hom_inv_inv_inv_inv_assoc,
      associator_inv_naturality_assoc, ←comp_tensor_id_assoc _ _ (𝟙_ C), coevaluation_evaluation],
    coherence }
end

lemma tensor_evaluation_coevaluation_aux (p₁ : exact_pairing X₁ Y₁) (p₂ : exact_pairing X₂ Y₂) :
  (tensor_coevaluation p₁ p₂ ⊗ 𝟙 (X₁ ⊗ X₂)) ≫ (α_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) (X₁ ⊗ X₂)).hom ≫
    (𝟙 (X₁ ⊗ X₂) ⊗ tensor_evaluation p₁ p₂) = (λ_ (X₁ ⊗ X₂)).hom ≫ (ρ_ (X₁ ⊗ X₂)).inv :=
begin
  calc _ =
  ((λ_ _).inv ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ p₁.coevaluation) ⊗ 𝟙 _) ≫ ((α_ _ _ _).inv ⊗ 𝟙 _) ≫
    (α_ _ _ _).hom ≫ (((λ_ X₁).hom ≫ (ρ_ X₁).inv ≫ (𝟙 X₁ ⊗ p₂.coevaluation)) ⊗ 𝟙 _) ≫
      (𝟙 _ ⊗ ((α_ _ _ _).inv ≫ (p₁.evaluation ⊗ 𝟙 X₂) ≫ (λ_ X₂).hom ≫ (ρ_ X₂).inv)) ≫
        (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv ≫ (𝟙 _ ⊗ (α_ _ _ _).inv) ≫
  (𝟙 _ ⊗ p₂.evaluation ⊗ 𝟙 _) ≫ (𝟙 _ ⊗ (ρ_ _).hom) : _
  ... = _ : _,
  { simp_rw [tensor_coevaluation_eq, tensor_evaluation_eq, evaluation_coevaluation,
      ←associator_naturality_assoc, comp_tensor_id, id_tensor_comp, assoc,
      ←associator_conjugation_assoc _ (𝟙 Y₁), pentagon_inv_hom_assoc,
      ←tensor_id X₁, ←associator_conjugation_assoc (𝟙 X₁), iso.inv_hom_id_assoc,
      ←id_tensor_comp_assoc X₁, ←associator_inv_conjugation_assoc (𝟙 X₂), iso.hom_inv_id_assoc,
      id_tensor_comp_assoc, ←associator_inv_conjugation_assoc (𝟙 X₁), iso.hom_inv_id_assoc,
      tensor_id],
    congr' 7, simp_rw ←assoc, congr' 9, simp_rw assoc, coherence },
  { simp_rw [←tensor_exchange_assoc, comp_tensor_id, id_tensor_comp, assoc,
      ←tensor_id (𝟙_ C), ←associator_conjugation_assoc (𝟙 (𝟙_ C)), iso.inv_hom_id_assoc,
      ←pentagon_comp_id_tensor_assoc, iso.inv_hom_id_assoc,
      ←id_tensor_comp_assoc (𝟙_ C), ←tensor_id, ←associator_inv_conjugation_assoc p₁.coevaluation,
      pentagon_hom_hom_inv_hom_hom_assoc, ←associator_naturality_assoc _ p₁.evaluation,
      ←comp_tensor_id_assoc _ _ X₂, evaluation_coevaluation, ←associator_conjugation_assoc (𝟙 X₁),
      iso.inv_hom_id_assoc, ←id_tensor_comp_assoc X₁,
      ←associator_inv_conjugation_assoc p₂.coevaluation, pentagon_hom_hom_inv_hom_hom_assoc,
      ←associator_naturality, ←comp_tensor_id_assoc _ _ (𝟙_ C), evaluation_coevaluation],
    coherence }
end

instance exact_pairing_tensor [p₁ : exact_pairing X₁ Y₁] [p₂ : exact_pairing X₂ Y₂] :
  exact_pairing (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) :=
{ coevaluation  := tensor_coevaluation p₁ p₂,
  evaluation    := tensor_evaluation p₁ p₂,
  coevaluation_evaluation' := by apply tensor_coevaluation_evaluation_aux,
  evaluation_coevaluation' := by apply tensor_evaluation_coevaluation_aux }

instance has_right_dual_tensor (X Y : C) [has_right_dual X] [has_right_dual Y] :
  has_right_dual (X ⊗ Y) := ⟨Yᘁ ⊗ Xᘁ⟩

instance has_left_dual_tensor (X Y : C) [has_left_dual X] [has_left_dual Y] :
  has_left_dual (X ⊗ Y) := ⟨ᘁY ⊗ ᘁX⟩

end tensor

end category_theory
