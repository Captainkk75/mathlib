/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.biproducts
import category_theory.preadditive
import category_theory.simple
import tactic.abel

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v u

namespace category_theory

variables {C : Type u} [category.{v} C]
variables [preadditive.{v} C] [has_binary_biproducts.{v} C]

/--
If
```
(f 0)
(0 g)
```
is invertible, then `f` is invertible.
-/
def is_iso_left_of_is_iso_biprod_map
  {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (biprod.map f g)] : is_iso f :=
begin
  fsplit,
  exact biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
  { dsimp,
    have := is_iso.hom_inv_id (biprod.map f g),
    have := congr_arg (λ p : W ⊞ X ⟶ W ⊞ X, biprod.inl ≫ p ≫ biprod.fst) this,
    simp only [category.id_comp, category.assoc] at this,
    simp only [biprod.inl_map_assoc] at this,
    rw this,
    simp, },
  { dsimp,
    have := is_iso.inv_hom_id (biprod.map f g),
    have := congr_arg (λ p : Y ⊞ Z ⟶ Y ⊞ Z, biprod.inl ≫ p ≫ biprod.fst) this,
    simp only [category.id_comp, category.assoc] at this,
    simp only [biprod.map_fst] at this,
    simp only [category.assoc],
    rw this,
    simp, },

end

def is_iso_right_of_is_iso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (biprod.map f g)] : is_iso g :=
sorry

section
variables {X₁ X₂ Y₁ Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)

def biprod.of_components : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ :=
biprod.fst ≫ f₁₁ ≫ biprod.inl +
biprod.fst ≫ f₁₂ ≫ biprod.inr +
biprod.snd ≫ f₂₁ ≫ biprod.inl +
biprod.snd ≫ f₂₂ ≫ biprod.inr

@[simp]
lemma biprod.inl_of_components_fst :
  biprod.inl ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.fst = f₁₁ :=
by simp [biprod.of_components]

@[simp]
lemma biprod.inl_of_components_snd :
  biprod.inl ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.snd = f₁₂ :=
by simp [biprod.of_components]

@[simp]
lemma biprod.inr_of_components_fst :
  biprod.inr ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.fst = f₂₁ :=
by simp [biprod.of_components]

@[simp]
lemma biprod.inr_of_components_snd :
  biprod.inr ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.snd = f₂₂ :=
by simp [biprod.of_components]

@[simp]
lemma biprod.of_components_comp {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
  (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)
  (g₁₁ : Y₁ ⟶ Z₁) (g₁₂ : Y₁ ⟶ Z₂) (g₂₁ : Y₂ ⟶ Z₁) (g₂₂ : Y₂ ⟶ Z₂) :
  biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.of_components g₁₁ g₁₂ g₂₁ g₂₂ =
    biprod.of_components (f₁₁ ≫ g₁₁ + f₁₂ ≫ g₂₁) (f₁₁ ≫ g₁₂ + f₁₂ ≫ g₂₂) (f₂₁ ≫ g₁₁ + f₂₂ ≫ g₂₁) (f₂₁ ≫ g₁₂ + f₂₂ ≫ g₂₂) :=
begin
  dsimp [biprod.of_components],
  apply biprod.hom_ext; apply biprod.hom_ext'; simp,
end

/--
The unipotent upper triangular matrix
```
(1 r)
(0 1)
```
as an isomorphism.
-/
@[simps]
def biprod.unipotent_upper {X₁ X₂ : C} (r : X₁ ⟶ X₂) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ :=
{ hom := biprod.of_components (𝟙 _) r 0 (𝟙 _),
  inv := biprod.of_components (𝟙 _) (-r) 0 (𝟙 _), }

/--
The unipotent lower triangular matrix
```
(1 0)
(r 1)
```
as an isomorphism.
-/
@[simps]
def biprod.unipotent_lower {X₁ X₂ : C} (r : X₂ ⟶ X₁) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ :=
{ hom := biprod.of_components (𝟙 _) 0 r (𝟙 _),
  inv := biprod.of_components (𝟙 _) 0 (-r) (𝟙 _), }


/--
If `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` via a two-by-two matrix whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def biprod.iso_elim [is_iso f₁₁] [is_iso (biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂)] : X₂ ≅ Y₂ :=
begin
  -- We use Gaussian elimination to show that the matrix `f` is equivalent to a diagonal matrix,
  -- which then must be an isomorphism.
  set f := biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂,
  set a : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ := biprod.unipotent_lower (-(f₂₁ ≫ inv f₁₁)),
  set b : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂ := biprod.unipotent_upper (-(inv f₁₁ ≫ f₁₂)),
  set r : X₂ ⟶ Y₂ := f₂₂ - f₂₁ ≫ (inv f₁₁) ≫ f₁₂,
  set d : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ := biprod.map f₁₁ r,
  have w : a.hom ≫ f ≫ b.hom = d := by { ext; simp [f, a, b, d, r]; abel, },
  haveI : is_iso d := by { rw ←w, apply_instance, },
  haveI : is_iso r := (is_iso_right_of_is_iso_biprod_map f₁₁ r),
  exact as_iso r
end

end

end category_theory
