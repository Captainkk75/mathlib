import category_theory.monoidal.CommMon_
import algebra.homology.single
import category_theory.limits.shapes.biproducts
import data.finset.nat_antidiagonal
import category_theory.monoidal.functorial
import algebra.category.Module.monoidal
import algebra.category.Module.abelian

open category_theory
open category_theory.limits

universes v u

noncomputable theory

variables {C : Type u} [category.{0} C] [has_zero_object C] [preadditive C] [has_finite_biproducts C] [monoidal_category C]

open_locale big_operators

def left_distributor {J : Type} [decidable_eq J] [fintype J] (X : C) (f : J → C) :
  X ⊗ (⨁ f) ≅ ⨁ (λ j, X ⊗ f j) :=
{ hom := ∑ j : J, (𝟙 X ⊗ biproduct.π f j) ≫ biproduct.ι _ j,
  inv := ∑ j : J, biproduct.π _ j ≫ (𝟙 X ⊗ biproduct.ι f j),
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

def right_distributor {J : Type} [decidable_eq J] [fintype J] (X : C) (f : J → C) :
  (⨁ f) ⊗ X ≅ ⨁ (λ j, f j ⊗ X) :=
{ hom := ∑ j : J, (biproduct.π f j ⊗ 𝟙 X) ≫ biproduct.ι _ j,
  inv := ∑ j : J, biproduct.π _ j ≫ (biproduct.ι f j ⊗ 𝟙 X),
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

namespace cochain_complex

def antidiagonal (i : ℕ) := { p : ℕ × ℕ // p.1 + p.2 = i }
instance (i : ℕ) : fintype (antidiagonal i) := sorry

def tensor_d (X Y : cochain_complex C ℕ) (i j : ℕ) (p : antidiagonal i) (q : antidiagonal j) :
  X.X p.1.1 ⊗ Y.X p.1.2 ⟶ X.X q.1.1 ⊗ Y.X q.1.2 :=
if h : p.1.1 = q.1.1 then
  (-1 : ℤ)^p.1.1 • eq_to_hom (congr_arg X.X h) ⊗ Y.d p.1.2 q.1.2
else if h : p.1.2 = q.1.2 then
  X.d p.1.1 q.1.1 ⊗ eq_to_hom (congr_arg Y.X h)
else
  0

def tensor_obj (X Y : cochain_complex C ℕ) : cochain_complex C ℕ :=
{ X := λ i, ⨁ (λ p : antidiagonal i, X.X p.1.1 ⊗ Y.X p.1.2),
  d := λ i j, biproduct.matrix (tensor_d X Y i j),
  shape' := sorry,
  d_comp_d' := sorry, }

def tensor_hom {X₁ X₂ Y₁ Y₂ : cochain_complex C ℕ} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
  tensor_obj X₁ Y₁ ⟶ tensor_obj X₂ Y₂ :=
{ f := λ i, biproduct.map (λ p, f.f p.1.1 ⊗ g.f p.1.2),
  comm' := sorry, }

def tensor_unit : cochain_complex C ℕ := (cochain_complex.single₀ C).obj (𝟙_ C)

def associator_hom_aux (X Y Z : cochain_complex C ℕ) (i : ℕ)
  (p q : antidiagonal i) (j : antidiagonal p.1.1) (k : antidiagonal q.1.2) :
    (X.X j.1.1 ⊗ Y.X j.1.2) ⊗ Z.X p.1.2 ⟶ X.X q.1.1 ⊗ (Y.X k.1.1 ⊗ Z.X k.1.2) :=
if h : j.1.1 = q.1.1 ∧ j.1.2 = k.1.1 ∧ p.1.2 = k.1.2 then
  (α_ _ _ _).hom ≫
    (eq_to_hom (congr_arg X.X h.1) ⊗ eq_to_hom (congr_arg Y.X h.2.1) ⊗
      eq_to_hom (congr_arg Z.X h.2.2))
else
  0

def associator_hom (X Y Z : cochain_complex C ℕ) :
  tensor_obj (tensor_obj X Y) Z ⟶ tensor_obj X (tensor_obj Y Z) :=
{ f := λ i, biproduct.matrix (λ p q,
  (right_distributor _ _).hom ≫ biproduct.matrix (associator_hom_aux X Y Z i p q) ≫
    (left_distributor _ _).inv),
  comm' := sorry }

def associator_inv_aux (X Y Z : cochain_complex C ℕ) (i : ℕ)
  (p q : antidiagonal i) (j : antidiagonal p.1.2) (k : antidiagonal q.1.1) :
    X.X p.1.1 ⊗ (Y.X j.1.1 ⊗ Z.X j.1.2) ⟶ (X.X k.1.1 ⊗ Y.X k.1.2) ⊗ Z.X q.1.2 :=
if h : p.1.1 = k.1.1 ∧ j.1.1 = k.1.2 ∧ j.1.2 = q.1.2 then
  (eq_to_hom (congr_arg X.X h.1) ⊗ eq_to_hom (congr_arg Y.X h.2.1) ⊗
      eq_to_hom (congr_arg Z.X h.2.2)) ≫ (α_ _ _ _).inv
else
  0

def associator_inv (X Y Z : cochain_complex C ℕ) :
  tensor_obj X (tensor_obj Y Z) ⟶ tensor_obj (tensor_obj X Y) Z :=
{ f := λ i, biproduct.matrix (λ p q,
  (left_distributor _ _).hom ≫ biproduct.matrix (associator_inv_aux X Y Z i p q) ≫
    (right_distributor _ _).inv),
  comm' := sorry }

def associator (X Y Z : cochain_complex C ℕ) :
  tensor_obj (tensor_obj X Y) Z ≅ tensor_obj X (tensor_obj Y Z) :=
{ hom := associator_hom X Y Z,
  inv := associator_inv X Y Z,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

-- TODO there is still data to construct here
def left_unitor (X : cochain_complex C ℕ) :
  tensor_obj tensor_unit X ≅ X := sorry

-- TODO there is still data to construct here
def right_unitor (X : cochain_complex C ℕ) :
  tensor_obj X tensor_unit ≅ X := sorry

end cochain_complex

instance : monoidal_category (cochain_complex C ℕ) :=
{ tensor_obj := λ X Y, cochain_complex.tensor_obj X Y,
  tensor_hom := λ X₁ X₂ Y₁ Y₂ f g, cochain_complex.tensor_hom f g,
  tensor_unit := cochain_complex.tensor_unit,
  associator := cochain_complex.associator,
  left_unitor := cochain_complex.left_unitor,
  right_unitor := cochain_complex.right_unitor,
  tensor_id' := sorry,
  tensor_comp' := sorry,
  associator_naturality' := sorry,
  left_unitor_naturality' := sorry,
  right_unitor_naturality' := sorry,
  pentagon' := sorry,
  triangle' := sorry, }

variables [braided_category C]

instance : braided_category (cochain_complex C ℕ) :=
sorry

namespace graded_object

def tensor_obj (X Y : graded_object ℕ C) : graded_object ℕ C :=
sorry

def tensor_hom {X₁ X₂ Y₁ Y₂ : graded_object ℕ C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
  tensor_obj X₁ Y₁ ⟶ tensor_obj X₂ Y₂ :=
sorry

def tensor_unit : graded_object ℕ C := sorry

def associator_hom (X Y Z : graded_object ℕ C) :
  tensor_obj (tensor_obj X Y) Z ⟶ tensor_obj X (tensor_obj Y Z) :=
sorry

def associator_inv (X Y Z : graded_object ℕ C) :
  tensor_obj X (tensor_obj Y Z) ⟶ tensor_obj (tensor_obj X Y) Z :=
sorry

def associator (X Y Z : graded_object ℕ C) :
  tensor_obj (tensor_obj X Y) Z ≅ tensor_obj X (tensor_obj Y Z) :=
{ hom := associator_hom X Y Z,
  inv := associator_inv X Y Z,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

def left_unitor (X : graded_object ℕ C) :
  tensor_obj tensor_unit X ≅ X := sorry

def right_unitor (X : graded_object ℕ C) :
  tensor_obj X tensor_unit ≅ X := sorry

end graded_object

instance : monoidal_category (graded_object ℕ C) :=
{ tensor_obj := λ X Y, graded_object.tensor_obj X Y,
  tensor_hom := λ X₁ X₂ Y₁ Y₂ f g, graded_object.tensor_hom f g,
  tensor_unit := graded_object.tensor_unit,
  associator := graded_object.associator,
  left_unitor := graded_object.left_unitor,
  right_unitor := graded_object.right_unitor,
  tensor_id' := sorry,
  tensor_comp' := sorry,
  associator_naturality' := sorry,
  left_unitor_naturality' := sorry,
  right_unitor_naturality' := sorry,
  pentagon' := sorry,
  triangle' := sorry, }

instance : braided_category (graded_object ℕ C) :=
sorry

variables [has_equalizers C] [has_images C] [has_image_maps C] [has_cokernels C]

instance : lax_monoidal (graded_homology_functor C (complex_shape.up ℕ)).obj :=
sorry

variables (C)

def graded_homology_lax_monoidal_functor : lax_monoidal_functor (cochain_complex C ℕ) (graded_object ℕ C) :=
lax_monoidal_functor.of (graded_homology_functor C (complex_shape.up ℕ)).obj

def graded_homology_lax_braided_functor : lax_braided_functor (cochain_complex C ℕ) (graded_object ℕ C) :=
sorry

def CDGA_challenge : CommMon_ (cochain_complex C ℕ) ⥤ CommMon_ (graded_object ℕ C) :=
(graded_homology_lax_braided_functor C).map_CommMon

variables (R : Type) [comm_ring R]

def CDGA_challenge' : CommMon_ (cochain_complex (Module.{0} R) ℕ) ⥤ CommMon_ (graded_object ℕ (Module.{0} R)) :=
CDGA_challenge _
