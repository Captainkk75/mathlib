/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.path_category
import category_theory.fully_faithful
import category_theory.bicategory.free
import category_theory.bicategory.locally_discrete
/-!
# The coherence theorem for bicategories

In this file, we prove the coherence theorem for bicategories, stated in the following form: the
free bicategory over any quiver is locally thin.

The proof is almost the same as the proof of the coherence theorem for monoidal categories that
has been previously formalized in mathlib, which is based on the proof described by Ilya Beylin
and Peter Dybjer. The idea is to view a path on a quiver as a normal form of a 1-morphism in the
free bicategory on the same quiver. A normalization procedure is then described by
`full_normalize : pseudofunctor (free_bicategory B) (locally_discrete (paths B))`, which is a
pseudofunctor from the free bicategory to the locally discrete bicategory on the path category.
It turns out that this pseudofunctor is locally an equivalence of categories, and the coherence
theorem follows immediately from this fact.

## Main statements

* `locally_thin` : the free bicategory is locally thin, that is, there is at most one
  2-morphism between two fixed 1-morphisms.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
   proof of normalization for monoids][beylin1996]
-/

open quiver (path) quiver.path

namespace category_theory

open bicategory category
open_locale bicategory

universes v u

namespace free_bicategory

variables {B : Type u} [quiver.{v+1} B]

/-- Auxiliary definition for `inclusion_path`. -/
@[simp]
def inclusion_path_aux {a : B} : ∀ {b : B}, path a b → hom a b
| _ nil := hom.id a
| _ (cons p f) := (inclusion_path_aux p).comp (hom.of f)

/--
The discrete category on the paths includes into the category of 1-morphisms in the free
bicategory.
-/
@[simps]
def inclusion_path (a b : B) : discrete (path.{v+1} a b) ⥤ hom a b :=
{ obj := inclusion_path_aux,
  map := λ f g η, eq_to_hom (congr_arg inclusion_path_aux (discrete.eq_of_hom η)) }

variables (B)

/--
The inclusion from the locally discrete bicategory on the path category into the free bicategory
as a prelax functor. This will be promoted to a pseudofunctor after proving the coherence theorem.
See `inclusion`.
-/
@[simps]
def preinclusion : prelax_functor (locally_discrete (paths B)) (free_bicategory B) :=
{ obj := id,
  map := λ a b, (inclusion_path a b).obj,
  map₂ := λ a b, (inclusion_path a b).map }

variables {B}

/--
The normalization of the composition of `p : path a b` and `f : hom b c`. Defining this function
is easier than defining the normalization of `f : hom a b` alone, which will defined as the
normalization of the composition of `path.nil : path a a` and `f : hom a b`.
-/
@[simp]
def normalize_hom {a : B} : ∀ {b c : B}, path a b → hom b c → path a c
| _ _ p (hom.of f) := p.cons f
| _ _ p (hom.id b) := p
| _ _ p (hom.comp f g) := normalize_hom (normalize_hom p f) g

@[simp]
def normalize_iso {a : B} : ∀ {b c : B} (p : path a b) (f : hom b c),
  (preinclusion B).map p ≫ f ≅ (preinclusion B).map (normalize_hom p f)
| b c p (hom.of f) := iso.refl _
| _ _ p (hom.id b) := ρ_ _
| b d p (hom.comp f g) := (α_ _ _ _).symm ≪≫
    whisker_right_iso (normalize_iso p f) g ≪≫ normalize_iso _ g

/--
Given a 2-morphism between `f` and `g` in the free bicategory, we have the equality
`normalize_hom f p = normalize_hom g p`.
-/
lemma normalize_hom_congr {a b c : B} (p : path a b) {f g : hom b c} (η : hom₂ f g) :
  normalize_hom p f = normalize_hom p g :=
begin
  apply @congr_fun _ _ (λ p, normalize_hom p f),
  clear p,
  induction η,
  case vcomp { apply eq.trans; assumption },
  case whisker_left  : _ _ _ _ _ _ _ ih { funext, apply congr_fun ih },
  case whisker_right : _ _ _ _ _ _ _ ih { funext, apply congr_arg2 _ (congr_fun ih p) rfl },
  all_goals { funext, refl }
end

/- should be moved to eq_to_hom -/
lemma family_congr {ι C : Type*} [category C] {o₁ o₂ : ι → C} (m : ∀ i, o₁ i ⟶ o₂ i)
  {i j : ι} (h : i = j) : m i = eq_to_hom (by rw h) ≫ m j ≫ eq_to_hom (by rw h) :=
by { subst h, apply eq_conj_eq_to_hom }

lemma normalize_naturality {a b c : B} (p : path a b) {f g : hom b c} (η : f ⟶ g) :
  ((preinclusion B).map p ◁ η) ≫ (normalize_iso p g).hom =
  (normalize_iso p f).hom ≫ eq_to_hom (by {rcases η, rw normalize_hom_congr p η}) :=
begin
  rcases η, induction η,
  case id : { simp },
  case vcomp : _ _ _ _ _ _ _ ihf ihg
  { rw [mk_vcomp, bicategory.whisker_left_comp],
    slice_lhs 2 3 { rw ihg }, slice_lhs 1 2 { rw ihf }, simp },
  case whisker_left : _ _ _ _ _ _ _ ih
  { dsimp, slice_lhs 1 2 { rw associator_inv_naturality_right },
    slice_lhs 2 3 { rw whisker_exchange },
    slice_lhs 3 4 { erw ih }, /- p ≠ nil required! -/ simpa only [assoc] },
  case whisker_right : _ _ _ _ _ h η ih
  { dsimp, slice_lhs 1 2 { rw associator_inv_naturality_middle },
    slice_lhs 2 3 { erw [←bicategory.whisker_right_comp, ih, bicategory.whisker_right_comp] },
    have := family_congr (λ x, (normalize_iso x h).hom) (normalize_hom_congr p η),
    dsimp at this, simpa [this] },
  case associator
  { erw comp_id, dsimp,
    slice_lhs 3 4 { erw associator_inv_naturality_left },
    slice_lhs 1 3 { erw pentagon_hom_inv_inv_inv_inv },
    simpa only [assoc, bicategory.whisker_right_comp] },
  case associator_inv
  { erw comp_id, dsimp,
    slice_rhs 2 3 { erw associator_inv_naturality_left },
    slice_rhs 1 2 { erw ←pentagon_inv },
    simpa only [assoc, bicategory.whisker_right_comp] },
  case left_unitor { erw comp_id, symmetry, apply triangle_assoc_comp_right_assoc },
  case left_unitor_inv
  { dsimp, slice_lhs 1 2 { erw triangle_assoc_comp_left_inv },
    rw [inv_hom_whisker_right, id_comp, comp_id] },
  case right_unitor
  { erw [comp_id, whisker_left_right_unitor, assoc, ←right_unitor_naturality], refl },
  case right_unitor_inv
  { erw [comp_id, whisker_left_right_unitor_inv, assoc, iso.hom_inv_id_assoc,
      right_unitor_conjugation] },
end

variable (B)

/-- The normalization pseudofunctor for the free bicategory on a quiver `B`. -/
def full_normalize : oplax_functor (free_bicategory B) (locally_discrete (paths B)) :=
{ obj := id,
  map := λ a b f, normalize_hom nil f, --((normalize a a b).obj f).obj nil,
  map₂ := λ a b f g η, ⟨⟨quot.ind (normalize_hom_congr nil) η⟩⟩, --((normalize a a b).map η).app nil,
  map_id := λ a, 𝟙 (𝟙 a),
  map_comp := λ a b c f g,
  ⟨⟨begin
    induction g generalizing a,
    case id { refl },
    case of { refl },
    case comp : _ _ _ g _ ihf ihg { erw [ihg _ (f.comp g), ihf _ f, ihg _ g, assoc] }
  end⟩⟩ }

variable {B}

def normalize_unit_iso (a b : free_bicategory B) :
  𝟭 (a ⟶ b) ≅ (full_normalize B).map_functor a b ⋙ inclusion_path a b :=
nat_iso.of_components (λ f, (λ_ _).symm ≪≫ normalize_iso nil f)
begin
  rintros f g η, erw left_unitor_inv_naturality_assoc,
  simp only [iso.trans_hom, assoc], congr' 1, apply normalize_naturality nil,
end

/-- The normalization as an equivalence of categories. -/
def normalize_equiv (a b : B) : hom a b ≌ discrete (path.{v+1} a b) :=
equivalence.mk ((full_normalize _).map_functor a b) (inclusion_path a b)
  (normalize_unit_iso a b)
  (nat_iso.of_components (λ f, eq_to_iso (by { induction f, tidy })) (by tidy))

/-- The coherence theorem for bicategories. -/
instance locally_thin {a b : free_bicategory B} (f g : a ⟶ b) : subsingleton (f ⟶ g) :=
⟨λ η θ, (normalize_equiv a b).functor.map_injective (subsingleton.elim _ _)⟩

/-- Auxiliary definition for `inclusion`. -/
def inclusion_map_comp_aux {a b : B} : ∀ {c : B} (f : path a b) (g : path b c),
  (preinclusion _).map (f ≫ g) ≅ (preinclusion _).map f ≫ (preinclusion _).map g
| _ f nil := (ρ_ ((preinclusion _).map f)).symm
| _ f (cons g₁ g₂) := whisker_right_iso (inclusion_map_comp_aux f g₁) (hom.of g₂) ≪≫ α_ _ _ _

variables (B)

/--
The inclusion pseudofunctor from the locally discrete bicategory on the path category into the
free bicategory.
-/
@[simps]
def inclusion : pseudofunctor (locally_discrete (paths B)) (free_bicategory B) :=
{ map_id := λ a, iso.refl (𝟙 a),
  map_comp := λ a b c f g, inclusion_map_comp_aux f g,
  -- All the conditions for 2-morphisms are trivial thanks to the coherence theorem!
  .. preinclusion B }

end free_bicategory

end category_theory
