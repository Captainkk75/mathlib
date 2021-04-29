/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import algebra.homology.exact
import algebra.homology.single
import algebra.homology.quasi_iso
import algebra.homology.homotopy
import algebra.homology.augment
import category_theory.types

/-!
# Projective objects and categories with enough projectives

An object `P` is called projective if every morphism out of `P` factors through every epimorphism.

A category `C` has enough projectives if every object admits an epimorphism from some
projective object.

`projective.over X` picks an arbitrary such projective object,
and `projective.π X : projective.over X ⟶ X` is the corresponding epimorphism.

Given a morphism `f : X ⟶ Y`, `projective.left f` is a projective object over `kernel f`,
and `projective.d f : projective.left f ⟶ X` is the morphism `π (kernel f) ≫ kernel.ι f`.
-/

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

/--
An object `P` is called projective if every morphism out of `P` factors through every epimorphism.
-/
class projective (P : C) : Prop :=
(factors : ∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X) [epi e], ∃ f', f' ≫ e = f)

section

/--
A projective presentation of an object `X` consists of an epimorphism `f : P ⟶ X`
from some projective object `P`.
-/
@[nolint has_inhabited_instance]
structure projective_presentation (X : C) :=
(P : C)
(projective : projective P . tactic.apply_instance)
(f : P ⟶ X)
(epi : epi f . tactic.apply_instance)

variables (C)

/-- A category "has enough projectives" if for every object `X` there is a projective object `P` and
    an epimorphism `P ↠ X`. -/
class enough_projectives : Prop :=
(presentation : ∀ (X : C), nonempty (projective_presentation X))

end

namespace projective

/--
An arbitrarily chosen factorisation of a morphism out of a projective object through an epimorphism.
-/
def factor_thru {P X E : C} [projective P] (f : P ⟶ X) (e : E ⟶ X) [epi e] : P ⟶ E :=
(projective.factors f e).some

@[simp] lemma factor_thru_comp {P X E : C} [projective P] (f : P ⟶ X) (e : E ⟶ X) [epi e] :
  factor_thru f e ≫ e = f :=
(projective.factors f e).some_spec

lemma of_iso {P Q : C} (i : P ≅ Q) (hP : projective P) : projective Q :=
begin
  fsplit,
  introsI E X f e e_epi,
  obtain ⟨f', hf'⟩ := projective.factors (i.hom ≫ f) e,
  exact ⟨i.inv ≫ f', by simp [hf']⟩
end

lemma iso_iff {P Q : C} (i : P ≅ Q) : projective P ↔ projective Q :=
⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every type is a projective object in `Type`. -/
instance (X : Type u) : projective X :=
{ factors := λ E X' f e epi,
  ⟨λ x, ((epi_iff_surjective _).mp epi (f x)).some,
  by { ext x, exact ((epi_iff_surjective _).mp epi (f x)).some_spec, }⟩ }

instance Type_enough_projectives : enough_projectives (Type u) :=
{ presentation := λ X, ⟨{ P := X, f := 𝟙 X, }⟩, }

instance {P Q : C} [has_binary_coproduct P Q] [projective P] [projective Q] :
  projective (P ⨿ Q) :=
{ factors := λ E X' f e epi, by exactI
  ⟨coprod.desc (factor_thru (coprod.inl ≫ f) e) (factor_thru (coprod.inr ≫ f) e), by tidy⟩, }

instance {β : Type v} (g : β → C) [has_coproduct g] [∀ b, projective (g b)] :
  projective (∐ g) :=
{ factors := λ E X' f e epi, by exactI
  ⟨sigma.desc (λ b, factor_thru (sigma.ι g b ≫ f) e), by tidy⟩, }

instance {P Q : C} [has_zero_morphisms C] [has_binary_biproduct P Q]
  [projective P] [projective Q] :
  projective (P ⊞ Q) :=
{ factors := λ E X' f e epi, by exactI
  ⟨biprod.desc (factor_thru (biprod.inl ≫ f) e) (factor_thru (biprod.inr ≫ f) e), by tidy⟩, }

instance {β : Type v} [decidable_eq β] (g : β → C) [has_zero_morphisms C] [has_biproduct g]
  [∀ b, projective (g b)] : projective (⨁ g) :=
{ factors := λ E X' f e epi, by exactI
  ⟨biproduct.desc (λ b, factor_thru (biproduct.ι g b ≫ f) e), by tidy⟩, }

section enough_projectives
variables [enough_projectives C]

/--
`projective.over X` provides an arbitrarily chosen projective object equipped with
an epimorphism `projective.π : projective.over X ⟶ X`.
-/
def over (X : C) : C :=
(enough_projectives.presentation X).some.P

instance projective_over (X : C) : projective (over X) :=
(enough_projectives.presentation X).some.projective

/--
The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
def π (X : C) : over X ⟶ X :=
(enough_projectives.presentation X).some.f

instance π_epi (X : C) : epi (π X) :=
(enough_projectives.presentation X).some.epi

section
variables [has_zero_morphisms C] {X Y : C} (f : X ⟶ Y) [has_kernel f]

/-- When `C` has enough projectives, the object `projective.left f` is
the arbitrarily chosen projective object over `kernel f`. -/
@[derive projective]
def left : C := over (kernel f)

/-- When `C` has enough projectives,
`projective.d f : projective.left f ⟶ X` is the composition
`π (kernel f) ≫ kernel.ι f`.
-/
abbreviation d : left f ⟶ X :=
π (kernel f) ≫ kernel.ι f

end

section
variables [has_zero_morphisms C] [has_equalizers C] [has_images C]

/--
A `projective.resolution Z` consists of a `ℕ`-indexed chain complex of projective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.
-/
-- We implement this more concretely, however, in terms of an exact sequence,
-- not even mentioning chain complexes or quasi-isomorphisms.
@[nolint has_inhabited_instance]
structure resolution (Z : C) :=
(X : ℕ → C)
(d : Π n, X (n+1) ⟶ X n)
(zero : X 0 ≅ Z)
(projective : ∀ n, projective (X (n+1)))
(epi : epi (d 0))
(exact : ∀ n, exact (d (n+1)) (d n))

variables [has_zero_object C] [has_image_maps C] [has_cokernels C]

-- TODO generalize to `chain_complex.mk`?
def resolution.exact_sequence {Z : C} (P : resolution Z) : chain_complex C ℕ :=
{ X := P.X,
  d := λ i j, if h : i = j + 1 then eq_to_hom (congr_arg P.X h) ≫ P.d j else 0,
  shape' := λ i j w, by rw dif_neg (ne.symm w),
  d_comp_d' := λ i j k,
  begin
    split_ifs with h h' h',
    { substs h h', simp [(P.exact k).w], },
    all_goals { simp },
  end }

def resolution.complex {Z : C} (P : resolution Z) : chain_complex C ℕ :=
chain_complex.truncate.obj P.exact_sequence

instance resolution.exact' {Z : C} (P : resolution Z) (n : ℕ) :
  exact (P.complex.d (n+2) (n+1)) (P.complex.d (n+1) n) :=
begin
  dsimp [resolution.complex, resolution.exact_sequence],
  rw [if_pos rfl, if_pos rfl],
  rw [category.id_comp, category.id_comp],
  exact P.exact (n+1),
end

instance resolution.projective' {Z : C} (P : resolution Z) (n : ℕ) :
  projective (P.complex.X n) :=
P.projective n

def resolution.map {Z : C} (P : resolution Z) :
  P.complex ⟶ (homological_complex.single C _ 0).obj Z :=
chain_complex.truncate_to_single P.exact_sequence ≫ (homological_complex.single C _ 0).map P.zero.hom

instance {Z : C} (P : resolution Z) : exact (P.complex.d 1 0) (P.map.f 0) :=
begin
  -- TODO: yuck:
  dsimp [resolution.map, resolution.complex, resolution.exact_sequence, chain_complex.truncate_to_single, chain_complex.truncate, chain_complex.to_single_equiv],
  split_ifs,
  { rw [category.comp_id, category.id_comp, category.id_comp, category.id_comp, exact_comp_iso],
    exact P.exact 0, },
  { simpa using h, },
end

@[simp] lemma resolution.map_f_succ {Z : C} (P : resolution Z) (n : ℕ) :
  P.map.f (n+1) = 0 :=
begin
  -- TODO: yuck
  dsimp [resolution.map, resolution.exact_sequence, chain_complex.truncate_to_single, chain_complex.truncate,
    chain_complex.to_single_equiv],
  rw [dif_neg, zero_comp],
  simp,
end

def resolution.quasi_iso {Z : C} (P : resolution Z) : quasi_iso P.map :=
sorry

attribute [instance] resolution.projective

instance {Z : C} (P : resolution Z) (n : ℕ) : epi (P.map.f n) := sorry

namespace resolution

def chain_map.mk_inductive_aux (P Q : chain_complex C ℕ)
  (zero : P.X 0 ⟶ Q.X 0)
  (one : P.X 1 ⟶ Q.X 1)
  (zero_one_comm : P.d 1 0 ≫ zero = one ≫ Q.d 1 0)
  (succ : ∀ (n : ℕ)
    (p : Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n+1) ⟶ Q.X (n+1)), P.d (n+1) n ≫ f = f' ≫ Q.d (n+1) n),
    Σ' f'' : P.X (n+2) ⟶ Q.X (n+2), P.d (n+2) (n+1) ≫ p.2.1 = f'' ≫ Q.d (n+2) (n+1)) :
  Π n, Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n+1) ⟶ Q.X (n+1)), P.d (n+1) n ≫ f = f' ≫ Q.d (n+1) n
| 0 := ⟨zero, one, zero_one_comm⟩
| (n+1) := ⟨(chain_map.mk_inductive_aux n).2.1,
    (succ n (chain_map.mk_inductive_aux n)).1, (succ n (chain_map.mk_inductive_aux n)).2⟩

-- TODO move, rename
def chain_map.mk_inductive (P Q : chain_complex C ℕ)
  (zero : P.X 0 ⟶ Q.X 0)
  (one : P.X 1 ⟶ Q.X 1)
  (zero_one_comm : P.d 1 0 ≫ zero = one ≫ Q.d 1 0)
  (succ : ∀ (n : ℕ)
    (p : Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n+1) ⟶ Q.X (n+1)), P.d (n+1) n ≫ f = f' ≫ Q.d (n+1) n),
    Σ' f'' : P.X (n+2) ⟶ Q.X (n+2), P.d (n+2) (n+1) ≫ p.2.1 = f'' ≫ Q.d (n+2) (n+1)) : P ⟶ Q :=
{ f := λ n, (chain_map.mk_inductive_aux P Q zero one zero_one_comm succ n).1,
  comm' := λ n m,
  begin
    by_cases h : m + 1 = n,
    { subst h,
      exact (chain_map.mk_inductive_aux P Q zero one zero_one_comm succ m).2.2.symm, },
    { rw [P.shape n m h, Q.shape n m h], simp, }
  end }

/- Auxiliary construction for `lift`. -/
def lift_f_zero {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) :
  P.complex.X 0 ⟶ Q.complex.X 0 :=
factor_thru (P.map.f 0 ≫ f) (Q.map.f 0)

local attribute [instance] epi_comp

/- Auxiliary construction for `lift`. -/
def lift_f_one {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) :
  P.complex.X 1 ⟶ Q.complex.X 1 :=
begin
  have z : (P.complex.d 1 0 ≫ lift_f_zero f P Q) ≫ Q.map.f 0 = 0,
  { dsimp [lift_f_zero], simp, },
  let g := factor_thru_kernel_subobject (Q.map.f 0) _ z,
  -- It is tempting, but incorrect, to factor `g` through the composition in one step here!
  exact factor_thru (factor_thru g
    (image_to_kernel (Q.complex.d 1 0) (Q.map.f 0) (by simp)))
      (factor_thru_image_subobject (Q.complex.d 1 0))
end

/- Auxiliary lemma for `lift`. -/
@[simp] lemma lift_f_zero_one_comm
  {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) :
  P.complex.d 1 0 ≫ lift_f_zero f P Q = lift_f_one f P Q ≫ Q.complex.d 1 0 :=
begin
  dsimp [lift_f_zero, lift_f_one],
  conv_rhs { congr, skip, rw ← image_subobject_arrow_comp (Q.complex.d 1 0), },
  rw [←category.assoc, category_theory.projective.factor_thru_comp, ←image_to_kernel_arrow,
    ←category.assoc, category_theory.projective.factor_thru_comp,
    factor_thru_kernel_subobject_comp_arrow],
end

/- Auxiliary construction for `lift`. -/
def lift_f_succ {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) (n : ℕ)
  (p : Σ' (f : P.complex.X n ⟶ Q.complex.X n) (f' : P.complex.X (n+1) ⟶ Q.complex.X (n+1)), P.complex.d (n+1) n ≫ f = f' ≫ Q.complex.d (n+1) n) :
    Σ' f'' : P.complex.X (n+2) ⟶ Q.complex.X (n+2), P.complex.d (n+2) (n+1) ≫ p.2.1 = f'' ≫ Q.complex.d (n+2) (n+1) :=
begin
  rcases p with ⟨f, f', w⟩,
  have z : (P.complex.d (n+2) (n+1) ≫ f') ≫ Q.complex.d (n+1) n = 0,
  { rw [category.assoc, ←w, ←category.assoc, P.complex.d_comp_d, zero_comp], },
  let g := factor_thru_kernel_subobject (Q.complex.d (n+1) n) _ z,
  fsplit,
  -- It is tempting, but incorrect, to factor `g` through the composition in one step here!
  exact factor_thru (factor_thru g
    (image_to_kernel (Q.complex.d (n+2) (n+1)) (Q.complex.d (n+1) n) (Q.complex.d_comp_d _ _ _)))
      (factor_thru_image_subobject (Q.complex.d (n+2) (n+1))),
  dsimp [g],
  conv_rhs { congr, skip, rw ← image_subobject_arrow_comp (Q.complex.d (n+2) (n+1)), },
  rw [←category.assoc, category_theory.projective.factor_thru_comp, ←image_to_kernel_arrow,
    ←category.assoc, category_theory.projective.factor_thru_comp,
    factor_thru_kernel_subobject_comp_arrow],
end

/-- A morphism in `C` lifts to a chain map between projective resolutions. -/
def lift {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) :
  P.complex ⟶ Q.complex :=
begin
  fapply chain_map.mk_inductive,
  apply lift_f_zero f,
  apply lift_f_one f,
  apply lift_f_zero_one_comm f,
  apply lift_f_succ f,
end

/-- The resolution maps interwine the lift of a morphism and that morphism. -/
@[simp, reassoc]
lemma lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) :
  lift f P Q ≫ Q.map = P.map ≫ (homological_complex.single C _ 0).map f :=
begin
  ext n,
  rcases n with (_|_|n),
  { dsimp [lift, chain_map.mk_inductive, chain_map.mk_inductive_aux, lift_f_zero], simp, },
  { dsimp [lift, chain_map.mk_inductive, chain_map.mk_inductive_aux, lift_f_one], simp, },
  { dsimp, simp, },
end

-- Now that we've checked this property of the lift,
-- we can seal away the actual definition.
attribute [irreducible] lift

end resolution

end

namespace resolution

variables [preadditive C] [has_equalizers C] [has_images C] [has_image_maps C]
  [has_zero_object C] [has_cokernels C]

def lift_homotopy {Y Z : C} (f : Y ⟶ Z) {P : resolution Y} {Q : resolution Z}
  (g h : P.complex ⟶ Q.complex)
  (g_comm : g ≫ Q.map = P.map ≫ (homological_complex.single C _ 0).map f)
  (h_comm : h ≫ Q.map = P.map ≫ (homological_complex.single C _ 0).map f) :
  homotopy g h :=
sorry

def lift_comp_homotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : resolution X) (Q : resolution Y) (R : resolution Z) :
  homotopy (lift (f ≫ g) P R) (lift f P Q ≫ lift g Q R) :=
by { apply lift_homotopy (f ≫ g); simp, }

def homotopy_equiv {Z : C} (P Q : resolution Z) : P.complex ⟶ Q.complex :=
  lift (𝟙 Z) P Q

@[simp] lemma homotopy_equiv_commutes {Z : C} (P Q : resolution Z) :
  homotopy_equiv P Q ≫ Q.map = P.map :=
by simp [homotopy_equiv]

-- TODO state that in the homotopy category `resolution.homotopy_equiv P Q` becomes an isomorphism
-- (and hence that it is a homotopy equivalence and a quasi-isomorphism).

-- TODO construct `resolution_functor : C ⥤ homotopy_category C ℕ`



end resolution

end enough_projectives

end projective

end category_theory
