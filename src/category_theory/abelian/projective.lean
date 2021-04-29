/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.exact
import algebra.homology.single
import algebra.homology.quasi_iso
import algebra.homology.homotopy
import algebra.homology.augment

/-!
# Projective objects and categories with enough projectives

An object `P` is called projective if every morphism out of `P` factors through every epimorphism.

A category `C` has enough projectives if every object admits an epimorphism from some
projective object.

`projective.over X` picks an arbitrary such projective object,
and `projective.π X : projective.over X ⟶ X` is the corresponding epimorphism.

Given a morphism `f : X ⟶ Y`, `projective.left f` is a projective object over `kernel f`,
and `projective.d f : projective.left f ⟶ X` is the morphism `π (kernel f) ≫ kernel.ι f`.
When `C` is abelian `projective.d f` and `f` are exact.
Hence, starting from an epimorphism `P ⟶ X`, where `P` is projective,
we can apply `projective.d` repeatedly to obtain a projective resolution of `X`.
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
(projective : projective P)
(f : P ⟶ X)
(epi : epi f)

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
variables [abelian C]

/--
When `C` is abelian, `projective.d f` and `f` are exact.
-/
lemma exact_d_f {X Y : C} (f : X ⟶ Y) : exact (d f) f :=
(abelian.exact_iff _ _).2 $
  ⟨by simp, zero_of_epi_comp (π _) $ by rw [←category.assoc, cokernel.condition]⟩

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

@[simp, reassoc] lemma resolution.complex_d_1_0_comp_map_f_0 {Z : C} (P : resolution Z) :
  P.complex.d 1 0 ≫ P.map.f 0 = 0 :=
sorry

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

def lift_f_zero {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) :
  P.complex.X 0 ⟶ Q.complex.X 0 :=
factor_thru (P.map.f 0 ≫ f) (Q.map.f 0)

local attribute [instance] epi_comp

def lift_f_one {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) :
  P.complex.X 1 ⟶ Q.complex.X 1 :=
begin
  have z : (P.complex.d 1 0 ≫ lift_f_zero f P Q) ≫ Q.map.f 0 = 0,
  { dsimp [lift_f_zero], simp, },
  let g := factor_thru_kernel_subobject (Q.map.f 0) _ z,
  haveI : category_theory.exact (Q.complex.d 1 0) (Q.map.f 0) := by {
    -- TODO: yuck:
    dsimp [map, complex, exact_sequence, chain_complex.truncate_to_single, chain_complex.truncate, chain_complex.to_single_equiv],
    split_ifs,
    { rw [category.comp_id, category.id_comp, category.id_comp, category.id_comp, exact_comp_iso],
      exact Q.exact 0, },
    { simpa using h, },
  },
  exact factor_thru g
    (factor_thru_image_subobject (Q.complex.d 1 0) ≫
      image_to_kernel (Q.complex.d 1 0) (Q.map.f 0) sorry)
end

def lift_f_succ {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) (n : ℕ)
  (p : Σ' (f : P.complex.X n ⟶ Q.complex.X n) (f' : P.complex.X (n+1) ⟶ Q.complex.X (n+1)), P.complex.d (n+1) n ≫ f = f' ≫ Q.complex.d (n+1) n) :
    Σ' f'' : P.complex.X (n+2) ⟶ Q.complex.X (n+2), P.complex.d (n+2) (n+1) ≫ p.2.1 = f'' ≫ Q.complex.d (n+2) (n+1) :=
begin
  rcases p with ⟨f, f', w⟩,
  have z : (P.complex.d (n+2) (n+1) ≫ f') ≫ Q.complex.d (n+1) n = 0,
  { rw [category.assoc, ←w, ←category.assoc, P.complex.d_comp_d, zero_comp], },
  let g := factor_thru_kernel_subobject (Q.complex.d (n+1) n) _ z,
  fsplit,
  exact factor_thru g
    (factor_thru_image_subobject (Q.complex.d (n+2) (n+1)) ≫
      image_to_kernel (Q.complex.d (n+2) (n+1)) (Q.complex.d (n+1) n) (Q.complex.d_comp_d _ _ _)),
  dsimp [g],
  sorry,
end

def lift {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) :
  P.complex ⟶ Q.complex :=
begin
  fapply chain_map.mk_inductive,
  apply lift_f_zero f,
  apply lift_f_one f,
  sorry,
  apply lift_f_succ f,
end

lemma lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) :
  lift f P Q ≫ Q.map = P.map ≫ (homological_complex.single C _ 0).map f :=
begin
  ext n,
  rcases n with (_|_|n),
  { dsimp [lift, chain_map.mk_inductive, chain_map.mk_inductive', lift_f_zero], simp, },
  sorry,
  sorry,
end

end resolution

end

namespace resolution

variables [preadditive C] [has_equalizers C] [has_images C] [has_image_maps C]
  [has_zero_object C] [has_cokernels C]

lemma lift_homotopy {Y Z : C} (f : Y ⟶ Z) {P : resolution Y} {Q : resolution Z}
  (g h : P.complex ⟶ Q.complex)
  (g_comm : g ≫ Q.map = P.map ≫ (homological_complex.single C _ 0).map f)
  (h_comm : h ≫ Q.map = P.map ≫ (homological_complex.single C _ 0).map f) :
  homotopy g h :=
sorry

def homotopy_equiv {Z : C} (P Q : resolution Z) : P.complex ⟶ Q.complex :=
  lift (𝟙 Z) P Q

@[simp] lemma homotopy_equiv_commutes {Z : C} (P Q : resolution Z) :
  homotopy_equiv P Q ≫ Q.map = P.map :=
sorry

-- TODO state that in the homotopy category `resolution.homotopy_equiv P Q` becomes an isomorphism
-- (and hence that it is a homotopy equivalence and a quasi-isomorphism).

-- TODO construct `resolution_functor : C ⥤ homotopy_category V ℕ`

end resolution

end enough_projectives

namespace resolution

/- We have to jump through some hoops to get `resolution.of` to typecheck! -/
section
variables (O : C → C) (π : Π X, O X ⟶ X)
variables (L : Π {X Y : C} (f : X ⟶ Y), C) (δ : Π {X Y : C} (f : X ⟶ Y), L f ⟶ X)

/-- An auxiliary construction for `resolution.of`. -/
def B' (Z : C) : ℕ → Σ (X Y : C), X ⟶ Y
| 0 := ⟨O Z, Z, π Z⟩
| (n+1) := ⟨L (B' n).2.2, (B' n).1, δ (B' n).2.2⟩

/-- An auxiliary construction for `resolution.of`. -/
def X' (Z : C) (n : ℕ) : C := (B' O π @L @δ Z n).2.1

/-- An auxiliary construction for `resolution.of`. -/
def d' (Z : C) (n : ℕ) : X' O π @L @δ Z (n+1) ⟶ X' O π @L @δ Z n :=
(B' O π @L @δ Z n).2.2

end

variables [enough_projectives C] [abelian C]

/--
In any category with enough projectives,
`projective.resolution.of Z` constructs a projection resolution of the object `Z`.
-/
def of (Z : C) : resolution Z :=
{ X := λ n, X' projective.over projective.π
    (λ (X Y : C) (f : X ⟶ Y), projective.left f)
    (λ (X Y : C) (f : X ⟶ Y), projective.d f)
    Z n,
  d := λ n, d' projective.over projective.π
    (λ (X Y : C) (f : X ⟶ Y), projective.left f)
    (λ (X Y : C) (f : X ⟶ Y), projective.d f)
    Z n,
  zero := iso.refl _,
  projective := λ n,
  begin
    induction n;
    { dsimp [X', B'],
      apply_instance, },
  end,
  epi := projective.π_epi _,
  exact := λ n, exact_d_f _ }

end resolution

end projective

end category_theory
