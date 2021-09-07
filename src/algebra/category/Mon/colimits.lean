/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Mon.basic
import category_theory.limits.has_limits
import category_theory.limits.concrete_category
import category_theory.limits.preserves.filtered

/-!
# The category of monoids has all colimits.

We do this construction knowing nothing about monoids.
In particular, I want to claim that this file could be produced by a python script
that just looks at the output of `#print monoid`:

  -- structure monoid : Type u → Type u
  -- fields:
  -- monoid.mul : Π {α : Type u} [c : monoid α], α → α → α
  -- monoid.mul_assoc : ∀ {α : Type u} [c : monoid α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
  -- monoid.one : Π (α : Type u) [c : monoid α], α
  -- monoid.one_mul : ∀ {α : Type u} [c : monoid α] (a : α), 1 * a = a
  -- monoid.mul_one : ∀ {α : Type u} [c : monoid α] (a : α), a * 1 = a

and if we'd fed it the output of `#print comm_ring`, this file would instead build
colimits of commutative rings.

A slightly bolder claim is that we could do this with tactics, as well.
-/

universes v

open category_theory
open category_theory.limits

namespace Mon.colimits
/-!
We build the colimit of a diagram in `Mon` by constructing the
free monoid on the disjoint union of all the monoids in the diagram,
then taking the quotient by the monoid laws within each monoid,
and the identifications given by the morphisms in the diagram.
-/

variables {J : Type v} [small_category J] (F : J ⥤ Mon.{v})

/--
An inductive type representing all monoid expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive prequotient
-- There's always `of`
| of : Π (j : J) (x : F.obj j), prequotient
-- Then one generator for each operation
| one : prequotient
| mul : prequotient → prequotient → prequotient

instance : inhabited (prequotient F) := ⟨prequotient.one⟩

open prequotient

/--
The relation on `prequotient` saying when two expressions are equal
because of the monoid laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive relation : prequotient F → prequotient F → Prop
-- Make it an equivalence relation:
| refl : Π (x), relation x x
| symm : Π (x y) (h : relation x y), relation y x
| trans : Π (x y z) (h : relation x y) (k : relation y z), relation x z
-- There's always a `map` relation
| map : Π (j j' : J) (f : j ⟶ j') (x : F.obj j), relation (of j' ((F.map f) x)) (of j x)
-- Then one relation per operation, describing the interaction with `of`
| mul : Π (j) (x y : F.obj j), relation (of j (x * y)) (mul (of j x) (of j y))
| one : Π (j), relation (of j 1) one
-- Then one relation per argument of each operation
| mul_1 : Π (x x' y) (r : relation x x'), relation (mul x y) (mul x' y)
| mul_2 : Π (x y y') (r : relation y y'), relation (mul x y) (mul x y')
-- And one relation per axiom
| mul_assoc : Π (x y z), relation (mul (mul x y) z) (mul x (mul y z))
| one_mul : Π (x), relation (mul one x) x
| mul_one : Π (x), relation (mul x one) x

/--
The setoid corresponding to monoid expressions modulo monoid relations and identifications.
-/
def colimit_setoid : setoid (prequotient F) :=
{ r := relation F, iseqv := ⟨relation.refl, relation.symm, relation.trans⟩ }
attribute [instance] colimit_setoid

/--
The underlying type of the colimit of a diagram in `Mon`.
-/
@[derive inhabited]
def colimit_type : Type v := quotient (colimit_setoid F)

instance monoid_colimit_type : monoid (colimit_type F) :=
{ mul :=
  begin
    fapply @quot.lift _ _ ((colimit_type F) → (colimit_type F)),
    { intro x,
      fapply @quot.lift,
      { intro y,
        exact quot.mk _ (mul x y) },
      { intros y y' r,
        apply quot.sound,
        exact relation.mul_2 _ _ _ r } },
    { intros x x' r,
      funext y,
      induction y,
      dsimp,
      apply quot.sound,
      { exact relation.mul_1 _ _ _ r },
      { refl } },
  end,
  one :=
  begin
    exact quot.mk _ one
  end,
  mul_assoc := λ x y z,
  begin
    induction x,
    induction y,
    induction z,
    dsimp,
    apply quot.sound,
    apply relation.mul_assoc,
    refl,
    refl,
    refl,
  end,
  one_mul := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.one_mul,
    refl,
  end,
  mul_one := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.mul_one,
    refl,
  end }

@[simp] lemma quot_one : quot.mk setoid.r one = (1 : colimit_type F) := rfl
@[simp] lemma quot_mul (x y) : quot.mk setoid.r (mul x y) =
  ((quot.mk setoid.r x) * (quot.mk setoid.r y) : colimit_type F) := rfl

/-- The bundled monoid giving the colimit of a diagram. -/
def colimit : Mon := ⟨colimit_type F, by apply_instance⟩

/-- The function from a given monoid in the diagram to the colimit monoid. -/
def cocone_fun (j : J) (x : F.obj j) : colimit_type F :=
quot.mk _ (of j x)

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
{ to_fun := cocone_fun F j,
  map_one' := quot.sound (relation.one _),
  map_mul' := λ x y, quot.sound (relation.mul _ _ _) }

@[simp] lemma cocone_naturality {j j' : J} (f : j ⟶ j') :
  F.map f ≫ (cocone_morphism F j') = cocone_morphism F j :=
begin
  ext,
  apply quot.sound,
  apply relation.map,
end

@[simp] lemma cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j):
  (cocone_morphism F j') (F.map f x) = (cocone_morphism F j) x :=
by { rw ←cocone_naturality F f, refl }

/-- The cocone over the proposed colimit monoid. -/
def colimit_cocone : cocone F :=
{ X := colimit F,
  ι :=
  { app := cocone_morphism F, } }.

/-- The function from the free monoid on the diagram to the cone point of any other cocone. -/
@[simp] def desc_fun_lift (s : cocone F) : prequotient F → s.X
| (of j x)  := (s.ι.app j) x
| one       := 1
| (mul x y) := desc_fun_lift x * desc_fun_lift y

/-- The function from the colimit monoid to the cone point of any other cocone. -/
def desc_fun (s : cocone F) : colimit_type F → s.X :=
begin
  fapply quot.lift,
  { exact desc_fun_lift F s },
  { intros x y r,
    induction r; try { dsimp },
    -- refl
    { refl },
    -- symm
    { exact r_ih.symm },
    -- trans
    { exact eq.trans r_ih_h r_ih_k },
    -- map
    { simp, },
    -- mul
    { simp, },
    -- one
    { simp, },
    -- mul_1
    { rw r_ih, },
    -- mul_2
    { rw r_ih, },
    -- mul_assoc
    { rw mul_assoc, },
    -- one_mul
    { rw one_mul, },
    -- mul_one
    { rw mul_one, } }
end

/-- The monoid homomorphism from the colimit monoid to the cone point of any other cocone. -/
def desc_morphism (s : cocone F) : colimit F ⟶ s.X :=
{ to_fun := desc_fun F s,
  map_one' := rfl,
  map_mul' := λ x y, by { induction x; induction y; refl }, }

/-- Evidence that the proposed colimit is the colimit. -/
def colimit_is_colimit : is_colimit (colimit_cocone F) :=
{ desc := λ s, desc_morphism F s,
  uniq' := λ s m w,
  begin
    ext,
    induction x,
    induction x,
    { have w' := congr_fun (congr_arg (λ f : F.obj x_j ⟶ s.X, (f : F.obj x_j → s.X)) (w x_j)) x_x,
      erw w',
      refl, },
    { simp *, },
    { simp *, },
    refl
  end }.

instance has_colimits_Mon : has_colimits Mon :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk
    { cocone := colimit_cocone F,
      is_colimit := colimit_is_colimit F } } }

namespace filtered

open category_theory.is_filtered (renaming max → max')

local infixl `~` := types.filtered_colimit.rel (F ⋙ forget Mon)

noncomputable theory
open_locale classical

set_option profiler true

variables [is_filtered J]

instance monoid_obj (F : J ⥤ Mon) (j) :
  monoid ((F ⋙ forget Mon).obj j) :=
by { change monoid (F.obj j), apply_instance }

def one_colimit : types.quot (F ⋙ forget Mon) :=
quot.mk _ ⟨is_filtered.nonempty.some, 1⟩

lemma one_colimit_eq (j : J) : one_colimit F = quot.mk _ ⟨j, 1⟩ :=
begin
  apply quot.eqv_gen_sound,
  apply types.filtered_colimit.eqv_gen_quot_rel_of_rel,
  refine ⟨is_filtered.max _ _, is_filtered.left_to_max _ _, is_filtered.right_to_max _ _, _⟩,
  simp,
end

def mul_colimit_pre (x y : Σ j, F.obj j) : types.quot (F ⋙ forget Mon) :=
quot.mk _ ⟨is_filtered.max x.1 y.1,
  F.map (is_filtered.left_to_max x.1 y.1) x.2 * F.map (is_filtered.right_to_max x.1 y.1) y.2⟩

lemma mul_colimit_pre_eq_of_rel_left {x x' y : Σ j, F.obj j} (hxx' : x ~ x') :
  mul_colimit_pre F x y = mul_colimit_pre F x' y :=
begin
  cases x with j₁ x, cases y with j₂ y, cases x' with j₃ x',
  obtain ⟨l, f, g, hfg⟩ := hxx',
  simp at hfg,
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ := crown (left_to_max j₁ j₂) (right_to_max j₁ j₂)
    (right_to_max j₃ j₂) (left_to_max j₃ j₂) f g,
  apply quot.eqv_gen_sound,
  apply types.filtered_colimit.eqv_gen_quot_rel_of_rel,
  use [s, α, γ],
  dsimp,
  simp_rw [monoid_hom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp, comp_apply, hfg]
end

lemma mul_colimit_pre_eq_of_rel_right {x y y' : Σ j, F.obj j} (hyy' : y ~ y') :
  mul_colimit_pre F x y = mul_colimit_pre F x y' :=
begin
  obtain ⟨l, α, β, hαβ⟩ := hyy',
  simp at hαβ,
  let O : finset J := {x.1, y.1, y'.1, max' x.1 y.1, max' x.1 y'.1, l},
  obtain ⟨x_mem, y_mem, y'_mem, k_mem, k'_mem, l_mem⟩ :
    x.1 ∈ O ∧ y.1 ∈ O ∧ y'.1 ∈ O ∧ max' x.1 y.1 ∈ O ∧ max' x.1 y'.1 ∈ O ∧ l ∈ O,
  { simp only [finset.mem_insert, finset.mem_singleton], tauto },

  let H_type := Σ' (i j : J) (mi : i ∈ O) (mY : j ∈ O), i ⟶ j,
  let H : finset H_type := { ⟨_, _, _, _, α⟩, ⟨_, _, _, _, β⟩,
    ⟨_, _, _, _, left_to_max x.1 y.1⟩, ⟨_, _, _, _, right_to_max x.1 y.1⟩,
    ⟨_, _, _, _, left_to_max x.1 y'.1⟩, ⟨_, _, _, _, right_to_max x.1 y'.1⟩ },

  obtain ⟨α_mem, β_mem, f_mem, g_mem, f'_mem, g'_mem⟩ :
    (⟨_, _, y_mem, l_mem, α⟩ : H_type) ∈ H ∧ (⟨_, _, y'_mem, l_mem, β⟩ : H_type) ∈ H ∧
    (⟨_, _, x_mem, k_mem, left_to_max x.1 y.1⟩ : H_type) ∈ H ∧
    (⟨_, _, y_mem, k_mem, right_to_max x.1 y.1⟩ : H_type) ∈ H ∧
    (⟨_, _, x_mem, k'_mem, left_to_max x.1 y'.1 ⟩ : H_type) ∈ H ∧
    (⟨_, _, y'_mem, k'_mem, right_to_max x.1 y'.1⟩ : H_type) ∈ H,
  { simp only [finset.mem_insert, finset.mem_singleton],
    split, left, split, refl, refl,
    split, right, left, split, refl, refl,
    split, right, right, left, split, refl, refl,
    split, right, right, right, left, split, refl, refl,
    split, right, right, right, right, left, split, refl, refl,
    right, right, right, right, right, split, refl, refl },

  obtain ⟨s, T, hT⟩ := sup_exists O H,
  apply quot.eqv_gen_sound,
  apply types.filtered_colimit.eqv_gen_quot_rel_of_rel,
  refine ⟨s, T k_mem, T k'_mem, _⟩,
  dsimp,
  rw [monoid_hom.map_mul, monoid_hom.map_mul, ← comp_apply, ← comp_apply, ← comp_apply,
    ← comp_apply, ← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp,
    hT x_mem k_mem f_mem, hT y_mem k_mem g_mem, hT x_mem k'_mem f'_mem, hT y'_mem k'_mem g'_mem,
    ← hT y_mem l_mem α_mem, ← hT y'_mem l_mem β_mem, F.map_comp, F.map_comp, comp_apply,
    comp_apply, hαβ],
end

def mul_colimit (x y : types.quot (F ⋙ forget Mon)) : types.quot (F ⋙ forget Mon) :=
begin
  refine quot.lift₂ (mul_colimit_pre F) _ _ x y,
  { intros x y y' h,
    apply mul_colimit_pre_eq_of_rel_right,
    apply types.filtered_colimit.rel_of_quot_rel,
    exact h },
  { intros x x' y h,
    apply mul_colimit_pre_eq_of_rel_left,
    apply types.filtered_colimit.rel_of_quot_rel,
    exact h },
end

lemma mul_colimit_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
  mul_colimit F (quot.mk _ x) (quot.mk _ y) = quot.mk _ ⟨k, F.map f x.2 * F.map g y.2⟩ :=
begin
  cases x with j₁ x, cases y with j₂ y,
  obtain ⟨s, α, β, h₁, h₂⟩ := bowtie (left_to_max j₁ j₂) f (right_to_max j₁ j₂) g,
  apply quot.eqv_gen_sound,
  apply types.filtered_colimit.eqv_gen_quot_rel_of_rel,
  use [s, α, β],
  dsimp,
  simp_rw [monoid_hom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂],
end

lemma colimit_one_mul (x : types.quot (F ⋙ forget Mon)) :
  mul_colimit F (one_colimit F) x = x :=
begin
  apply quot.induction_on x, clear x, intro x,
  cases x with j x,
  rw [one_colimit_eq F j, mul_colimit_eq F ⟨j, 1⟩ ⟨j, x⟩ j (𝟙 j) (𝟙 j)],
  congr,
  rw [monoid_hom.map_one, one_mul, F.map_id, id_apply],
end

lemma colimit_mul_one (x : types.quot (F ⋙ forget Mon)) :
  mul_colimit F x (one_colimit F) = x :=
begin
  apply quot.induction_on x, clear x, intro x,
  cases x with j x,
  rw [one_colimit_eq F j, mul_colimit_eq F ⟨j, x⟩ ⟨j, 1⟩ j (𝟙 j) (𝟙 j)],
  congr,
  rw [monoid_hom.map_one, mul_one, F.map_id, id_apply],
end

lemma colimit_mul_assoc (x y z : types.quot (F ⋙ forget Mon)) :
  mul_colimit F (mul_colimit F x y) z = mul_colimit F x (mul_colimit F y z) :=
begin
  apply quot.induction_on₃ x y z, clear x y z, intros x y z,
  cases x with j₁ x, cases y with j₂ y, cases z with j₃ z,
  let k := max' (max' j₁ j₂) j₃,
  rw mul_colimit_eq F ⟨j₁, x⟩ ⟨j₂, y⟩ k (left_to_max _ _ ≫ left_to_max _ _)
    (right_to_max _ _ ≫ left_to_max _ _),
  rw mul_colimit_eq F ⟨k, _⟩ ⟨j₃, z⟩ k (𝟙 k) (right_to_max _ _),
  rw mul_colimit_eq F ⟨j₂, y⟩ ⟨j₃, z⟩ k (right_to_max _ _ ≫ left_to_max _ _) (right_to_max _ _),
  rw mul_colimit_eq F ⟨j₁, x⟩ ⟨k, _⟩ k (left_to_max _ _ ≫ left_to_max _ _) (𝟙 k),
  dsimp,
  congr' 1,
  rw [F.map_id, id_apply, id_apply, mul_assoc],
end

instance colimit_monoid : monoid (types.quot (F ⋙ forget Mon)) :=
{ one := one_colimit F,
  mul := mul_colimit F,
  one_mul := colimit_one_mul F,
  mul_one := colimit_mul_one F,
  mul_assoc := colimit_mul_assoc F }

/-- The bundled monoid giving the colimit of a diagram. -/
def colimit : Mon := ⟨types.quot (F ⋙ forget Mon), by apply_instance⟩

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
{ to_fun := (types.colimit_cocone (F ⋙ forget Mon)).ι.app j,
  map_one' := (one_colimit_eq F j).symm,
  map_mul' := λ x y, begin
    convert (mul_colimit_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 j) (𝟙 j)).symm,
    rw [F.map_id, id_apply, id_apply], refl,
  end }

@[simp] lemma cocone_naturality {j j' : J} (f : j ⟶ j') :
  F.map f ≫ (cocone_morphism F j') = cocone_morphism F j :=
begin
  apply monoid_hom.coe_inj,
  exact (types.colimit_cocone (F ⋙ forget Mon)).ι.naturality f,
end

/-- The cocone over the proposed colimit monoid. -/
noncomputable
def colimit_cocone : cocone F :=
{ X := colimit F,
  ι := { app := cocone_morphism F } }.

def blub : cocone F → cocone (F ⋙ forget Mon) := λ t,
{ X := t.X, ι := { app := λ j, t.ι.app j } }

def colimit_desc (t : cocone F) : colimit F ⟶ t.X :=
{ to_fun := (types.colimit_cocone_is_colimit (F ⋙ forget Mon)).desc (blub F t),
  map_one' := begin
    change (types.colimit_cocone_is_colimit (F ⋙ forget Mon)).desc (blub F t) (one_colimit F) = _,
    dsimp [types.colimit_cocone_is_colimit, one_colimit, blub],
    rw monoid_hom.map_one,
  end,
  map_mul' := λ x y, begin
    sorry
  end }

def colimit_cocone_is_colimit : is_colimit (colimit_cocone F) :=
{ desc := colimit_desc F, fac' := sorry, uniq' := sorry }

instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget Mon) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F) (types.colimit_cocone_is_colimit (F ⋙ forget Mon)) } }

end filtered

end Mon.colimits
