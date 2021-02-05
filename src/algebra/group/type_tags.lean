/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.group.hom
import data.equiv.basic
import tactic.equiv_rw

/-!
# Type tags that turn additive structures into multiplicative, and vice versa

We define two type tags:

* `additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `additive α`;
* `multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `multiplicative α`.

We also define instances `additive.*` and `multiplicative.*` that actually transfer the structures.
-/

universes u v
variables {α : Type u} {β : Type v}

/-- If `α` carries some multiplicative structure, then `additive α` carries the corresponding
additive structure. -/
structure additive (α : Type*) := (out : α)

/-- If `α` carries some additive structure, then `multiplicative α` carries the corresponding
multiplicative structure. -/
structure multiplicative (α : Type*) := (out : α)

namespace additive

/-- Reinterpret `x : α` as an element of `additive α`. -/
def of_mul : α ≃ additive α :=
⟨additive.mk, additive.out, λ _, rfl, λ ⟨_⟩, rfl⟩

/-- Reinterpret `x : additive α` as an element of `α`. -/
def to_mul : additive α ≃ α := of_mul.symm

@[simp] lemma of_mul_symm_eq : (@of_mul α).symm = to_mul := rfl

@[simp] lemma to_mul_symm_eq : (@to_mul α).symm = of_mul := rfl

@[ext] protected lemma ext {x y : additive α} : x.to_mul = y.to_mul → x = y :=
to_mul.apply_eq_iff_eq.mp

protected lemma ext_iff {x y : additive α} : x = y ↔ x.to_mul = y.to_mul :=
⟨congr_arg _, additive.ext⟩

end additive

namespace multiplicative

/-- Reinterpret `x : α` as an element of `multiplicative α`. -/
def of_add : α ≃ multiplicative α :=
⟨mk, out, λ _, rfl, λ ⟨_⟩, rfl⟩

/-- Reinterpret `x : multiplicative α` as an element of `α`. -/
def to_add : multiplicative α ≃ α := of_add.symm

@[simp] lemma of_add_symm_eq : (@of_add α).symm = to_add := rfl

@[simp] lemma to_add_symm_eq : (@to_add α).symm = of_add := rfl

@[ext] protected lemma ext {x y : multiplicative α} : x.to_add = y.to_add → x = y :=
to_add.apply_eq_iff_eq.mp

protected lemma ext_iff {x y : multiplicative α} : x = y ↔ x.to_add = y.to_add :=
⟨congr_arg _, multiplicative.ext⟩

end multiplicative

@[simp] lemma to_add_of_add (x : α) : (multiplicative.of_add x).to_add = x := rfl
@[simp] lemma of_add_to_add (x : multiplicative α) : multiplicative.of_add x.to_add = x :=
multiplicative.of_add.right_inv _

@[simp] lemma to_mul_of_mul (x : α) : (additive.of_mul x).to_mul = x := rfl
@[simp] lemma of_mul_to_mul (x : additive α) : additive.of_mul x.to_mul = x :=
additive.of_mul.right_inv _

-- TODO: equiv_rw should probably be able to do this
lemma exists_multiplicative_iff (p : multiplicative α → Prop) :
  (∃ x, p x) ↔ ∃ x, p (multiplicative.of_add x) :=
⟨λ ⟨x, h⟩, ⟨x.to_add, by simpa⟩, λ ⟨x, h⟩, ⟨_, h⟩⟩

-- TODO: equiv_rw should probably be able to do this
lemma forall_multiplicative_iff (p : multiplicative α → Prop) :
  (∀ x, p x) ↔ ∀ x, p (multiplicative.of_add x) :=
⟨λ h x, h _, λ h x, by simpa using h x.to_add⟩

-- TODO: equiv_rw should probably be able to do this
lemma exists_additive_iff (p : additive α → Prop) :
  (∃ x, p x) ↔ ∃ x, p (additive.of_mul x) :=
⟨λ ⟨x, h⟩, ⟨x.to_mul, by simpa⟩, λ ⟨x, h⟩, ⟨_, h⟩⟩

-- TODO: equiv_rw should probably be able to do this
lemma forall_additive_iff (p : additive α → Prop) :
  (∀ x, p x) ↔ ∀ x, p (additive.of_mul x) :=
⟨λ h x, h _, λ h x, by simpa using h x.to_mul⟩

instance [inhabited α] : inhabited (additive α) := ⟨additive.of_mul (default α)⟩
instance [inhabited α] : inhabited (multiplicative α) := ⟨multiplicative.of_add (default α)⟩

instance additive.has_add [has_mul α] : has_add (additive α) :=
{ add := λ x y, additive.of_mul (x.to_mul * y.to_mul) }

instance [has_add α] : has_mul (multiplicative α) :=
{ mul := λ x y, multiplicative.of_add (x.to_add + y.to_add) }

@[simp] lemma of_add_add [has_add α] (x y : α) :
  multiplicative.of_add (x + y) = multiplicative.of_add x * multiplicative.of_add y :=
rfl

@[simp] lemma to_add_mul [has_add α] (x y : multiplicative α) :
  (x * y).to_add = x.to_add + y.to_add :=
rfl

@[simp] lemma of_mul_mul [has_mul α] (x y : α) :
  additive.of_mul (x * y) = additive.of_mul x + additive.of_mul y :=
rfl

@[simp] lemma to_mul_add [has_mul α] (x y : additive α) :
  (x + y).to_mul = x.to_mul * y.to_mul :=
rfl

instance [semigroup α] : add_semigroup (additive α) :=
{ add_assoc := by { equiv_rw additive.to_mul, simpa [← of_mul_mul] using mul_assoc },
  ..additive.has_add }

instance [add_semigroup α] : semigroup (multiplicative α) :=
{ mul_assoc := by { equiv_rw multiplicative.to_add, simpa [← of_add_add] using add_assoc },
  ..multiplicative.has_mul }

instance [comm_semigroup α] : add_comm_semigroup (additive α) :=
{ add_comm := by { equiv_rw additive.to_mul, simpa [← of_mul_mul] using mul_comm },
  ..additive.add_semigroup }

instance [add_comm_semigroup α] : comm_semigroup (multiplicative α) :=
{ mul_comm := by { equiv_rw multiplicative.to_add, simpa [← of_add_add] using add_comm },
  ..multiplicative.semigroup }

instance [left_cancel_semigroup α] : add_left_cancel_semigroup (additive α) :=
{ add_left_cancel := by { equiv_rw additive.to_mul, simp [← of_mul_mul] },
  ..additive.add_semigroup }

instance [add_left_cancel_semigroup α] : left_cancel_semigroup (multiplicative α) :=
{ mul_left_cancel := by { equiv_rw multiplicative.to_add, simp [← of_add_add] },
  ..multiplicative.semigroup }

instance [right_cancel_semigroup α] : add_right_cancel_semigroup (additive α) :=
{ add_right_cancel := by { equiv_rw additive.to_mul, simp [← of_mul_mul] },
  ..additive.add_semigroup }

instance [add_right_cancel_semigroup α] : right_cancel_semigroup (multiplicative α) :=
{ mul_right_cancel := by { equiv_rw multiplicative.to_add, simp [← of_add_add] },
  ..multiplicative.semigroup }

instance [has_one α] : has_zero (additive α) := ⟨additive.of_mul 1⟩

@[simp] lemma of_mul_one [has_one α] : @additive.of_mul α 1 = 0 := rfl

@[simp] lemma to_mul_zero [has_one α] : (0 : additive α).to_mul = 1 := rfl

instance [has_zero α] : has_one (multiplicative α) := ⟨multiplicative.of_add 0⟩

@[simp] lemma of_add_zero [has_zero α] : @multiplicative.of_add α 0 = 1 := rfl

@[simp] lemma to_add_one [has_zero α] : (1 : multiplicative α).to_add = 0 := rfl

instance [monoid α] : add_monoid (additive α) :=
{ zero     := 0,
  zero_add := by { equiv_rw additive.to_mul, simp [← of_mul_mul, ← @of_mul_one α, -of_mul_one] },
  add_zero := by { equiv_rw additive.to_mul, simp [← of_mul_mul, ← @of_mul_one α, -of_mul_one] },
  ..additive.add_semigroup }

instance [add_monoid α] : monoid (multiplicative α) :=
{ one     := 1,
  one_mul := begin
    equiv_rw multiplicative.to_add,
    simp [← of_add_add, ← @of_add_zero α, -of_add_zero]
  end,
  mul_one := begin
    equiv_rw multiplicative.to_add,
    simp [← of_add_add, ← @of_add_zero α, -of_add_zero]
  end,
  ..multiplicative.semigroup }

instance [comm_monoid α] : add_comm_monoid (additive α) :=
{ .. additive.add_monoid, .. additive.add_comm_semigroup }

instance [add_comm_monoid α] : comm_monoid (multiplicative α) :=
{ ..multiplicative.monoid, .. multiplicative.comm_semigroup }

instance [has_inv α] : has_neg (additive α) :=
⟨λ x, additive.of_mul x.to_mul⁻¹⟩

@[simp] lemma of_mul_inv [has_inv α] (x : α) : additive.of_mul x⁻¹ = -(additive.of_mul x) := rfl

@[simp] lemma to_mul_neg [has_inv α] (x : additive α) : (-x).to_mul = x.to_mul⁻¹ := rfl

instance [has_neg α] : has_inv (multiplicative α) :=
⟨λ x, multiplicative.of_add (-x.to_add)⟩

@[simp] lemma of_add_neg [has_neg α] (x : α) :
  multiplicative.of_add (-x) = (multiplicative.of_add x)⁻¹ := rfl

@[simp] lemma to_add_inv [has_neg α] (x : multiplicative α) :
  (x⁻¹).to_add = -x.to_add := rfl

instance additive.has_sub [has_div α] : has_sub (additive α) :=
{ sub := λ x y, additive.of_mul (x.to_mul / y.to_mul) }

instance multiplicative.has_div [has_sub α] : has_div (multiplicative α) :=
{ div := λ x y, multiplicative.of_add (x.to_add - y.to_add) }

@[simp] lemma of_add_sub [has_sub α] (x y : α) :
  multiplicative.of_add (x - y) = multiplicative.of_add x / multiplicative.of_add y :=
rfl

@[simp] lemma to_add_div [has_sub α] (x y : multiplicative α) :
  (x / y).to_add = x.to_add - y.to_add :=
rfl

@[simp] lemma of_mul_div [has_div α] (x y : α) :
  additive.of_mul (x / y) = additive.of_mul x - additive.of_mul y :=
rfl

@[simp] lemma to_mul_sub [has_div α] (x y : additive α) :
  (x - y).to_mul = x.to_mul / y.to_mul :=
rfl

instance [div_inv_monoid α] : sub_neg_monoid (additive α) :=
{ sub_eq_add_neg := begin
    equiv_rw additive.to_mul,
    simp [← of_mul_div, ← of_mul_inv, ← of_mul_mul, div_eq_mul_inv]
  end,
  .. additive.has_neg, .. additive.has_sub, .. additive.add_monoid }

instance [sub_neg_monoid α] : div_inv_monoid (multiplicative α) :=
{ div_eq_mul_inv := begin
    equiv_rw multiplicative.to_add,
    simp [← of_add_sub, ← of_add_neg, ← of_add_add, sub_eq_add_neg]
  end,
  .. multiplicative.has_inv, .. multiplicative.has_div, .. multiplicative.monoid }

instance [group α] : add_group (additive α) :=
{ add_left_neg := by { equiv_rw additive.to_mul, simp [← of_mul_inv, ← of_mul_mul] },
  .. additive.sub_neg_monoid }

instance [add_group α] : group (multiplicative α) :=
{ mul_left_inv := by { equiv_rw multiplicative.to_add, simp [← of_add_neg, ← of_add_add] },
  .. multiplicative.div_inv_monoid }

instance [comm_group α] : add_comm_group (additive α) :=
{ .. additive.add_group, .. additive.add_comm_monoid }

instance [add_comm_group α] : comm_group (multiplicative α) :=
{ .. multiplicative.group, .. multiplicative.comm_monoid }

/-- Reinterpret `α →+ β` as `multiplicative α →* multiplicative β`. -/
@[simps]
def add_monoid_hom.to_multiplicative [add_monoid α] [add_monoid β] :
  (α →+ β) ≃ (multiplicative α →* multiplicative β) :=
⟨λ f, ⟨λ a, multiplicative.of_add (f a.to_add), by simp, by simp⟩,
 λ f, ⟨λ a, (f (multiplicative.of_add a)).to_add, by simp, by simp⟩,
 λ _, by simp, λ _, by simp⟩

/-- Reinterpret `α →* β` as `additive α →+ additive β`. -/
@[simps]
def monoid_hom.to_additive [monoid α] [monoid β] :
  (α →* β) ≃ (additive α →+ additive β) :=
⟨λ f, ⟨λ a, additive.of_mul (f a.to_mul), by simp, by simp⟩,
 λ f, ⟨λ a, (f (additive.of_mul a)).to_mul, by simp, by simp⟩,
 λ _, by simp, λ _, by simp⟩

/-- Reinterpret `additive α →+ β` as `α →* multiplicative β`. -/
@[simps]
def add_monoid_hom.to_multiplicative' [monoid α] [add_monoid β] :
  (additive α →+ β) ≃ (α →* multiplicative β) :=
⟨λ f, ⟨λ a, multiplicative.of_add (f (additive.of_mul a)), by simp, by simp⟩,
 λ f, ⟨λ a, (f a.to_mul).to_add, by simp, by simp⟩,
 λ _, by simp, λ _, by simp⟩

/-- Reinterpret `α →* multiplicative β` as `additive α →+ β`. -/
@[simps { value_md := semireducible }]
def monoid_hom.to_additive' [monoid α] [add_monoid β] :
  (α →* multiplicative β) ≃ (additive α →+ β) :=
add_monoid_hom.to_multiplicative'.symm

/-- Reinterpret `α →+ additive β` as `multiplicative α →* β`. -/
@[simps]
def add_monoid_hom.to_multiplicative'' [add_monoid α] [monoid β] :
  (α →+ additive β) ≃ (multiplicative α →* β) :=
⟨λ f, ⟨λ a, (f a.to_add).to_mul, by simp, by simp⟩,
 λ f, ⟨λ a, additive.of_mul (f (multiplicative.of_add a)), by simp, by simp⟩,
 λ _, by simp, λ _, by simp⟩

/-- Reinterpret `multiplicative α →* β` as `α →+ additive β`. -/
@[simps { value_md := semireducible }]
def monoid_hom.to_additive'' [add_monoid α] [monoid β] :
  (multiplicative α →* β) ≃ (α →+ additive β) :=
add_monoid_hom.to_multiplicative''.symm

@[simp]
lemma add_monoid_hom.to_multiplicative_conjugate [add_monoid α] [add_monoid β] (f : α →+ β) :
  multiplicative.to_add ∘ f.to_multiplicative ∘ multiplicative.of_add = f :=
by { ext, simp }

@[simp]
lemma monoid_hom.to_additive_conjugate [monoid α] [monoid β] (f : α →* β) :
  additive.to_mul ∘ f.to_additive ∘ additive.of_mul = f :=
by { ext, simp }
