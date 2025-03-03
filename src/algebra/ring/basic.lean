/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import algebra.divisibility
import algebra.regular.basic
import data.int.cast.defs
import data.pi.algebra

/-!
# Semirings and rings

This file defines semirings, rings and domains. This is analogous to `algebra.group.defs` and
`algebra.group.basic`, the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

## Main definitions

* `distrib`: Typeclass for distributivity of multiplication over addition.
* `has_distrib_neg`: Typeclass for commutativity of negation and multiplication. This is useful when
  dealing with multiplicative submonoids which are closed under negation without being closed under
  addition, for example `units`.
* `(non_unital_)(non_assoc_)(semi)ring`: Typeclasses for possibly non-unital or non-associative
  rings and semirings. Some combinations are not defined yet because they haven't found use.

## Tags

`semiring`, `comm_semiring`, `ring`, `comm_ring`, `domain`, `is_domain`, `nonzero`, `units`
-/
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

set_option old_structure_cmd true
open function

/-!
### `distrib` class
-/

/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
@[protect_proj, ancestor has_mul has_add]
class distrib (R : Type*) extends has_mul R, has_add R :=
(left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c)
(right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c)

/-- A typeclass stating that multiplication is left distributive over addition. -/
@[protect_proj]
class left_distrib_class (R : Type*) [has_mul R] [has_add R] :=
(left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c)

/-- A typeclass stating that multiplication is right distributive over addition. -/
@[protect_proj]
class right_distrib_class (R : Type*) [has_mul R] [has_add R] :=
(right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c)

@[priority 100] -- see Note [lower instance priority]
instance distrib.left_distrib_class (R : Type*) [distrib R] : left_distrib_class R :=
⟨distrib.left_distrib⟩

@[priority 100] -- see Note [lower instance priority]
instance distrib.right_distrib_class (R : Type*) [distrib R] : right_distrib_class R :=
⟨distrib.right_distrib⟩

lemma left_distrib [has_mul R] [has_add R] [left_distrib_class R] (a b c : R) :
  a * (b + c) = a * b + a * c :=
left_distrib_class.left_distrib a b c

alias left_distrib ← mul_add

lemma right_distrib [has_mul R] [has_add R] [right_distrib_class R] (a b c : R) :
  (a + b) * c = a * c + b * c :=
right_distrib_class.right_distrib a b c

alias right_distrib ← add_mul

lemma distrib_three_right [has_mul R] [has_add R] [right_distrib_class R] (a b c d : R) :
  (a + b + c) * d = a * d + b * d + c * d :=
by simp [right_distrib]

/-- Pullback a `distrib` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.distrib {S} [has_mul R] [has_add R] [distrib S]
  (f : R → S) (hf : injective f) (add : ∀ x y, f (x + y) = f x + f y)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  distrib R :=
{ mul := (*),
  add := (+),
  left_distrib := λ x y z, hf $ by simp only [*, left_distrib],
  right_distrib := λ x y z, hf $ by simp only [*, right_distrib] }

/-- Pushforward a `distrib` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.distrib {S} [distrib R] [has_add S] [has_mul S]
  (f : R → S) (hf : surjective f) (add : ∀ x y, f (x + y) = f x + f y)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  distrib S :=
{ mul := (*),
  add := (+),
  left_distrib := hf.forall₃.2 $ λ x y z, by simp only [← add, ← mul, left_distrib],
  right_distrib := hf.forall₃.2 $ λ x y z, by simp only [← add, ← mul, right_distrib] }

/-!
### Semirings
-/

/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
@[protect_proj, ancestor add_comm_monoid distrib mul_zero_class]
class non_unital_non_assoc_semiring (α : Type u) extends
  add_comm_monoid α, distrib α, mul_zero_class α

/-- An associative but not-necessarily unital semiring. -/
@[protect_proj, ancestor non_unital_non_assoc_semiring semigroup_with_zero]
class non_unital_semiring (α : Type u) extends
  non_unital_non_assoc_semiring α, semigroup_with_zero α

/-- A unital but not-necessarily-associative semiring. -/
@[protect_proj, ancestor non_unital_non_assoc_semiring mul_zero_one_class]
class non_assoc_semiring (α : Type u) extends
  non_unital_non_assoc_semiring α, mul_zero_one_class α, add_comm_monoid_with_one α

/-- A semiring is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), multiplicative monoid (`monoid`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). The actual definition extends `monoid_with_zero`
instead of `monoid` and `mul_zero_class`. -/
@[protect_proj, ancestor non_unital_semiring non_assoc_semiring monoid_with_zero]
class semiring (α : Type u) extends non_unital_semiring α, non_assoc_semiring α, monoid_with_zero α

section injective_surjective_maps

variables [has_zero β] [has_add β] [has_mul β] [has_smul ℕ β]

/-- Pullback a `non_unital_non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_non_assoc_semiring
  {α : Type u} [non_unital_non_assoc_semiring α]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_non_assoc_semiring β :=
{ .. hf.mul_zero_class f zero mul, .. hf.add_comm_monoid f zero add nsmul, .. hf.distrib f add mul }

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_semiring
  {α : Type u} [non_unital_semiring α]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_semiring β :=
{ .. hf.non_unital_non_assoc_semiring f zero add mul nsmul, .. hf.semigroup_with_zero f zero mul }

/-- Pullback a `non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_assoc_semiring
  {α : Type u} [non_assoc_semiring α]
  {β : Type v} [has_zero β] [has_one β] [has_mul β] [has_add β]
  [has_smul ℕ β] [has_nat_cast β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (nat_cast : ∀ n : ℕ, f n = n) :
  non_assoc_semiring β :=
{ .. hf.add_monoid_with_one f zero one add nsmul nat_cast,
  .. hf.non_unital_non_assoc_semiring f zero add mul nsmul,
  .. hf.mul_one_class f one mul }

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.semiring
  {α : Type u} [semiring α]
  {β : Type v} [has_zero β] [has_one β] [has_add β] [has_mul β] [has_pow β ℕ]
  [has_smul ℕ β] [has_nat_cast β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) :
  semiring β :=
{ .. hf.non_assoc_semiring f zero one add mul nsmul nat_cast,
  .. hf.monoid_with_zero f zero one mul npow,
  .. hf.distrib f add mul }

/-- Pushforward a `non_unital_non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_non_assoc_semiring
  {α : Type u} [non_unital_non_assoc_semiring α]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_non_assoc_semiring β :=
{ .. hf.mul_zero_class f zero mul, .. hf.add_comm_monoid f zero add nsmul, .. hf.distrib f add mul }

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_semiring
  {α : Type u} [non_unital_semiring α]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_semiring β :=
{ .. hf.non_unital_non_assoc_semiring f zero add mul nsmul, .. hf.semigroup_with_zero f zero mul }

/-- Pushforward a `non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_assoc_semiring
  {α : Type u} [non_assoc_semiring α]
  {β : Type v} [has_zero β] [has_one β] [has_add β] [has_mul β]
  [has_smul ℕ β] [has_nat_cast β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (nat_cast : ∀ n : ℕ, f n = n) :
  non_assoc_semiring β :=
{ .. hf.add_monoid_with_one f zero one add nsmul nat_cast,
  .. hf.non_unital_non_assoc_semiring f zero add mul nsmul, .. hf.mul_one_class f one mul }

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.semiring
  {α : Type u} [semiring α]
  {β : Type v} [has_zero β] [has_one β] [has_add β] [has_mul β] [has_pow β ℕ]
  [has_smul ℕ β] [has_nat_cast β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) :
  semiring β :=
{ .. hf.non_assoc_semiring f zero one add mul nsmul nat_cast,
  .. hf.monoid_with_zero f zero one mul npow, .. hf.add_comm_monoid f zero add nsmul,
  .. hf.distrib f add mul }

end injective_surjective_maps

section has_one_has_add

variables [has_one α] [has_add α]

lemma one_add_one_eq_two : 1 + 1 = (2 : α) := rfl

end has_one_has_add

section distrib_semigroup
variables [has_add α] [semigroup α]

theorem dvd_add [left_distrib_class α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
dvd.elim h₁ (λ d hd, dvd.elim h₂ (λ e he, dvd.intro (d + e) (by simp [left_distrib, hd, he])))

end distrib_semigroup

section distrib_mul_one_class
variables [has_add α] [mul_one_class α]

lemma add_one_mul [right_distrib_class α] (a b : α) : (a + 1) * b = a * b + b :=
by rw [add_mul, one_mul]
lemma mul_add_one [left_distrib_class α] (a b : α) : a * (b + 1) = a * b + a :=
by rw [mul_add, mul_one]
lemma one_add_mul [right_distrib_class α] (a b : α) : (1 + a) * b = b + a * b :=
by rw [add_mul, one_mul]
lemma mul_one_add [left_distrib_class α] (a b : α) : a * (1 + b) = a + a * b :=
by rw [mul_add, mul_one]

theorem two_mul [right_distrib_class α] (n : α) : 2 * n = n + n :=
eq.trans (right_distrib 1 1 n) (by simp)

theorem bit0_eq_two_mul [right_distrib_class α] (n : α) : bit0 n = 2 * n :=
(two_mul _).symm

theorem mul_two [left_distrib_class α] (n : α) : n * 2 = n + n :=
(left_distrib n 1 1).trans (by simp)

end distrib_mul_one_class

section semiring
variables [semiring α]

@[to_additive] lemma mul_ite {α} [has_mul α] (P : Prop) [decidable P] (a b c : α) :
  a * (if P then b else c) = if P then a * b else a * c :=
by split_ifs; refl

@[to_additive] lemma ite_mul {α} [has_mul α] (P : Prop) [decidable P] (a b c : α) :
  (if P then a else b) * c = if P then a * c else b * c :=
by split_ifs; refl

-- We make `mul_ite` and `ite_mul` simp lemmas,
-- but not `add_ite` or `ite_add`.
-- The problem we're trying to avoid is dealing with
-- summations of the form `∑ x in s, (f x + ite P 1 0)`,
-- in which `add_ite` followed by `sum_ite` would needlessly slice up
-- the `f x` terms according to whether `P` holds at `x`.
-- There doesn't appear to be a corresponding difficulty so far with
-- `mul_ite` and `ite_mul`.
attribute [simp] mul_ite ite_mul

@[simp] lemma mul_boole {α} [mul_zero_one_class α] (P : Prop) [decidable P] (a : α) :
  a * (if P then 1 else 0) = if P then a else 0 :=
by simp

@[simp] lemma boole_mul {α} [mul_zero_one_class α] (P : Prop) [decidable P] (a : α) :
  (if P then 1 else 0) * a = if P then a else 0 :=
by simp

lemma ite_mul_zero_left {α : Type*} [mul_zero_class α] (P : Prop) [decidable P] (a b : α) :
  ite P (a * b) 0 = ite P a 0 * b :=
by { by_cases h : P; simp [h], }

lemma ite_mul_zero_right {α : Type*} [mul_zero_class α] (P : Prop) [decidable P] (a b : α) :
  ite P (a * b) 0 = a * ite P b 0 :=
by { by_cases h : P; simp [h], }

lemma ite_and_mul_zero {α : Type*} [mul_zero_class α]
  (P Q : Prop) [decidable P] [decidable Q] (a b : α) :
  ite (P ∧ Q) (a * b) 0 = ite P a 0 * ite Q b 0 :=
by simp only [←ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm]

end semiring

namespace add_hom

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps { fully_applied := ff}] def mul_left {R : Type*} [distrib R] (r : R) : add_hom R R :=
⟨(*) r, mul_add r⟩

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps { fully_applied := ff}] def mul_right {R : Type*} [distrib R] (r : R) : add_hom R R :=
⟨λ a, a * r, λ _ _, add_mul _ _ r⟩

end add_hom

section add_hom_class

variables {F : Type*} [non_assoc_semiring α] [non_assoc_semiring β] [add_hom_class F α β]

/-- Additive homomorphisms preserve `bit0`. -/
@[simp] lemma map_bit0 (f : F) (a : α) : (f (bit0 a) : β) = bit0 (f a) :=
map_add _ _ _

end add_hom_class

namespace add_monoid_hom

/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_left {R : Type*} [non_unital_non_assoc_semiring R] (r : R) : R →+ R :=
{ to_fun := (*) r,
  map_zero' := mul_zero r,
  map_add' := mul_add r }

@[simp] lemma coe_mul_left {R : Type*} [non_unital_non_assoc_semiring R] (r : R) :
  ⇑(mul_left r) = (*) r := rfl

/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_right {R : Type*} [non_unital_non_assoc_semiring R] (r : R) : R →+ R :=
{ to_fun := λ a, a * r,
  map_zero' := zero_mul r,
  map_add' := λ _ _, add_mul _ _ r }

@[simp] lemma coe_mul_right {R : Type*} [non_unital_non_assoc_semiring R] (r : R) :
  ⇑(mul_right r) = (* r) := rfl

lemma mul_right_apply {R : Type*} [non_unital_non_assoc_semiring R] (a r : R) :
  mul_right r a = a * r := rfl

end add_monoid_hom

@[simp] theorem two_dvd_bit0 [semiring α] {a : α} : 2 ∣ bit0 a := ⟨a, bit0_eq_two_mul _⟩

/-- A non-unital commutative semiring is a `non_unital_semiring` with commutative multiplication.
In other words, it is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), commutative semigroup (`comm_semigroup`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). -/
@[protect_proj, ancestor non_unital_semiring comm_semigroup]
class non_unital_comm_semiring (α : Type u) extends non_unital_semiring α, comm_semigroup α

section non_unital_comm_semiring
variables [non_unital_comm_semiring α] [non_unital_comm_semiring β] {a b c : α}

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_comm_semiring [has_zero γ] [has_add γ] [has_mul γ]
  [has_smul ℕ γ] (f : γ → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_comm_semiring γ :=
{ .. hf.non_unital_semiring f zero add mul nsmul, .. hf.comm_semigroup f mul }

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_comm_semiring [has_zero γ] [has_add γ] [has_mul γ]
  [has_smul ℕ γ] (f : α → γ) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) :
  non_unital_comm_semiring γ :=
{ .. hf.non_unital_semiring f zero add mul nsmul, .. hf.comm_semigroup f mul }

lemma has_dvd.dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) :
  d ∣ (a * x + b * y) :=
dvd_add (hdx.mul_left a) (hdy.mul_left b)

end non_unital_comm_semiring

/-- A commutative semiring is a `semiring` with commutative multiplication. In other words, it is a
type with the following structures: additive commutative monoid (`add_comm_monoid`), multiplicative
commutative monoid (`comm_monoid`), distributive laws (`distrib`), and multiplication by zero law
(`mul_zero_class`). -/
@[protect_proj, ancestor semiring comm_monoid]
class comm_semiring (α : Type u) extends semiring α, comm_monoid α

@[priority 100] -- see Note [lower instance priority]
instance comm_semiring.to_non_unital_comm_semiring [comm_semiring α] : non_unital_comm_semiring α :=
{ .. comm_semiring.to_comm_monoid α, .. comm_semiring.to_semiring α }

@[priority 100] -- see Note [lower instance priority]
instance comm_semiring.to_comm_monoid_with_zero [comm_semiring α] : comm_monoid_with_zero α :=
{ .. comm_semiring.to_comm_monoid α, .. comm_semiring.to_semiring α }

section comm_semiring
variables [comm_semiring α] [comm_semiring β] {a b c : α}

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.comm_semiring
  [has_zero γ] [has_one γ] [has_add γ] [has_mul γ] [has_smul ℕ γ] [has_nat_cast γ]
  [has_pow γ ℕ] (f : γ → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) :
  comm_semiring γ :=
{ .. hf.semiring f zero one add mul nsmul npow nat_cast, .. hf.comm_semigroup f mul }

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.comm_semiring
  [has_zero γ] [has_one γ] [has_add γ] [has_mul γ] [has_smul ℕ γ] [has_nat_cast γ]
  [has_pow γ ℕ] (f : α → γ) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) :
  comm_semiring γ :=
{ .. hf.semiring f zero one add mul nsmul npow nat_cast, .. hf.comm_semigroup f mul }

lemma add_mul_self_eq (a b : α) : (a + b) * (a + b) = a*a + 2*a*b + b*b :=
by simp only [two_mul, add_mul, mul_add, add_assoc, mul_comm b]

end comm_semiring

section has_distrib_neg

/-- Typeclass for a negation operator that distributes across multiplication.

This is useful for dealing with submonoids of a ring that contain `-1` without having to duplicate
lemmas. -/
class has_distrib_neg (α : Type*) [has_mul α] extends has_involutive_neg α :=
(neg_mul : ∀ x y : α, -x * y = -(x * y))
(mul_neg : ∀ x y : α, x * -y = -(x * y))

section has_mul
variables [has_mul α] [has_distrib_neg α]

@[simp] lemma neg_mul (a b : α) : - a * b = - (a * b) :=
has_distrib_neg.neg_mul _ _

@[simp] lemma mul_neg (a b : α) : a * - b = - (a * b) :=
has_distrib_neg.mul_neg _ _

lemma neg_mul_neg (a b : α) : -a * -b = a * b :=
by simp

lemma neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b :=
(neg_mul _ _).symm

lemma neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
(mul_neg _ _).symm

lemma neg_mul_comm (a b : α) : -a * b = a * -b :=
by simp

/-- A type endowed with `-` and `*` has distributive negation, if it admits an injective map that
preserves `-` and `*` to a type which has distributive negation. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.has_distrib_neg [has_neg β] [has_mul β] (f : β → α)
  (hf : injective f) (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) :
  has_distrib_neg β :=
{ neg_mul := λ x y, hf $ by erw [neg, mul, neg, neg_mul, mul],
  mul_neg := λ x y, hf $ by erw [neg, mul, neg, mul_neg, mul],
  ..hf.has_involutive_neg _ neg, ..‹has_mul β› }

/-- A type endowed with `-` and `*` has distributive negation, if it admits a surjective map that
preserves `-` and `*` from a type which has distributive negation. -/
@[reducible] -- See note [reducible non-instances]
protected def function.surjective.has_distrib_neg [has_neg β] [has_mul β] (f : α → β)
  (hf : surjective f) (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) :
  has_distrib_neg β :=
{ neg_mul := hf.forall₂.2 $ λ x y, by { erw [←neg, ← mul, neg_mul, neg, mul], refl },
  mul_neg := hf.forall₂.2 $ λ x y, by { erw [←neg, ← mul, mul_neg, neg, mul], refl },
  ..hf.has_involutive_neg _ neg, ..‹has_mul β› }

namespace add_opposite

instance : has_distrib_neg αᵃᵒᵖ := unop_injective.has_distrib_neg _ unop_neg unop_mul

end add_opposite

open mul_opposite

instance : has_distrib_neg αᵐᵒᵖ :=
{ neg_mul := λ _ _, unop_injective $ mul_neg _ _,
  mul_neg := λ _ _, unop_injective $ neg_mul _ _,
  ..mul_opposite.has_involutive_neg _ }

end has_mul

section mul_one_class
variables [mul_one_class α] [has_distrib_neg α]

theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a :=
by simp

/-- An element of a ring multiplied by the additive inverse of one is the element's additive
  inverse. -/
lemma mul_neg_one (a : α) : a * -1 = -a := by simp

/-- The additive inverse of one multiplied by an element of a ring is the element's additive
  inverse. -/
lemma neg_one_mul (a : α) : -1 * a = -a := by simp

end mul_one_class

section mul_zero_class
variables [mul_zero_class α] [has_distrib_neg α]

/-- Prefer `neg_zero` if `subtraction_monoid` is available. -/
@[simp] lemma neg_zero' : (-0 : α) = 0 :=
by rw [←zero_mul (0 : α), ←neg_mul, mul_zero, mul_zero]

end mul_zero_class

section semigroup

variables [semigroup α] [has_distrib_neg α] {a b c : α}

theorem dvd_neg_of_dvd (h : a ∣ b) : (a ∣ -b) :=
let ⟨c, hc⟩ := h in ⟨-c, by simp [hc]⟩

theorem dvd_of_dvd_neg (h : a ∣ -b) : (a ∣ b) :=
let t := dvd_neg_of_dvd h in by rwa neg_neg at t

/-- An element a of a semigroup with a distributive negation divides the negation of an element b
iff a divides b. -/
@[simp] lemma dvd_neg (a b : α) : (a ∣ -b) ↔ (a ∣ b) :=
⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

theorem neg_dvd_of_dvd (h : a ∣ b) : -a ∣ b :=
let ⟨c, hc⟩ := h in ⟨-c, by simp [hc]⟩

theorem dvd_of_neg_dvd (h : -a ∣ b) : a ∣ b :=
let t := neg_dvd_of_dvd h in by rwa neg_neg at t

/-- The negation of an element a of a semigroup with a distributive negation divides
another element b iff a divides b. -/
@[simp] lemma neg_dvd (a b : α) : (-a ∣ b) ↔ (a ∣ b) :=
⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩

end semigroup

section group
variables [group α] [has_distrib_neg α]

@[simp] lemma inv_neg' (a : α) : (- a)⁻¹ = - a⁻¹ :=
by rw [eq_comm, eq_inv_iff_mul_eq_one, neg_mul, mul_neg,neg_neg, mul_left_inv]

end group

end has_distrib_neg

/-!
### Rings
-/

/-- A not-necessarily-unital, not-necessarily-associative ring. -/
@[protect_proj, ancestor add_comm_group non_unital_non_assoc_semiring]
class non_unital_non_assoc_ring (α : Type u) extends
  add_comm_group α, non_unital_non_assoc_semiring α

section non_unital_non_assoc_ring
variables [non_unital_non_assoc_ring α]


/-- Pullback a `non_unital_non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_non_assoc_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β] [has_smul ℕ β] [has_smul ℤ β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_non_assoc_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul zsmul, ..hf.mul_zero_class f zero mul,
  .. hf.distrib f add mul }

/-- Pushforward a `non_unital_non_assoc_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_non_assoc_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β] [has_smul ℕ β] [has_smul ℤ β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_non_assoc_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul zsmul, .. hf.mul_zero_class f zero mul,
  .. hf.distrib f add mul }

@[priority 100]
instance non_unital_non_assoc_ring.to_has_distrib_neg : has_distrib_neg α :=
{ neg := has_neg.neg,
  neg_neg := neg_neg,
  neg_mul := λ a b, eq_neg_of_add_eq_zero_left $ by rw [←right_distrib, add_left_neg, zero_mul],
  mul_neg := λ a b, eq_neg_of_add_eq_zero_left $ by rw [←left_distrib, add_left_neg, mul_zero] }

lemma mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c :=
by simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)

alias mul_sub_left_distrib ← mul_sub

lemma mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c :=
by simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c

alias mul_sub_right_distrib ← sub_mul

variables {a b c d e : α}

/-- An iff statement following from right distributivity in rings and the definition
  of subtraction. -/
theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
calc
  a * e + c = b * e + d ↔ a * e + c = d + b * e : by simp [add_comm]
    ... ↔ a * e + c - b * e = d : iff.intro (λ h, begin rw h, simp end) (λ h,
                                                  begin rw ← h, simp end)
    ... ↔ (a - b) * e + c = d   : begin simp [sub_mul, sub_add_eq_add_sub] end

/-- A simplification of one side of an equation exploiting right distributivity in rings
  and the definition of subtraction. -/
theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d :=
assume h,
calc
  (a - b) * e + c = (a * e + c) - b * e : begin simp [sub_mul, sub_add_eq_add_sub] end
              ... = d                   : begin rw h, simp [@add_sub_cancel α] end

end non_unital_non_assoc_ring

/-- An associative but not-necessarily unital ring. -/
@[protect_proj, ancestor non_unital_non_assoc_ring non_unital_semiring]
class non_unital_ring (α : Type*) extends
  non_unital_non_assoc_ring α, non_unital_semiring α

section non_unital_ring
variables [non_unital_ring α]

/-- Pullback a `non_unital_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β] [has_smul ℕ β] [has_smul ℤ β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul gsmul, ..hf.mul_zero_class f zero mul,
  .. hf.distrib f add mul, .. hf.semigroup f mul }

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β] [has_smul ℕ β] [has_smul ℤ β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul gsmul, .. hf.mul_zero_class f zero mul,
  .. hf.distrib f add mul, .. hf.semigroup f mul }

end non_unital_ring

/-- A unital but not-necessarily-associative ring. -/
@[protect_proj, ancestor non_unital_non_assoc_ring non_assoc_semiring]
class non_assoc_ring (α : Type*) extends
  non_unital_non_assoc_ring α, non_assoc_semiring α, add_group_with_one α

section non_assoc_ring
variables [non_assoc_ring α]

/-- Pullback a `non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_assoc_ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_nat_cast β] [has_int_cast β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  non_assoc_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul gsmul,
  .. hf.add_group_with_one f zero one add neg sub nsmul gsmul nat_cast int_cast,
  .. hf.mul_zero_class f zero mul, .. hf.distrib f add mul,
  .. hf.mul_one_class f one mul }

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_assoc_ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_nat_cast β] [has_int_cast β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  non_assoc_ring β :=
{ .. hf.add_comm_group f zero add neg sub nsmul gsmul, .. hf.mul_zero_class f zero mul,
  .. hf.add_group_with_one f zero one add neg sub nsmul gsmul nat_cast int_cast,
  .. hf.distrib f add mul, .. hf.mul_one_class f one mul }

lemma sub_one_mul (a b : α) : (a - 1) * b = a * b - b :=
by rw [sub_mul, one_mul]
lemma mul_sub_one (a b : α) : a * (b - 1) = a * b - a :=
by rw [mul_sub, mul_one]
lemma one_sub_mul (a b : α) : (1 - a) * b = b - a * b :=
by rw [sub_mul, one_mul]
lemma mul_one_sub (a b : α) : a * (1 - b) = a - a * b :=
by rw [mul_sub, mul_one]

end non_assoc_ring

/-- A ring is a type with the following structures: additive commutative group (`add_comm_group`),
multiplicative monoid (`monoid`), and distributive laws (`distrib`).  Equivalently, a ring is a
`semiring` with a negation operation making it an additive group.  -/
@[protect_proj, ancestor add_comm_group monoid distrib]
class ring (α : Type u) extends add_comm_group_with_one α, monoid α, distrib α

section ring
variables [ring α] {a b c d e : α}

/- A (unital, associative) ring is a not-necessarily-unital ring -/
@[priority 100] -- see Note [lower instance priority]
instance ring.to_non_unital_ring :
  non_unital_ring α :=
{ zero_mul := λ a, add_left_cancel $ show 0 * a + 0 * a = 0 * a + 0,
    by rw [← add_mul, zero_add, add_zero],
  mul_zero := λ a, add_left_cancel $ show a * 0 + a * 0 = a * 0 + 0,
    by rw [← mul_add, add_zero, add_zero],
  ..‹ring α› }

/- A (unital, associative) ring is a not-necessarily-associative ring -/
@[priority 100] -- see Note [lower instance priority]
instance ring.to_non_assoc_ring :
  non_assoc_ring α :=
{ zero_mul := λ a, add_left_cancel $ show 0 * a + 0 * a = 0 * a + 0,
    by rw [← add_mul, zero_add, add_zero],
  mul_zero := λ a, add_left_cancel $ show a * 0 + a * 0 = a * 0 + 0,
    by rw [← mul_add, add_zero, add_zero],
  ..‹ring α› }

/- The instance from `ring` to `semiring` happens often in linear algebra, for which all the basic
definitions are given in terms of semirings, but many applications use rings or fields. We increase
a little bit its priority above 100 to try it quickly, but remaining below the default 1000 so that
more specific instances are tried first. -/
@[priority 200]
instance ring.to_semiring : semiring α :=
{ ..‹ring α›, .. ring.to_non_unital_ring }

/-- Pullback a `ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_pow β ℕ] [has_nat_cast β] [has_int_cast β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  ring β :=
{ .. hf.add_group_with_one f zero one add neg sub nsmul zsmul nat_cast int_cast,
  .. hf.add_comm_group f zero add neg sub nsmul zsmul,
  .. hf.monoid f one mul npow, .. hf.distrib f add mul }

/-- Pushforward a `ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_pow β ℕ] [has_nat_cast β] [has_int_cast β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  ring β :=
{ .. hf.add_group_with_one f zero one add neg sub nsmul zsmul nat_cast int_cast,
  .. hf.add_comm_group f zero add neg sub nsmul zsmul,
  .. hf.monoid f one mul npow, .. hf.distrib f add mul }

end ring

namespace units
variables [ring α] {a b : α}

/-- Each element of the group of units of a ring has an additive inverse. -/
instance : has_neg αˣ := ⟨λu, ⟨-↑u, -↑u⁻¹, by simp, by simp⟩ ⟩

/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp, norm_cast] protected theorem coe_neg (u : αˣ) : (↑-u : α) = -u := rfl

@[simp, norm_cast] protected theorem coe_neg_one : ((-1 : αˣ) : α) = -1 := rfl

instance : has_distrib_neg αˣ := units.ext.has_distrib_neg _ units.coe_neg units.coe_mul

@[field_simps] lemma neg_divp (a : α) (u : αˣ) : -(a /ₚ u) = (-a) /ₚ u :=
by simp only [divp, neg_mul]

@[field_simps] lemma divp_add_divp_same (a b : α) (u : αˣ) :
  a /ₚ u + b /ₚ u = (a + b) /ₚ u :=
by simp only [divp, add_mul]

@[field_simps] lemma divp_sub_divp_same (a b : α) (u : αˣ) :
  a /ₚ u - b /ₚ u = (a - b) /ₚ u :=
by rw [sub_eq_add_neg, sub_eq_add_neg, neg_divp, divp_add_divp_same]

@[field_simps] lemma add_divp (a b : α) (u : αˣ)  : a + b /ₚ u = (a * u + b) /ₚ u :=
by simp only [divp, add_mul, units.mul_inv_cancel_right]

@[field_simps] lemma sub_divp (a b : α) (u : αˣ) : a - b /ₚ u = (a * u - b) /ₚ u :=
by simp only [divp, sub_mul, units.mul_inv_cancel_right]

@[field_simps] lemma divp_add (a b : α) (u : αˣ) : a /ₚ u + b = (a + b * u) /ₚ u :=
by simp only [divp, add_mul, units.mul_inv_cancel_right]

@[field_simps] lemma divp_sub (a b : α) (u : αˣ) : a /ₚ u - b = (a - b * u) /ₚ u :=
begin
  simp only [divp, sub_mul, sub_right_inj],
  assoc_rw [units.mul_inv, mul_one],
end

end units

lemma is_unit.neg [ring α] {a : α} : is_unit a → is_unit (-a)
| ⟨x, hx⟩ := hx ▸ (-x).is_unit

lemma is_unit.neg_iff [ring α] (a : α) : is_unit (-a) ↔ is_unit a :=
⟨λ h, neg_neg a ▸ h.neg, is_unit.neg⟩

lemma is_unit.sub_iff [ring α] {x y : α} :
  is_unit (x - y) ↔ is_unit (y - x) :=
(is_unit.neg_iff _).symm.trans $ neg_sub x y ▸ iff.rfl

namespace ring_hom

end ring_hom

/-- A non-unital commutative ring is a `non_unital_ring` with commutative multiplication. -/
@[protect_proj, ancestor non_unital_ring comm_semigroup]
class non_unital_comm_ring (α : Type u) extends non_unital_ring α, comm_semigroup α

@[priority 100] -- see Note [lower instance priority]
instance non_unital_comm_ring.to_non_unital_comm_semiring [s : non_unital_comm_ring α] :
  non_unital_comm_semiring α :=
{ ..s }

/-- A commutative ring is a `ring` with commutative multiplication. -/
@[protect_proj, ancestor ring comm_semigroup]
class comm_ring (α : Type u) extends ring α, comm_monoid α

@[priority 100] -- see Note [lower instance priority]
instance comm_ring.to_comm_semiring [s : comm_ring α] : comm_semiring α :=
{ mul_zero := mul_zero, zero_mul := zero_mul, ..s }

@[priority 100] -- see Note [lower instance priority]
instance comm_ring.to_non_unital_comm_ring [s : comm_ring α] : non_unital_comm_ring α :=
{ mul_zero := mul_zero, zero_mul := zero_mul, ..s }

section non_unital_ring
variables [non_unital_ring α] {a b c : α}

theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c :=
by { rw sub_eq_add_neg, exact dvd_add h₁ (dvd_neg_of_dvd h₂) }

theorem dvd_add_iff_left (h : a ∣ c) : a ∣ b ↔ a ∣ b + c :=
⟨λh₂, dvd_add h₂ h, λH, by have t := dvd_sub H h; rwa add_sub_cancel at t⟩

theorem dvd_add_iff_right (h : a ∣ b) : a ∣ c ↔ a ∣ b + c :=
by rw add_comm; exact dvd_add_iff_left h

/-- If an element a divides another element c in a commutative ring, a divides the sum of another
  element b with c iff a divides b. -/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
(dvd_add_iff_left h).symm

/-- If an element a divides another element b in a commutative ring, a divides the sum of b and
  another element c iff a divides c. -/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c :=
(dvd_add_iff_right h).symm

lemma dvd_iff_dvd_of_dvd_sub {a b c : α} (h : a ∣ (b - c)) : (a ∣ b ↔ a ∣ c) :=
begin
  split,
  { intro h',
    convert dvd_sub h' h,
    exact eq.symm (sub_sub_self b c) },
  { intro h',
    convert dvd_add h h',
    exact eq_add_of_sub_eq rfl }
end

end non_unital_ring

section ring
variables [ring α] {a b c : α}

theorem two_dvd_bit1 : 2 ∣ bit1 a ↔ (2 : α) ∣ 1 := (dvd_add_iff_right (@two_dvd_bit0 _ _ a)).symm

/-- An element a divides the sum a + b if and only if a divides b.-/
@[simp] lemma dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
dvd_add_right (dvd_refl a)

/-- An element a divides the sum b + a if and only if a divides b.-/
@[simp] lemma dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
dvd_add_left (dvd_refl a)

end ring

section non_unital_comm_ring
variables [non_unital_comm_ring α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_comm_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_comm_ring β :=
{ .. hf.non_unital_ring f zero add mul neg sub nsmul zsmul, .. hf.comm_semigroup f mul }

/-- Pushforward a `non_unital_comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_comm_ring
  [has_zero β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x) :
  non_unital_comm_ring β :=
{ .. hf.non_unital_ring f zero add mul neg sub nsmul zsmul, .. hf.comm_semigroup f mul }

local attribute [simp] add_assoc add_comm add_left_comm mul_comm

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
lemma Vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
  ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c :=
begin
  have : c = x * (b - x) := (eq_neg_of_add_eq_zero_right h).trans (by simp [mul_sub, mul_comm]),
  refine ⟨b - x, _, by simp, by rw this⟩,
  rw [this, sub_add, ← sub_mul, sub_self]
end

lemma dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) :
  k ∣ a * x - b * y :=
begin
  convert dvd_add (hxy.mul_left a) (hab.mul_right y),
  rw [mul_sub_left_distrib, mul_sub_right_distrib],
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left],
end

end non_unital_comm_ring

section comm_ring
variables [comm_ring α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.comm_ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_pow β ℕ] [has_nat_cast β] [has_int_cast β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  comm_ring β :=
{ .. hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast,
  .. hf.comm_semigroup f mul }

/-- Pushforward a `comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.comm_ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  [has_smul ℕ β] [has_smul ℤ β] [has_pow β ℕ] [has_nat_cast β] [has_int_cast β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
  comm_ring β :=
{ .. hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast,
  .. hf.comm_semigroup f mul }

end comm_ring

lemma succ_ne_self [non_assoc_ring α] [nontrivial α] (a : α) : a + 1 ≠ a :=
λ h, one_ne_zero ((add_right_inj a).mp (by simp [h]))

lemma pred_ne_self [non_assoc_ring α] [nontrivial α] (a : α) : a - 1 ≠ a :=
λ h, one_ne_zero (neg_injective ((add_right_inj a).mp (by simpa [sub_eq_add_neg] using h)))

/-- Left `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
lemma is_left_regular_of_non_zero_divisor [non_unital_non_assoc_ring α] (k : α)
  (h : ∀ (x : α), k * x = 0 → x = 0) : is_left_regular k :=
begin
  refine λ x y (h' : k * x = k * y), sub_eq_zero.mp (h _ _),
  rw [mul_sub, sub_eq_zero, h']
end

/-- Right `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
lemma is_right_regular_of_non_zero_divisor [non_unital_non_assoc_ring α] (k : α)
  (h : ∀ (x : α), x * k = 0 → x = 0) : is_right_regular k :=
begin
  refine λ x y (h' : x * k = y * k), sub_eq_zero.mp (h _ _),
  rw [sub_mul, sub_eq_zero, h']
end

lemma is_regular_of_ne_zero' [non_unital_non_assoc_ring α] [no_zero_divisors α] {k : α}
  (hk : k ≠ 0) : is_regular k :=
⟨is_left_regular_of_non_zero_divisor k
  (λ x h, (no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk),
 is_right_regular_of_non_zero_divisor k
  (λ x h, (no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk)⟩

lemma is_regular_iff_ne_zero' [nontrivial α] [non_unital_non_assoc_ring α] [no_zero_divisors α]
  {k : α} : is_regular k ↔ k ≠ 0 :=
⟨λ h, by { rintro rfl, exact not_not.mpr h.left not_is_left_regular_zero }, is_regular_of_ne_zero'⟩

/-- A ring with no zero divisors is a `cancel_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def no_zero_divisors.to_cancel_monoid_with_zero [ring α] [no_zero_divisors α] :
  cancel_monoid_with_zero α :=
{ mul_left_cancel_of_ne_zero := λ a b c ha,
    @is_regular.left _ _ _ (is_regular_of_ne_zero' ha) _ _,
  mul_right_cancel_of_ne_zero := λ a b c hb,
    @is_regular.right _ _ _ (is_regular_of_ne_zero' hb) _ _,
  .. (by apply_instance : monoid_with_zero α) }

/-- A commutative ring with no zero divisors is a `cancel_comm_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def no_zero_divisors.to_cancel_comm_monoid_with_zero [comm_ring α] [no_zero_divisors α] :
  cancel_comm_monoid_with_zero α :=
{ .. no_zero_divisors.to_cancel_monoid_with_zero,
  .. (by apply_instance : comm_monoid_with_zero α) }

/-- A domain is a nontrivial ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`.

  This is implemented as a mixin for `ring α`.
  To obtain an integral domain use `[comm_ring α] [is_domain α]`. -/
@[protect_proj] class is_domain (α : Type u) [ring α]
  extends no_zero_divisors α, nontrivial α : Prop

section is_domain

@[priority 100] -- see Note [lower instance priority]
instance is_domain.to_cancel_monoid_with_zero [ring α] [is_domain α] : cancel_monoid_with_zero α :=
no_zero_divisors.to_cancel_monoid_with_zero

variables [comm_ring α] [is_domain α]

@[priority 100] -- see Note [lower instance priority]
instance is_domain.to_cancel_comm_monoid_with_zero : cancel_comm_monoid_with_zero α :=
no_zero_divisors.to_cancel_comm_monoid_with_zero

end is_domain

namespace semiconj_by

@[simp] lemma add_right [distrib R] {a x y x' y' : R}
  (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x + x') (y + y') :=
by simp only [semiconj_by, left_distrib, right_distrib, h.eq, h'.eq]

@[simp] lemma add_left [distrib R] {a b x y : R}
  (ha : semiconj_by a x y) (hb : semiconj_by b x y) :
  semiconj_by (a + b) x y :=
by simp only [semiconj_by, left_distrib, right_distrib, ha.eq, hb.eq]

section
variables [has_mul R] [has_distrib_neg R] {a x y : R}

lemma neg_right (h : semiconj_by a x y) : semiconj_by a (-x) (-y) :=
by simp only [semiconj_by, h.eq, neg_mul, mul_neg]

@[simp] lemma neg_right_iff : semiconj_by a (-x) (-y) ↔ semiconj_by a x y :=
⟨λ h, neg_neg x ▸ neg_neg y ▸ h.neg_right, semiconj_by.neg_right⟩

lemma neg_left (h : semiconj_by a x y) : semiconj_by (-a) x y :=
by simp only [semiconj_by, h.eq, neg_mul, mul_neg]

@[simp] lemma neg_left_iff : semiconj_by (-a) x y ↔ semiconj_by a x y :=
⟨λ h, neg_neg a ▸ h.neg_left, semiconj_by.neg_left⟩

end

section
variables [mul_one_class R] [has_distrib_neg R] {a x y : R}

@[simp] lemma neg_one_right (a : R) : semiconj_by a (-1) (-1) :=
(one_right a).neg_right

@[simp] lemma neg_one_left (x : R) : semiconj_by (-1) x x :=
(semiconj_by.one_left x).neg_left

end

section
variables [non_unital_non_assoc_ring R] {a b x y x' y' : R}

@[simp] lemma sub_right (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x - x') (y - y') :=
by simpa only [sub_eq_add_neg] using h.add_right h'.neg_right

@[simp] lemma sub_left (ha : semiconj_by a x y) (hb : semiconj_by b x y) :
  semiconj_by (a - b) x y :=
by simpa only [sub_eq_add_neg] using ha.add_left hb.neg_left

end

end semiconj_by

namespace commute

@[simp] theorem add_right [distrib R] {a b c : R} :
  commute a b → commute a c → commute a (b + c) :=
semiconj_by.add_right

@[simp] theorem add_left [distrib R] {a b c : R} :
  commute a c → commute b c → commute (a + b) c :=
semiconj_by.add_left

lemma bit0_right [distrib R] {x y : R} (h : commute x y) : commute x (bit0 y) :=
h.add_right h

lemma bit0_left [distrib R] {x y : R} (h : commute x y) : commute (bit0 x) y :=
h.add_left h

lemma bit1_right [non_assoc_semiring R] {x y : R} (h : commute x y) : commute x (bit1 y) :=
h.bit0_right.add_right (commute.one_right x)

lemma bit1_left [non_assoc_semiring R] {x y : R} (h : commute x y) : commute (bit1 x) y :=
h.bit0_left.add_left (commute.one_left y)

/-- Representation of a difference of two squares of commuting elements as a product. -/
lemma mul_self_sub_mul_self_eq [non_unital_non_assoc_ring R] {a b : R} (h : commute a b) :
  a * a - b * b = (a + b) * (a - b) :=
by rw [add_mul, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]

lemma mul_self_sub_mul_self_eq' [non_unital_non_assoc_ring R] {a b : R} (h : commute a b) :
  a * a - b * b = (a - b) * (a + b) :=
by rw [mul_add, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]

lemma mul_self_eq_mul_self_iff [non_unital_non_assoc_ring R] [no_zero_divisors R] {a b : R}
  (h : commute a b) : a * a = b * b ↔ a = b ∨ a = -b :=
by rw [← sub_eq_zero, h.mul_self_sub_mul_self_eq, mul_eq_zero, or_comm, sub_eq_zero,
  add_eq_zero_iff_eq_neg]

section
variables [has_mul R] [has_distrib_neg R] {a b : R}

theorem neg_right : commute a b → commute a (- b) := semiconj_by.neg_right
@[simp] theorem neg_right_iff : commute a (-b) ↔ commute a b := semiconj_by.neg_right_iff

theorem neg_left : commute a b → commute (- a) b := semiconj_by.neg_left
@[simp] theorem neg_left_iff : commute (-a) b ↔ commute a b := semiconj_by.neg_left_iff

end

section
variables [mul_one_class R] [has_distrib_neg R] {a : R}

@[simp] theorem neg_one_right (a : R) : commute a (-1) := semiconj_by.neg_one_right a
@[simp] theorem neg_one_left (a : R): commute (-1) a := semiconj_by.neg_one_left a

end

section
variables [non_unital_non_assoc_ring R] {a b c : R}

@[simp] theorem sub_right : commute a b → commute a c → commute a (b - c) := semiconj_by.sub_right
@[simp] theorem sub_left : commute a c → commute b c → commute (a - b) c := semiconj_by.sub_left

end

end commute

/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self [comm_ring R] (a b : R) : a * a - b * b = (a + b) * (a - b) :=
(commute.all a b).mul_self_sub_mul_self_eq

lemma mul_self_sub_one [non_assoc_ring R] (a : R) : a * a - 1 = (a + 1) * (a - 1) :=
by rw [←(commute.one_right a).mul_self_sub_mul_self_eq, mul_one]

lemma mul_self_eq_mul_self_iff [comm_ring R] [no_zero_divisors R] {a b : R} :
  a * a = b * b ↔ a = b ∨ a = -b :=
(commute.all a b).mul_self_eq_mul_self_iff

lemma mul_self_eq_one_iff [non_assoc_ring R] [no_zero_divisors R] {a : R} :
  a * a = 1 ↔ a = 1 ∨ a = -1 :=
by rw [←(commute.one_right a).mul_self_eq_mul_self_iff, mul_one]

namespace units

@[field_simps] lemma divp_add_divp [comm_ring α] (a b : α) (u₁ u₂ : αˣ) :
a /ₚ u₁ + b /ₚ u₂ = (a * u₂ + u₁ * b) /ₚ (u₁ * u₂) :=
begin
  simp only [divp, add_mul, mul_inv_rev, coe_mul],
  rw [mul_comm (↑u₁ * b), mul_comm b],
  assoc_rw [mul_inv, mul_inv, mul_one, mul_one],
end

@[field_simps] lemma divp_sub_divp [comm_ring α] (a b : α) (u₁ u₂ : αˣ) :
  (a /ₚ u₁) - (b /ₚ u₂) = ((a * u₂) - (u₁ * b)) /ₚ (u₁ * u₂) :=
by simp_rw [sub_eq_add_neg, neg_divp, divp_add_divp, mul_neg]

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
lemma inv_eq_self_iff [ring R] [no_zero_divisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 :=
begin
  rw inv_eq_iff_mul_eq_one,
  simp only [ext_iff],
  push_cast,
  exact mul_self_eq_one_iff
end

end units
