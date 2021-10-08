/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.apply_fun
import algebra.order.ring
import algebra.opposites
import algebra.big_operators.basic
import data.equiv.ring_aut
import data.equiv.mul_add_aut

/-!
# Star monoids and star rings

We introduce the basic algebraic notions of star monoids, and star rings.
Star algebras are introduced in `algebra.algebra.star`.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type) [ring R] [star_ring R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/


universes u v

open opposite

/--
Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class has_star (R : Type u) :=
(star : R → R)

variables {R : Type u}

/--
A star operation (e.g. complex conjugate).
-/
def star [has_star R] (r : R) : R := has_star.star r

/-- The opposite type carries the same star operation. -/
instance [has_star R] : has_star (Rᵒᵖ) :=
{ star := λ r, op (star (r.unop)) }

@[simp] lemma unop_star [has_star R] (r : Rᵒᵖ) : unop (star r) = star (unop r) := rfl
@[simp] lemma op_star [has_star R] (r : R) : op (star r) = star (op r) := rfl

/--
Typeclass for a star operation with is involutive.
-/
class has_involutive_star (R : Type u) extends has_star R :=
(star_involutive : function.involutive star)

export has_involutive_star (star_involutive)

@[simp] lemma star_star [has_involutive_star R] (r : R) : star (star r) = r :=
star_involutive _

lemma star_injective [has_involutive_star R] : function.injective (star : R → R) :=
star_involutive.injective

instance [has_involutive_star R] : has_involutive_star (Rᵒᵖ) :=
{ star_involutive := λ r, unop_injective (star_star r.unop) }

/--
A `*`-monoid is a monoid `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class star_monoid (R : Type u) [monoid R] extends has_involutive_star R :=
(star_mul : ∀ r s : R, star (r * s) = star s * star r)

@[simp] lemma star_mul [monoid R] [star_monoid R] (r s : R) : star (r * s) = star s * star r :=
star_monoid.star_mul r s

/-- `star` as an `mul_equiv` from `R` to `Rᵒᵖ` -/
@[simps apply]
def star_mul_equiv [monoid R] [star_monoid R] : R ≃* Rᵒᵖ :=
{ to_fun := λ x, opposite.op (star x),
  map_mul' := λ x y, (star_mul x y).symm ▸ (opposite.op_mul _ _),
  ..(has_involutive_star.star_involutive.to_equiv star).trans opposite.equiv_to_opposite}

/-- `star` as a `mul_aut` for commutative `R`. -/
@[simps apply]
def star_mul_aut [comm_monoid R] [star_monoid R] : mul_aut R :=
{ to_fun := star,
  map_mul' := λ x y, (star_mul x y).trans (mul_comm _ _),
  ..(has_involutive_star.star_involutive.to_equiv star) }

variables (R)

@[simp] lemma star_one [monoid R] [star_monoid R] : star (1 : R) = 1 :=
begin
  have := congr_arg opposite.unop (star_mul_equiv : R ≃* Rᵒᵖ).map_one,
  rwa [star_mul_equiv_apply, opposite.unop_op, opposite.unop_one] at this,
end

variables {R}

instance [monoid R] [star_monoid R] : star_monoid (Rᵒᵖ) :=
{ star_mul := λ x y, unop_injective (star_mul y.unop x.unop) }

/--
Any commutative monoid admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def star_monoid_of_comm {R : Type*} [comm_monoid R] : star_monoid R :=
{ star := id,
  star_involutive := λ x, rfl,
  star_mul := mul_comm }

section
local attribute [instance] star_monoid_of_comm

@[simp] lemma star_id_of_comm {R : Type*} [comm_semiring R] {x : R} : star x = x := rfl

end

/--
A `*`-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a `*`-monoid
(i.e. `star (r * s) = star s * star r`).
-/
class star_ring (R : Type u) [semiring R] extends star_monoid R :=
(star_add : ∀ r s : R, star (r + s) = star r + star s)

@[simp] lemma star_add [semiring R] [star_ring R] (r s : R) : star (r + s) = star r + star s :=
star_ring.star_add r s

/-- `star` as an `add_equiv` -/
@[simps apply]
def star_add_equiv [semiring R] [star_ring R] : R ≃+ R :=
{ to_fun := star,
  map_add' := star_add,
  ..(has_involutive_star.star_involutive.to_equiv star)}

variables (R)

@[simp] lemma star_zero [semiring R] [star_ring R] : star (0 : R) = 0 :=
(star_add_equiv : R ≃+ R).map_zero

variables {R}

instance [semiring R] [star_ring R] : star_ring (Rᵒᵖ) :=
{ star_add := λ x y, unop_injective (star_add x.unop y.unop) }

/-- `star` as an `ring_equiv` from `R` to `Rᵒᵖ` -/
@[simps apply]
def star_ring_equiv [semiring R] [star_ring R] : R ≃+* Rᵒᵖ :=
{ to_fun := λ x, opposite.op (star x),
  ..star_add_equiv.trans (opposite.op_add_equiv : R ≃+ Rᵒᵖ),
  ..star_mul_equiv}

/-- `star` as a `ring_aut` for commutative `R`. -/
--@[simps apply]
def star_ring_aut [comm_semiring R] [star_ring R] : ring_aut R :=
{ to_fun := star,
  ..star_add_equiv,
  ..star_mul_aut }

lemma star_ring_aut_apply [comm_semiring R] [star_ring R] {x : R} :
  star_ring_aut x = star x := rfl

@[simp] lemma star_ring_aut_self_apply [comm_semiring R] [star_ring R] {x : R} :
  star_ring_aut (star_ring_aut x) = x := star_star x

section
open_locale big_operators

@[simp] lemma star_sum [semiring R] [star_ring R] {α : Type*}
  (s : finset α) (f : α → R):
  star (∑ x in s, f x) = ∑ x in s, star (f x) :=
(star_add_equiv : R ≃+ R).map_sum _ _

end

@[simp] lemma star_neg [ring R] [star_ring R] (r : R) : star (-r) = - star r :=
(star_add_equiv : R ≃+ R).map_neg _

@[simp] lemma star_sub [ring R] [star_ring R] (r s : R) : star (r - s) = star r - star s :=
(star_add_equiv : R ≃+ R).map_sub _ _

@[simp] lemma star_bit0 [ring R] [star_ring R] (r : R) : star (bit0 r) = bit0 (star r) :=
by simp [bit0]

@[simp] lemma star_bit1 [ring R] [star_ring R] (r : R) : star (bit1 r) = bit1 (star r) :=
by simp [bit1]

/--
Any commutative semiring admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def star_ring_of_comm {R : Type*} [comm_semiring R] : star_ring R :=
{ star := id,
  star_add := λ x y, rfl,
  ..star_monoid_of_comm }

/--
An ordered `*`-ring is a ring which is both an ordered ring and a `*`-ring,
and `0 ≤ star r * r` for every `r`.

(In a Banach algebra, the natural ordering is given by the positive cone
which is the closure of the sums of elements `star r * r`.
This ordering makes the Banach algebra an ordered `*`-ring.)
-/
class star_ordered_ring (R : Type u) [ordered_semiring R] extends star_ring R :=
(star_mul_self_nonneg : ∀ r : R, 0 ≤ star r * r)

lemma star_mul_self_nonneg [ordered_semiring R] [star_ordered_ring R] {r : R} : 0 ≤ star r * r :=
star_ordered_ring.star_mul_self_nonneg r

localized "notation `conj` := star_ring_aut" in complex_conjugate
