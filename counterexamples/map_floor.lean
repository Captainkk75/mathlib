/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.hom.ring

/-!
# The floor isn't preserved under ordered ring homomorphisms


-/

def weird := ℕ ⊕ ℕ

namespace weird

open nat sum

def to_nat : ℕ ⊕ ℕ ↪ ℕ := ⟨sum.elim bit0 bit1, λ a b, by cases a; cases b; simp⟩

instance : linear_order weird := linear_order.lift' to_nat to_nat.injective

instance : has_add weird :=
⟨λ a b, match a, b with
  | inl a, inl b := inl (a + b)
  | inl a, inr b := inr (a + b)
  | inr a, inl b := inr (a + b)
  | inr a, inr b := inr (a + b)
  end⟩

@[simp] lemma inl_add_inl (a b : ℕ) : (inl a + inl b : weird) = inl (a + b) := rfl
@[simp] lemma inl_add_inr (a b : ℕ) : (inl a + inr b : weird) = inr (a + b) := rfl
@[simp] lemma inr_add_inl (a b : ℕ) : (inr a + inl b : weird) = inr (a + b) := rfl
@[simp] lemma inr_add_inr (a b : ℕ) : (inr a + inr b : weird) = inr (a + b) := rfl

instance : has_zero weird := ⟨inl 0⟩
instance : has_one weird := ⟨inl 1⟩

@[simp] lemma zero_def : (0 : weird) = inl 0 := rfl
@[simp] lemma one_def : (1 : weird) = inl 1 := rfl

instance : has_mul weird :=
⟨λ a b, match a, b with
  | inl a, inl b := inl (a * b)
  | inl a, inr b := match a with
    | 0 := 0
    | succ a := inr (a * b + a + b)
    end
  | inr a, inl b := match b with
    | 0 := 0
    | succ b := inr (a * b + a + b)
    end
  | inr a, inr b := inr (a * b + a + b)
  end⟩

@[simp] lemma inl_mul_inl (a b : ℕ) : (inl a * inl b : weird) = inl (a * b) := rfl
@[simp] lemma zero_mul_inr (b : ℕ) : (inl 0 * inr b : weird) = 0 := rfl
@[simp] lemma inr_mul_zero (a : ℕ) : (inr a * inl 0 : weird) = 0 := rfl
@[simp] lemma inl_succ_mul_inr (a b : ℕ) : (inl a.succ * inr b : weird) = inr (a * b + a + b) := rfl
@[simp] lemma inr_mul_inl_succ (a b : ℕ) : (inr a * inl b.succ : weird) = inr (a * b + a + b) := rfl
@[simp] lemma inr_mul_inr (a b : ℕ) : (inr a * inr b : weird) = inr (a * b + a + b) := rfl

instance : semiring weird :=
{ add := (+),
  add_assoc := by rintro (a | a) (b | b) (c | c); simp [add_assoc],
  add_comm := by rintro (a | a) (b | b); simp [add_comm],
  zero := inl 0,
  zero_add := by rintro (a | a); simp,
  add_zero := by rintro (a | a); simp,
  mul := (*),
  left_distrib := by rintro ((_ | a) | a) ((_ | b) | b) ((_ | c) | c); simp [mul_add],
  right_distrib := by rintro ((_ | a) | a) ((_ | b) | b) ((_ | c) | c); simp [add_mul],
  zero_mul := by rintro (a | a); simp,
  mul_zero := by rintro (a | a); simp,
  mul_assoc := by rintro (a | a) (b | b) (c | c); simp [mul_assoc],
  one := inl 1,
  one_mul := by rintro (a | a); simp,
  mul_one := by rintro (a | a); simp,
  nat_cast := inl,
  nat_cast_zero := rfl,
  nat_cast_succ := λ n, rfl }

instance : linear_ordered_semiring weird :=
{ add_left_cancel := _, --false
  add_le_add_left := _,
  le_of_add_le_add_left := _, --false
  zero_le_one := _,
  mul_lt_mul_of_pos_left := _,
  mul_lt_mul_of_pos_right := _,
  exists_pair_ne := ⟨inl 0, inr 0, inl_ne_inr⟩,
  ..weird.linear_order, ..weird.semiring }

instance : floor_semiring weird :=
{ floor := sum.elim id id,
  ceil := sum.elim id succ,
  floor_of_neg := _,
  gc_floor := _,
  gc_ceil := _ }

@[simp] lemma floor_inl (a : ℕ) : @floor weird _ _ (inl a) = a := rfl
@[simp] lemma floor_inr (a : ℕ) : @floor weird _ _ (inr a) = a := rfl
@[simp] lemma ceil_inl (a : ℕ) : @ceil weird _ _ (inl a) = a := rfl
@[simp] lemma ceil_inr (a : ℕ) : @ceil weird _ _ (inr a) = a + 1 := rfl

def ceil_hom : weird →*o ℕ :=
{ to_fun := ceil,
  map_one' := rfl,
  map_mul' := by rintro ((_ | a) | a) ((_ | b) | b);
    simp [mul_add_one, add_one_mul, ←add_assoc, succ_eq_add_one],
  monotone' := ceil_mono }

@[simp] lemma coe_ceil_hom : ⇑ceil_hom = ceil := rfl

example (a : ℕ) : ⌊ceil_hom (inr a)⌋₊ ≠ @floor weird _ _ (inr a) := succ_ne_self _

end weird
