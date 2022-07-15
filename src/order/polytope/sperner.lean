/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.nat_antidiagonal
import data.finset.slice

/-!
# Sperner orders and Whitney numbers

This file defines Whitney numbers and the Sperner and strict Sperner properties of an order.

In a graded order, the `n`-th Whitney number is the number of elements of grade `n`.

Sperner's theorem says that any antichain in `finset α` is of size at most
`(card α).choose (card α / 2)`. This is exactly the maximal Whitney number of `finset α`. Hence, we
say that an order has the *Sperner property* if any antichain is less than some Whitney number.

## Main declarations

* `slice_order`: An order whose slices are finite.
* `slice α n`: The `n`-th slice of `α`. The finset of elements of grade `n`.
* `whitney_number α n`: The number of elements of `α` of grade `n`, aka `n`-th Whitney number.
* `is_sperner_order`: A Sperner order is an order in which every antichain is smaller than some
  slice.
* `is_strict_sperner_order`: A strict Sperner order is a Sperner order in which every maximal
  antichain has the size of some slice.

## Instances

Here are some instances we could have:
* `finset α` when `fintype α`. This is the usual Sperner theorem.
* `list α` when `fintype α`. Roughly corresponds to codes, could be used for Kraft's inequality.
* `tree α`. Roughly corresponds to codes, could be used for Kraft's inequality.
* `α × β`
* `α ×ₗ β` where `fintype α`
* `Π i, α i` where `fintype ι`
* `α ⊕ β`
* `α ⊕ₗ β` where `fintype α`
* `Σ i, α i`, `Σ' i, α i`
* `Σₗ i, α i`, `Σₗ' i, α i`
-/

open finset

variables {𝕆 α β : Type*}

/-! ### Slice orders -/

/-- A `slice_order` is an order whose "horizontal slices" (elements of a given grade) are finite.
This is the most general structure in which we can define Whitney numbers. -/
class slice_order (𝕆 α : Type*) [preorder 𝕆] [preorder α] [order_bot α] [grade_order 𝕆 α] :=
(slice (n : 𝕆) : finset α)
(mem_slice (n : 𝕆) (a : α) : a ∈ slice n ↔ grade 𝕆 a = n)

section slice_order
section preorder
variables [preorder 𝕆] [preorder α]

section order_bot
variables (α) [order_bot α] [grade_order 𝕆 α] [slice_order 𝕆 α] (n : 𝕆) {a : α}

/-- The `n`-th slice of `α` is the finset of element of `α` of grade `n`. -/
def slice : finset α := slice_order.slice n

variables {α n}

@[simp] lemma mem_slice_iff : a ∈ slice α n ↔ grade 𝕆 a = n := slice_order.mem_slice _ _

lemma mem_slice_grade (a : α) : a ∈ slice α (grade 𝕆 a) := mem_slice_iff.2 rfl

variables (α n)

lemma slice_sized : (slice α n : set α).sized n := λ a, mem_slice_iff.1

lemma slice_nonempty [no_top_order α] : (slice α n).nonempty := sorry

end order_bot

section bounded_order
variables [bounded_order α] [grade_order 𝕆 α] [slice_order 𝕆 α] {n : 𝕆} {a : α}

lemma slice_nonempty_of_le (h : n ≤ grade 𝕆 (⊤ : α)) : (slice α n).nonempty := sorry

end bounded_order
end preorder

section partial_order
variables [preorder 𝕆] [partial_order α]

section order_bot
variables (α) [order_bot 𝕆] [order_bot α] [grade_order 𝕆 α] [slice_order 𝕆 α] (n : 𝕆) {a : α}

lemma slice_bot : slice α (⊥ : 𝕆) = {⊥} := sorry

/-- A slice order is locally finite. The converse is false, for example `list α` with the prefix
order when `α` is infinite. -/
@[reducible] -- See note [reducible non-instances]
def slice_order.to_locally_finite_order [locally_finite_order 𝕆] [decidable_eq α]
  [@decidable_rel α (≤)] [@decidable_rel α (<)] :
  locally_finite_order α :=
locally_finite_order.of_decidable_le_lt
  (λ a b, (Icc (grade 𝕆 a) (grade 𝕆 b)).sup $ slice α)
  (λ a b, (Ico (grade 𝕆 a) (grade 𝕆 b)).sup $ slice α)
  (λ a b, (Ioc (grade 𝕆 a) (grade 𝕆 b)).sup $ slice α)
  (λ a b, (Ioo (grade 𝕆 a) (grade 𝕆 b)).sup $ slice α)
  (λ a b x ha hb, mem_sup.2
    ⟨grade 𝕆 x, mem_Icc.2 ⟨grade_mono ha, grade_mono hb⟩, mem_slice_grade _⟩)
  (λ a b x ha hb, mem_sup.2
    ⟨grade 𝕆 x, mem_Ico.2 ⟨grade_mono ha, grade_strict_mono hb⟩, mem_slice_grade _⟩)
  (λ a b x ha hb, mem_sup.2
    ⟨grade 𝕆 x, mem_Ioc.2 ⟨grade_strict_mono ha, grade_mono hb⟩, mem_slice_grade _⟩)
  (λ a b x ha hb, mem_sup.2
    ⟨grade 𝕆 x, mem_Ioo.2 ⟨grade_strict_mono ha, grade_strict_mono hb⟩, mem_slice_grade _⟩)

end order_bot

section bounded_order
variables (α) [bounded_order α] [grade_order 𝕆 α] [slice_order 𝕆 α] (n : ℕ) {a : α}

lemma slice_grade_top : slice α (grade 𝕆 (⊤ : α)) = {⊤} := sorry

end bounded_order
end partial_order
end slice_order

/-! ### Whitney numbers -/

section whitney
section preorder
variables [preorder 𝕆] [preorder α]

section order_bot
variables (α) [order_bot α] [grade_order 𝕆 α] [slice_order 𝕆 α] (n : 𝕆) {a : α}

-- Is this worth a separate definition?
/-- The `n`-th Whitney number of `α`is the number of element of `α` of grade `n`. -/
def whitney_number : ℕ := (slice α n).card

lemma whitney_number_pos [no_top_order α] : 0 < whitney_number α n :=
card_pos.2 $ slice_nonempty _ _

end order_bot

section bounded_order
variables [bounded_order α] [grade_order 𝕆 α] [slice_order 𝕆 α] {n : 𝕆} {a : α}

lemma whitney_number_pos_of_le (h : n ≤ grade 𝕆 (⊤ : α)) : 0 < whitney_number α n :=
card_pos.2 $ slice_nonempty_of_le h

end bounded_order
end preorder

section partial_order
variables [preorder 𝕆] [partial_order α]

section order_bot
variables (α) [order_bot 𝕆] [order_bot α] [grade_order 𝕆 α] [slice_order 𝕆 α] {a : α}

lemma whitney_number_bot : whitney_number α (⊥ : 𝕆) = 1 :=
by rw [whitney_number, slice_bot, card_singleton]

end order_bot

section bounded_order
variables (α) [bounded_order α] [grade_order 𝕆 α] [slice_order 𝕆 α] (n : ℕ) {a : α}

lemma whitney_number_grade_top : whitney_number α (grade 𝕆 (⊤ : α)) = 1 :=
by rw [whitney_number, slice_grade_top, card_singleton]

end bounded_order
end partial_order
end whitney

/-! ### Sperner orders -/

/-- An order has the Sperner property if all antichains are smaller than some slice of the order.
Sperner's theorem exactly claims that `finset α` has the Sperner property. -/
class is_sperner_order (𝕆 α : Type*) [preorder 𝕆] [preorder α] [order_bot α] [grade_order 𝕆 α]
  [slice_order 𝕆 α] :
  Prop :=
(exists_le_whitney (s : finset α) : is_antichain (≤) (s : set α) →
  ∃ n : 𝕆, s.card ≤ whitney_number α n)

/-- An order has the strict Sperner property if all antichains are smaller than some slice of the
order and all maximal antichains are the size of some Whitney number. -/
class is_strict_sperner_order (𝕆 α : Type*) [preorder 𝕆] [preorder α] [order_bot α]
  [grade_order 𝕆 α] [slice_order 𝕆 α] extends is_sperner_order 𝕆 α : Prop :=
(exists_eq_whitney (s : finset α) : is_antichain (≤) (s : set α) →
  (∀ t : finset α, is_antichain (≤) (t : set α) → s ⊆ t → s = t) →
    ∃ n : 𝕆, s.card = whitney_number α n)

/-! ### Instances -/

/-! ### Product of two slice orders -/

namespace prod
variables [partial_order α] [partial_order β] [order_bot α] [order_bot β] [grade_order ℕ α]
  [grade_order ℕ β] [slice_order ℕ α] [slice_order ℕ β] [decidable_eq α] [decidable_eq β]

instance : slice_order ℕ (α × β) :=
{ slice := λ n, begin
    sorry
    -- have := (nat.antidiagonal n).image (prod.map (slice α) $ slice β),
  end,
  mem_slice := sorry }

end prod
