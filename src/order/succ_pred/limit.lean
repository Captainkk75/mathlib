/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import order.succ_pred.basic

/-!
# Successor and predecessor limits

The predicates `is_succ_limit` and `is_pred_limit` are defined elsewhere, to refer to elements in an
order that don't cover or aren't covered by another element, respectively. In this file, we prove
theorems relating these predicates to successors in a `succ_order` and predecessors in a
`pred_order`.

## Todo

The plan is to eventually replace `ordinal.is_limit` and `cardinal.is_limit` with the common
predicate `is_succ_limit`.
-/

variables {α : Type*} {a b : α}

open function set order order_dual

/-! ### Successor limits -/

section preorder
variables [preorder α] [succ_order α]

protected lemma is_succ_limit.is_max (h : is_succ_limit (succ a)) : is_max a :=
by { by_contra H, exact h a (covby_succ_of_not_is_max H) }

lemma not_is_succ_limit_succ_of_not_is_max (ha : ¬ is_max a) : ¬ is_succ_limit (succ a) :=
by { contrapose! ha, exact ha.is_max }

section no_max_order
variables [no_max_order α]

lemma is_succ_limit.succ_ne (h : is_succ_limit a) (b) : succ b ≠ a :=
by { rintro rfl, exact not_is_max _ h.is_max }

@[simp] lemma not_is_succ_limit_succ (a : α) : ¬ is_succ_limit (succ a) := λ h, h.succ_ne _ rfl

end no_max_order

section is_succ_archimedean
variable [is_succ_archimedean α]

lemma is_succ_limit.is_min_of_no_max [no_max_order α] (h : is_succ_limit a) : is_min a :=
λ b hb, begin
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩,
  { exact le_rfl },
  { rw iterate_succ_apply' at h,
    exact (not_is_succ_limit_succ _ h).elim }
end

@[simp] lemma is_succ_limit_iff_of_no_max [no_max_order α] : is_succ_limit a ↔ is_min a :=
⟨is_succ_limit.is_min_of_no_max, is_min.is_succ_limit⟩

lemma not_is_succ_limit_of_no_max [no_min_order α] [no_max_order α] : ¬ is_succ_limit a := by simp

end is_succ_archimedean
end preorder

section partial_order
variables [partial_order α] [succ_order α]

lemma is_succ_limit_of_succ_ne (h : ∀ b, succ b ≠ a) : is_succ_limit a := λ b hba, h b hba.succ_eq

lemma not_is_succ_limit_iff : ¬ is_succ_limit a ↔ ∃ b, ¬ is_max b ∧ succ b = a :=
begin
  rw not_is_succ_limit_iff_exists_covby,
  refine exists_congr (λ b, ⟨λ hba, ⟨hba.lt.not_is_max, hba.succ_eq⟩, _⟩),
  rintro ⟨h, rfl⟩,
  exact covby_succ_of_not_is_max h
end

/-- See `not_is_succ_limit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
lemma mem_range_succ_of_not_is_succ_limit (h : ¬ is_succ_limit a) : a ∈ range (@succ α _ _) :=
by { cases not_is_succ_limit_iff.1 h with b hb, exact ⟨b, hb.2⟩ }

lemma is_succ_limit_of_succ_lt (H : ∀ a < b, succ a < b) : is_succ_limit b :=
λ a hab, (H a hab.lt).ne hab.succ_eq

lemma is_succ_limit.succ_lt (hb : is_succ_limit b) (ha : a < b) : succ a < b :=
begin
  by_cases h : is_max a,
  { rwa h.succ_eq },
  { rw [lt_iff_le_and_ne, succ_le_iff_of_not_is_max h],
    refine ⟨ha, λ hab, _⟩,
    subst hab,
    exact (h hb.is_max).elim }
end

lemma is_succ_limit.succ_lt_iff (hb : is_succ_limit b) : succ a < b ↔ a < b :=
⟨λ h, (le_succ a).trans_lt h, hb.succ_lt⟩

lemma is_succ_limit_iff_succ_lt : is_succ_limit b ↔ ∀ a < b, succ a < b :=
⟨λ hb a, hb.succ_lt, is_succ_limit_of_succ_lt⟩

/-- A value can be built by building it on successors and successor limits. -/
@[elab_as_eliminator] noncomputable def is_succ_limit_rec_on {C : α → Sort*} (b)
  (hs : Π a, ¬ is_max a → C (succ a)) (hl : Π a, is_succ_limit a → C a) : C b :=
begin
  by_cases hb : is_succ_limit b,
  { exact hl b hb },
  { have H := classical.some_spec (not_is_succ_limit_iff.1 hb),
    rw ←H.2,
    exact hs _ H.1 }
end

lemma is_succ_limit_rec_on_limit {C : α → Sort*} (hs : Π a, ¬ is_max a → C (succ a))
  (hl : Π a, is_succ_limit a → C a) (hb : is_succ_limit b) :
  @is_succ_limit_rec_on α _ _ C b hs hl = hl b hb :=
by { classical, exact dif_pos hb }

lemma is_succ_limit_rec_on_succ' {C : α → Sort*} (hs : Π a, ¬ is_max a → C (succ a))
  (hl : Π a, is_succ_limit a → C a) {b : α} (hb : ¬ is_max b) :
  @is_succ_limit_rec_on α _ _ C (succ b) hs hl = hs b hb :=
begin
  have hb' := not_is_succ_limit_succ_of_not_is_max hb,
  have H := classical.some_spec (not_is_succ_limit_iff.1 hb'),
  rw is_succ_limit_rec_on,
  simp only [cast_eq_iff_heq, hb', not_false_iff, eq_mpr_eq_cast, dif_neg],
  congr,
  { exact (succ_eq_succ_iff_of_not_is_max H.1 hb).1 H.2 },
  { apply proof_irrel_heq }
end

section no_max_order
variables [no_max_order α]

@[simp] lemma is_succ_limit_rec_on_succ {C : α → Sort*} (hs : Π a, ¬ is_max a → C (succ a))
  (hl : Π a, is_succ_limit a → C a) (b : α) :
  @is_succ_limit_rec_on α _ _ C (succ b) hs hl = hs b (not_is_max b) :=
is_succ_limit_rec_on_succ' _ _ _

lemma is_succ_limit_iff_succ_ne : is_succ_limit a ↔ ∀ b, succ b ≠ a :=
⟨is_succ_limit.succ_ne, is_succ_limit_of_succ_ne⟩

lemma not_is_succ_limit_iff' : ¬ is_succ_limit a ↔ a ∈ range (@succ α _ _) :=
by { simp_rw [is_succ_limit_iff_succ_ne, not_forall, not_ne_iff], refl }

end no_max_order

section is_succ_archimedean
variable [is_succ_archimedean α]

protected lemma is_succ_limit.is_min (h : is_succ_limit a) : is_min a :=
λ b hb, begin
  revert h,
  refine succ.rec (λ _, le_rfl) (λ c hbc H hc, _) hb,
  have := hc.is_max.succ_eq,
  rw this at hc ⊢,
  exact H hc
end

@[simp] lemma is_succ_limit_iff : is_succ_limit a ↔ is_min a :=
⟨is_succ_limit.is_min, is_min.is_succ_limit⟩

lemma not_is_succ_limit [no_min_order α] : ¬ is_succ_limit a := by simp

end is_succ_archimedean
end partial_order

/-! ### Predecessor limits -/

section preorder
variables [preorder α] [pred_order α]

protected lemma is_pred_limit.is_min (h : is_pred_limit (pred a)) : is_min a :=
by { by_contra H, exact h a (pred_covby_of_not_is_min H) }

lemma not_is_pred_limit_pred_of_not_is_min (ha : ¬ is_min a) : ¬ is_pred_limit (pred a) :=
by { contrapose! ha, exact ha.is_min }

section no_min_order
variables [no_min_order α]

lemma is_pred_limit.pred_ne (h : is_pred_limit a) (b) : pred b ≠ a :=
by { rintro rfl, exact not_is_min _ h.is_min }

@[simp] lemma not_is_pred_limit_pred (a : α) : ¬ is_pred_limit (pred a) := λ h, h.pred_ne _ rfl

end no_min_order

section is_pred_archimedean
variable [is_pred_archimedean α]

protected lemma is_pred_limit.is_max_of_no_min [no_min_order α] (h : is_pred_limit a) : is_max a :=
@is_succ_limit.is_min_of_no_max αᵒᵈ (to_dual a) _ _ _ _ h.dual

@[simp] lemma is_pred_limit_iff_of_no_min [no_min_order α] : is_pred_limit a ↔ is_max a :=
is_succ_limit_to_dual_iff.symm.trans is_succ_limit_iff_of_no_max

lemma not_is_pred_limit_of_no_min [no_min_order α] [no_max_order α] : ¬ is_pred_limit a :=
by simp

end is_pred_archimedean
end preorder

section partial_order
variables [partial_order α] [pred_order α]

lemma is_pred_limit_of_pred_ne (h : ∀ b, pred b ≠ a) : is_pred_limit a := λ b hba, h b hba.pred_eq

lemma not_is_pred_limit_iff : ¬ is_pred_limit a ↔ ∃ b, ¬ is_min b ∧ pred b = a :=
by { rw ←is_succ_limit_to_dual_iff, exact not_is_succ_limit_iff }

/-- See `not_is_pred_limit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
lemma mem_range_pred_of_not_is_pred_limit (h : ¬ is_pred_limit a) : a ∈ range (@pred α _ _) :=
by { cases not_is_pred_limit_iff.1 h with b hb, exact ⟨b, hb.2⟩ }

lemma is_pred_limit_of_pred_lt (H : ∀ a > b, pred a < b) : is_pred_limit b :=
λ a hab, (H a hab.lt).ne hab.pred_eq

lemma is_pred_limit.lt_pred (h : is_pred_limit a) : a < b → a < pred b :=
@is_succ_limit.succ_lt αᵒᵈ b a _ _ h.dual

lemma is_pred_limit.lt_pred_iff (h : is_pred_limit a) : a < pred b ↔ a < b :=
@is_succ_limit.succ_lt_iff αᵒᵈ b a _ _ h.dual

lemma is_pred_limit_iff_lt_pred : is_pred_limit a ↔ ∀ b > a, a < pred b :=
is_succ_limit_to_dual_iff.symm.trans is_succ_limit_iff_succ_lt

/-- A value can be built by building it on predecessors and predecessor limits. -/
@[elab_as_eliminator] noncomputable def is_pred_limit_rec_on {C : α → Sort*} (b)
  (hs : Π a, ¬ is_min a → C (pred a)) (hl : Π a, is_pred_limit a → C a) : C b :=
@is_succ_limit_rec_on αᵒᵈ _ _ _ _ hs (λ a ha, hl _ ha.dual)

lemma is_pred_limit_rec_on_limit {C : α → Sort*} (hs : Π a, ¬ is_min a → C (pred a))
  (hl : Π a, is_pred_limit a → C a) (hb : is_pred_limit b) :
  @is_pred_limit_rec_on α _ _ C b hs hl = hl b hb :=
is_succ_limit_rec_on_limit _ _ hb.dual

lemma is_pred_limit_rec_on_pred' {C : α → Sort*} (hs : Π a, ¬ is_min a → C (pred a))
  (hl : Π a, is_pred_limit a → C a) {b : α} (hb : ¬ is_min b) :
  @is_pred_limit_rec_on α _ _ C (pred b) hs hl = hs b hb :=
is_succ_limit_rec_on_succ' _ _ _

section no_min_order
variables [no_min_order α]

@[simp] theorem is_pred_limit_rec_on_pred {C : α → Sort*} (hs : Π a, ¬ is_min a → C (pred a))
  (hl : Π a, is_pred_limit a → C a) (b : α) :
  @is_pred_limit_rec_on α _ _ C (pred b) hs hl = hs b (not_is_min b) :=
is_succ_limit_rec_on_succ _ _ _

end no_min_order

section is_pred_archimedean
variable [is_pred_archimedean α]

protected lemma is_pred_limit.is_max (h : is_pred_limit a) : is_max a := h.dual.is_min

@[simp] lemma is_pred_limit_iff : is_pred_limit a ↔ is_max a :=
is_succ_limit_to_dual_iff.symm.trans is_succ_limit_iff

lemma not_is_pred_limit [no_max_order α] : ¬ is_pred_limit a := by simp

end is_pred_archimedean
end partial_order
