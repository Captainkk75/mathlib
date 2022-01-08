import order.atoms
import order.locally_finite
import order.zorn

/-!
# To move
-/

variables {α : Type*}

section order_dual
open order_dual
variables [has_lt α]

lemma has_lt.lt.of_dual {a b : order_dual α} (h : a < b) : of_dual b < of_dual a := h

end order_dual

namespace nat

/-- A set of nats without gaps is an interval. The sizes of the gaps and intervals we consider are
bounded by `n`, so that we may induct on it. -/
private lemma all_ioo_of_ex_ioo {S : set ℕ} (n : ℕ) {a b c}
  (hS : ∀ {a b c} (hle : b ≤ a + n) (ha : a ∈ S) (hb : b ∈ S) (hac : a < c) (hcb : c < b),
    (S ∩ set.Ioo a b).nonempty)
  (hle : b ≤ a + n) (ha : a ∈ S) (hb : b ∈ S) (hac : a < c) (hcb : c < b) : c ∈ S :=
begin
  revert a b c,
  induction n with n hS',
  { exact λ a b c hle ha hb hac hcb, (not_lt_of_ge hle (lt_trans hac hcb)).elim },
  intros a b c hle ha hb hac hcb,
  rcases hS hle ha hb hac hcb with ⟨d, hd, had, hdb⟩,
  cases eq_or_ne c d with hcd hcd, { rwa hcd },
  have hxy : ∃ x y, y ≤ x + n ∧ x ∈ S ∧ y ∈ S ∧ x < c ∧ c < y := begin
    cases ne.lt_or_lt hcd with hcd hdc,
    { refine ⟨a, d, nat.le_of_lt_succ _, ha, hd, hac, hcd⟩,
      rw ←nat.add_succ,
      exact lt_of_lt_of_le hdb hle },
    { refine ⟨d, b, nat.le_of_lt_succ _, hd, hb, hdc, hcb⟩,
      rw ←nat.add_succ,
      exact lt_of_le_of_lt hle (add_lt_add_right had _) }
  end,
  rcases hxy with ⟨x, y, hle, hx, hy, hxc, hcy⟩,
  exact hS' (λ a b c hle ha hb hac hcb, hS (hle.trans (le_succ _)) ha hb hac hcb) hle hx hy hxc hcy
end

/-- A set of nats without gaps is an interval. -/
lemma all_icc_of_ex_ioo {S : set ℕ}
  (H : ∀ {a b c} (ha : a ∈ S) (hb : b ∈ S) (hac : a < c) (hcb : c < b), (S ∩ set.Ioo a b).nonempty)
  {a b c} (ha : a ∈ S) (hb : b ∈ S) (hac : a ≤ c) (hcb : c ≤ b) : c ∈ S :=
begin
  cases eq_or_lt_of_le hac with hac hac, { rwa ←hac },
  cases eq_or_lt_of_le hcb with hcb hcb, { rwa  hcb },
  exact all_ioo_of_ex_ioo b (λ a b c _ ha hb hac hcb, H ha hb hac hcb) (le_add_self) ha hb hac hcb
end

end nat

/-- Any singleton is a chain. -/
lemma zorn.chain_singleton (r : α → α → Prop) (a : α) : zorn.chain r {a} :=
set.pairwise_singleton _ _

/-- A preorder is isomorphic to the section from bottom to top. -/
def set.Icc.self_order_iso_bot_top (α : Type*) [preorder α] [order_bot α] [order_top α] :
  α ≃o set.Icc ⊥ (⊤ : α) :=
{ to_fun := λ x, ⟨x, bot_le, le_top⟩,
  inv_fun := subtype.val,
  left_inv := λ _, rfl,
  right_inv := λ _, subtype.eq rfl,
  map_rel_iff' := by simp }

lemma ne_bot_of_lt {α : Type*} [preorder α] [order_bot α] {a b : α} (h : a < b) : b ≠ ⊥ :=
begin
  rintro rfl,
  exact not_lt_bot h,
end

lemma ne_top_of_gt {α : Type*} [preorder α] [order_top α] {a b : α} (h : a < b) : a ≠ ⊤ :=
begin
  rintro rfl,
  exact not_top_lt h,
end

lemma is_simple_order.eq_bot_of_lt {α : Type*} [preorder α] [bounded_order α] [is_simple_order α]
  {a b : α} (h : a < b) :
  a = ⊥ :=
(is_simple_order.eq_bot_or_eq_top _).resolve_right $ ne_top_of_gt h

lemma is_simple_order.eq_top_of_lt {α : Type*} [preorder α] [bounded_order α] [is_simple_order α]
  {a b : α} (h : a < b) :
  b = ⊤ :=
(is_simple_order.eq_bot_or_eq_top _).resolve_left $ ne_bot_of_lt h

lemma bot_lt_top {α : Type*} [partial_order α] [bounded_order α] [nontrivial α] : (⊥ : α) < ⊤ :=
lt_top_iff_ne_top.2 bot_ne_top
