/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/

import data.fintype.basic
import data.nat.choose
import combinatorics.set_family.basic
import order.antichain

/-!
# Shadows

This file proves the local LYM and LYM theorems, as well as Sperner's theorem.

## Main declarations

* `local_lym`
* `lubell_yamamoto_meshalkin`
* `sperner`

## Notation

We introduce the notation ∂ to denote the shadow.
We also maintain the convention that A, B, ... denote sets (usually finset α),
𝒜, ℬ, ... denote set families, i.e. `finset (finset α)` and lower-case letters
denote elements of the ground set α.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, lym, slice, sperner, antichain
-/

open finset fintype nat
open_locale finset_family

variables {α : Type*}

/-!
### Build up and proof of local LYM

If there is a fintype α which is our universe, informally write `α^(r)` for the
`set {A : finset α | |A| = r}`. Then if `𝒜` is a subset of `α^(r)`, we get that `∂𝒜`
is a subset of `α^(r-1)`.
The local LYM inequality says `𝒜` 'takes up less' of `α^(r)` than `∂𝒜` takes up of
`α^(r-1)`. In particular,
`|𝒜| / choose |α| r ≤ |∂𝒜| / choose |α| (r-1)`
-/

section local_lym
variables [decidable_eq α]

/-- Start by multiplying out the inequality so it's in a slightly nicer form. -/
lemma multiply_out {A B n r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ n)
  (h : A * r ≤ B * (n - r + 1)) :
  (A : ℚ) / nat.choose n r ≤ B / nat.choose n (r-1) :=
begin
  rw div_le_div_iff; norm_cast,
  { apply le_of_mul_le_mul_right _ ‹0 < r›,
    cases r,
    { simp },
    rw nat.succ_eq_add_one at *,
    rw [← nat.sub_add_comm hr2, nat.add_sub_add_right] at h,
    convert nat.mul_le_mul_right (choose n r) h using 1;
    { simp [mul_assoc, nat.choose_succ_right_eq],
      left,
      ac_refl } },
{ apply nat.choose_pos hr2 },
  { apply nat.choose_pos (le_trans (nat.pred_le _) hr2) },
end

/-- We'll prove local LYM by a double counting argument. Here's the first set
we'll count, which is effectively `{(A, B) | A ∈ 𝒜, B ∈ all_removals A}`. -/
def the_pairs (𝒜 : finset (finset α)) : finset (finset α × finset α) :=
𝒜.sup (λ A, (all_removals A).image (prod.mk A))

/-- Find how big the_pairs is: for each `A ∈ 𝒜` there are `r` possible `B`, giving the
exact cardinality. -/
lemma card_the_pairs {r : ℕ} (𝒜 : finset (finset α)) (a : all_sized 𝒜 r) :
  (the_pairs 𝒜).card = 𝒜.card * r :=
begin
  rw [the_pairs, sup_eq_bUnion, card_bUnion],
  { convert sum_const_nat _,
    intros x hx,
    rw card_image_of_inj_on,
    rw card_all_removals (a _ hx),
    exact (λ _ _ _ _ k, (prod.mk.inj k).2) },
  simp only [disjoint_left, mem_image],
  rintro _ _ _ _ k a ⟨_, _, rfl⟩ ⟨_, _, a₂⟩,
  exact k (prod.mk.inj a₂.symm).1,
end

/-- Here's the second set we'll count. We're trying to get the same set, but we
count `B` first, so we overestimate a bit. It's pretty much
`{(A, B) | B ∈ ∂𝒜, ∃ i ∉ B: A = B ∪ i}` -/
def from_below [fintype α] (𝒜 : finset (finset α)) : finset (finset α × finset α) :=
(∂𝒜).sup (λ B, (univ \ B).image (λ x, (insert x B, B)))

/-- Note the first is a subset of the second: if `A ∈ 𝒜` and `B ∈ all_removals A`, then certainly
`B ∈ ∂𝒜`, and there's some `i` that was removed from `A` to make `B`.-/
lemma above_sub_below [fintype α] (𝒜 : finset (finset α)) : the_pairs 𝒜 ⊆ from_below 𝒜 :=
begin
  rintro ⟨A, B⟩,
  simp only [the_pairs, from_below, mem_sup, mem_all_removals, mem_shadow_iff, true_and, and_imp,
    exists_prop, mem_sdiff, mem_image, prod.mk.inj_iff, mem_univ, exists_imp_distrib],
  rintro A Ah B i ih z rfl rfl,
  exact ⟨B, ⟨A, Ah, i, ih, z⟩, i, z ▸ not_mem_erase _ _,
          z ▸ insert_erase ih, rfl⟩
end

/-- We can also find how big the second set is: for each `B` there are `|α| - r + 1` choices for
what to put into it. -/
lemma card_from_below [fintype α] {𝒜 : finset (finset α)} {r : ℕ}
  (a : all_sized 𝒜 r) :
  (from_below 𝒜).card = (∂𝒜).card * (card α - (r - 1)) :=
begin
  rw [from_below, sup_eq_bUnion, card_bUnion],
  { apply sum_const_nat,
    intros,
    rw [card_image_of_inj_on,
    card_univ_diff,
    shadow_sized a _ H],
    intros x1 x1h _ _ h,
    injection h,
    have q := mem_insert_self x1 x,
    rw [h_1, mem_insert] at q,
    apply q.resolve_right (mem_sdiff.1 x1h).2 },
  intros _ _ _ _ t,
  rw disjoint_left,
  simp_rw [mem_image, not_exists, exists_prop, mem_sdiff,
            mem_univ, true_and, exists_imp_distrib,
            prod.forall, prod.mk.inj_iff, and_imp, not_and],
  rintro _ b i hi rfl rfl j hj k,
  rwa eq_comm,
end

/-- The local LYM inequality says `𝒜` 'takes up less' of `α^(r)` than `∂𝒜` takes up of `α^(r - 1)`.
In particular, `|𝒜| / choose |α| r ≤ |∂𝒜| / choose |α| (r-1)`. -/
theorem local_lym [fintype α] {𝒜 : finset (finset α)} {r : ℕ} (hr1 : 1 ≤ r)
  (H : all_sized 𝒜 r) :
  (𝒜.card : ℚ) / (card α).choose r ≤ (∂𝒜).card / (card α).choose (r-1) :=
begin
  cases lt_or_le (card α) r with z hr2,
  -- Take care of the r > n case: it's trivial
  { rw [choose_eq_zero_of_lt z, cast_zero, div_zero],
    refine div_nonneg _ _; norm_cast,
    any_goals { apply nat.zero_le } },
  { apply multiply_out hr1 hr2,
  -- Multiply out, convert to the cardinality forms we got above and done
    rw [← card_the_pairs _ H, ← tsub_tsub_assoc hr2 hr1,
        ← card_from_below H],
    apply card_le_of_subset,
    apply above_sub_below }
end

end local_lym

/-!
The LYM inequality says ∑_i |A#i|/(n choose i) ≤ 1 for an antichain A.
Observe that A#i is all the stuff in A which has size i, and the collection of
subsets of (fin n) with size i has size (n choose i).
So, |A#i|/(n choose i) represents how much of each that A can take up.

Other proofs of LYM exist, but we'll do it by applying local LYM.
-/
section lym

variables [fintype α]

/-- An inductive definition, from the top down.
`falling 𝒜 k` is all the sets with cardinality (card α - k) which are a
subset of something in 𝒜. -/
def falling [decidable_eq α] (𝒜 : finset (finset α)) : Π (k : ℕ), finset (finset α)
| 0       := 𝒜#(card α)
| (k + 1) := 𝒜#(card α - (k+1)) ∪ shadow (falling k)

/--
Everything in the kth fallen has size `n-k`
-/
lemma falling_sized [decidable_eq α] (𝒜 : finset (finset α)) (k : ℕ) :
  all_sized (falling 𝒜 k) (card α - k) :=
begin
  induction k with k ih; rw falling,
  { apply sized_slice },
  { rw ← union_layer,
    split,
    { apply sized_slice },
    { apply shadow_sized ih } },
end

/--
Here's the first key proposition, helping to give the disjointness
property in the next lemma.
-/
theorem antichain_prop [decidable_eq α] {𝒜 : finset (finset α)} {r k : ℕ}
  (hk : k ≤ card α) (hr : r < k) (H : is_antichain (⊆) (𝒜 : set (finset α))) :
  ∀ A ∈ 𝒜#(card α - k), ∀ B ∈ ∂ (falling 𝒜 r), ¬(A ⊆ B) :=
begin
  intros A HA B HB k,
  obtain ⟨C, HC, _⟩ := exists_subset_of_mem_shadow HB,
  replace k := trans k ‹B ⊆ C›,
  clear HB h_h B,
  induction r with r ih generalizing A C;
  rw falling at HC,
  any_goals { rw mem_union at HC, cases HC },
  any_goals { refine H A (mem_slice.1 HA).1 C (mem_slice.1 HC).1 _ ‹A ⊆ C›,
              apply ne_of_diff_slice HA HC _,
              apply ne_of_lt },
  { apply nat.sub_lt_of_pos_le _ _ hr hk },
  { mono },
  { obtain ⟨_, HB', HB''⟩ := exists_subset_of_mem_shadow HC,
    exact ih (lt_of_succ_lt hr) _ _ HA HB' (trans k_1 HB'') }
end

/-- This tells us that `falling 𝒜 k` is disjoint from the` n - (k + 1)`-sized elements of `𝒜`,
thanks to the antichain property. -/
lemma is_antichain.disjoint_falling_slice [decidable_eq α] {𝒜 : finset (finset α)} {k : ℕ}
  (H : is_antichain (⊆) (𝒜 : set (finset α))) (hk : k + 1 ≤ card α) :
  disjoint (∂ (falling 𝒜 k)) (𝒜#(card α - (k + 1))) :=
disjoint_right.2 $ λ A HA HB,
  antichain_prop hk (lt_add_one k) H A HA A HB (subset.refl _)

/-- In particular, we can use induction and local LYM to get a bound on any top
part of the sum in LYM in terms of the size of `falling 𝒜 k`. -/
lemma card_falling [decidable_eq α] {𝒜 : finset (finset α)} {k : ℕ} (hk : k ≤ card α)
  (H : is_antichain (⊆) (𝒜 : set (finset α))) :
  (range (k+1)).sum
    (λ r, ((𝒜#(card α - r)).card : ℚ) / (card α).choose (card α - r))
  ≤ (falling 𝒜 k).card / (card α).choose (card α - k) :=
begin
  induction k with k ih,
  { simp [falling] },
  rw [sum_range_succ, falling, union_comm, card_disjoint_union (H.disjoint_falling_slice hk),
    cast_add, add_div],
  exact add_le_add_right
    ((ih $ le_of_lt hk).trans (local_lym (le_tsub_of_add_le_left hk) (falling_sized _ _))) _,
end

/-- A stepping-stone lemma to get to LYM. -/
lemma card_fallen [decidable_eq α] {𝒜 : finset (finset α)}
  (H : is_antichain (⊆) (𝒜 : set (finset α))) :
  (range (card α + 1)).sum (λ r, ((𝒜#r).card : ℚ) / (card α).choose r)
  ≤ (falling 𝒜 (card α)).card / (card α).choose 0 :=
begin
  rw [← nat.sub_self (card α)],
  convert ← card_falling le_rfl H using 1,
  apply sum_flip (λ r, ((𝒜#r).card : ℚ) / (card α).choose r),
end

/-- The LYM inequality says `∑_i |A#i|/(n choose i) ≤ 1` for an antichain `A`.
Observe that `A#i` is all the stuff in `A` which has size `i`, and the collection of
sets of `fin n` with size `i` has size `n choose i`.
So `|A#i|/(n choose i)` represents how much of each `A` can take up.

The proof is easy using the developed lemmas above. -/
theorem lubell_yamamoto_meshalkin {𝒜 : finset (finset α)}
  (H : is_antichain (⊆) (𝒜 : set (finset α))) :
  (range (card α + 1)).sum (λ r, ((𝒜#r).card : ℚ) / (card α).choose r) ≤ 1 :=
begin
  classical,
  transitivity,
  { apply card_fallen H },
  rw div_le_iff; norm_cast,
  { simpa only [mul_one, nat.choose_zero_right, nat.sub_self]
      using number_of_fixed_size (falling_sized 𝒜 (card α)) },
  apply nat.choose_pos (nat.zero_le _)
end

end lym

/-- Sperner's theorem gives a bound on the size of an antichain. This can be proved in a few ways,
but this uses the machinery already developed about LYM. The idea is simple: with LYM, we get a
bound on how much of `A` can have any particular size.  So, to maximise the size of A, we'd like to
fit it all into the term with the biggest denominator. In other words,
`∑_i |A#i|/(n choose (n/2)) ≤ ∑_i |A#i|/(n choose i) ≤ 1`, so `∑_i |A#i| ≤ (n choose (n/2))` as
required. -/
theorem sperner [fintype α] {𝒜 : finset (finset α)} (H : is_antichain (⊆) (𝒜 : set (finset α))) :
  𝒜.card ≤ (card α).choose (card α / 2) :=
begin
  classical,
  have: (range (card α + 1)).sum (λ (r : ℕ), ((𝒜#r).card : ℚ) / (card α).choose (card α/2)) ≤ 1,
  { apply le_trans _ (lubell_yamamoto_meshalkin H),
    apply sum_le_sum,
    intros r hr,
    apply div_le_div_of_le_left; norm_cast,
    { apply nat.zero_le },
    { apply choose_pos, rw mem_range at hr, rwa ← nat.lt_succ_iff },
    { apply choose_le_middle } },
  rw [← sum_div, ← nat.cast_sum, div_le_one] at this,
  { norm_cast at this,
    rw ← card_bUnion at this,
    convert this,
    simp only [ext_iff, mem_slice, mem_bUnion, exists_prop, mem_range, lt_succ_iff],
    intro a,
    split,
    { intro ha,
      refine ⟨a.card, card_le_of_subset (subset_univ _), ha, rfl⟩ },
    { rintro ⟨_, _, q, _⟩,
      exact q },
    intros x _ y _ ne,
    rw disjoint_left,
    intros a Ha k,
    exact ne_of_diff_slice Ha k ne rfl },
  norm_cast,
  apply choose_pos,
  apply nat.div_le_self,
end
