/-
Copyright (c) 2022 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import topology.metric_space.emetric_space
/-!
# Basic definitions of coarse geometry on metric space

This file defines the notions of “coarsely dense” and “coarsely separated” subsets
of a pseudo-emetric space.
If `α` is a pseudo-emetric space, `s t : set α` and `ε δ : ℝ≥0`:

* `s` is `ε`-dense in `t` if any point of `t` is at distance at most `ε` from some point of `s`;
* `s` is `δ`-separated if any two distinct points of `s` have distance greater than `δ`.

## Main result

* `exists_coarsely_separated_coarsely_dense_with_in`:
  Given a subset `S` of the pseudo-emetric space `α` and some non-negative `δ`,
  there exists a set `s ⊆ S` that is both `δ`-dense in `S` and `δ`-separated.

## References

* [C. Druțu and M. Kapovich **Geometric group theory**][MR3753580]

## Tags

coarse geometry, metric space
-/

universes u v w

open function set fintype function pseudo_emetric_space
open_locale nnreal ennreal

variables {α : Type u} [pseudo_emetric_space α]

/--
Given a pseudo-emetric space `α`, the subset `s` is `ε`-dense in the subset `t`
if any point of `t` is at distance at most `ε` from some point of `s`.
-/
def coarsely_dense_with_in (ε : ℝ≥0) (s t : set α) :=
∀ ⦃x⦄ (hx : x ∈ t), ∃ ⦃y⦄ (hy : y ∈ s), edist x y ≤ ε

/--
Given a pseudo-emetric space `α`, the subset `s` is `δ`-separated
if any pair of distinct points of `s` has distance greater than `δ`.
-/
def coarsely_separated_with  (δ : ℝ≥0) (s : set α)  :=
∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), x ≠ y → edist x y > δ

namespace coarsely_dense_with_in

/--
A set is always `0`-dense in itself.
-/
lemma refl (s : set α) : coarsely_dense_with_in 0 s s :=
λ x xs, ⟨x, xs, by simp⟩

/--
If `r` is `ε`-dense in `s`, and `s` is `ε'`-dense in `t`,
then `r` is `(ε+ε')`-dense in `t`.
-/
lemma trans {ε ε' : ℝ≥0} {r s t : set α}
  (r_in_s : coarsely_dense_with_in ε r s) (s_in_t : coarsely_dense_with_in ε' s t) :
  coarsely_dense_with_in (ε + ε') r t :=
begin
  rintros z z_in_t,
  rcases s_in_t z_in_t with ⟨y,y_in_s,yd⟩,
  rcases r_in_s y_in_s with ⟨x,x_in_r,xd⟩,
  use [x, x_in_r],
  calc edist z x ≤ (edist z y) + (edist y x) : edist_triangle z y x
             ... ≤ ε'          + (edist y x) : add_le_add yd (le_refl $ edist y x)
             ... ≤ ε'          + ε           : add_le_add (le_refl ε') xd
             ... = ε + ε'                    : by ring
end

/--
If `s` is `ε`-dense in `t`, `s ⊆ s'`, `t' ⊆ t`, and `ε ≤ ε'`,
then `s'` is `ε'`-dense in `t'`.
-/
lemma weaken {ε ε' : ℝ≥0} {s s' t t' : set α }
  (s_in_t : coarsely_dense_with_in ε s t)
  (s_sub_s' : s ⊆ s') (t'_sub_t : t' ⊆ t) (ε_le_ε' : ε ≤ ε') :
  coarsely_dense_with_in ε' s' t' :=
begin
  rintros z z_in_t',
  have z_in_t : z ∈ t, from t'_sub_t z_in_t',
  rcases s_in_t z_in_t with ⟨x,x_in_s,xd⟩,
  have x_in_s' : x ∈ s', from s_sub_s' x_in_s,
  use [x,x_in_s'],
  calc edist z x ≤ ε  : xd
             ... ≤ ε' : ennreal.coe_le_coe.mpr ε_le_ε',
end

/--
If `s` is a maximal `δ`-separated subset of `S`, then it is `δ`-dense in `S`.
-/
theorem of_max_coarsely_separated_with_in {δ : ℝ≥0} {s S: set α}
  (H : s ⊆ S
     ∧ coarsely_separated_with δ s
     ∧ (∀ t : set α, s ⊆ t → t ⊆ S →  coarsely_separated_with δ t → s = t)) :
  coarsely_dense_with_in δ s S :=
begin
  rcases H with ⟨s_sub_S, s_sep, s_max⟩,
  rintros x xS,
  let t := s.insert x,
  by_contradiction H,
  push_neg at H,
  have x_notin_s : x ∉ s,
  { intro x_in_s,
    have : edist x x > 0, from gt_of_gt_of_ge (H x_in_s) (zero_le ↑δ),
    exact (ne_of_gt this) (edist_self x)},
  have s_sub_t : s ⊆ t , from subset_insert x s,
  have s_ne_t : s ≠ t , from ne_insert_of_not_mem s x_notin_s,
  have t_sub_S : t ⊆ S, from insert_subset.mpr ⟨xS, s_sub_S⟩,
  have : coarsely_separated_with δ t,
  { rintros z (rfl | zs) y (rfl | ys),
    { exact λ h, (h rfl).elim },
    { exact λ hzy, H ys },
    { intro hzy,
      rw edist_comm,
      exact H zs },
    { exact s_sep zs ys }},
  exact s_ne_t (s_max t s_sub_t t_sub_S this),
end

end coarsely_dense_with_in

namespace coarsely_separated_with

/--
The set of all `δ`-separated subsets of `S`.
This is only used in the proof of `exists_max`.
-/
def all_with_in (δ : ℝ≥0) (S : set α) : set (set α) :=
{t : set α | t ⊆ S ∧ coarsely_separated_with δ t}

/--
A directed union of `δ`-separated subsets of a set `S` is a `δ`-separated
-/
lemma of_directed_union (δ : ℝ≥0) (S : set α) (𝒸 ⊆ all_with_in δ S) (dir : directed_on (⊆) 𝒸) :
  𝒸.sUnion ∈ all_with_in δ S :=
begin
  let 𝒞 := 𝒸.sUnion,
  have : 𝒞 ⊆ S, by
  { apply set.sUnion_subset ,
    rintros s s_in_𝒸,
    have : s ⊆ S, from (set.mem_of_subset_of_mem H s_in_𝒸).left,
    exact ‹s ⊆ S›,},
  have : coarsely_separated_with δ 𝒞, by
  { rintros x x_in_𝒞,
    rcases set.mem_sUnion.mp x_in_𝒞 with ⟨t,t_in_𝒸,x_in_t⟩,
    rintros y y_in_𝒞,
    rcases set.mem_sUnion.mp y_in_𝒞 with ⟨r,r_in_𝒸,y_in_r⟩,
    intro x_ne_y,
    rcases dir t t_in_𝒸 r r_in_𝒸 with ⟨s,s_in_𝒸,t_sub_s,r_sub_s⟩,
    have x_in_s : x ∈ s, from set.mem_of_subset_of_mem t_sub_s x_in_t,
    have y_in_s : y ∈ s, from set.mem_of_subset_of_mem r_sub_s y_in_r,
    let s_coarse := set.mem_of_subset_of_mem H s_in_𝒸,
    exact s_coarse.right x_in_s y_in_s x_ne_y,},
  exact ⟨‹𝒞 ⊆ S›, this⟩,
end

/--
A `⊆`-chain of `δ`-separated subsets of `S` has an upper bound.
-/
lemma chain_has_ub (δ : ℝ≥0) (S : set α) (𝒸 ⊆ all_with_in δ S) :
  zorn.chain has_subset.subset 𝒸 →
  ∃ (ub : set α) (H : ub ∈ all_with_in δ S), ∀ (s : set α), s ∈ 𝒸 → s ⊆ ub :=
begin
  intro 𝒸chain,
  let 𝒞 : set α := 𝒸.sUnion,
  have H' : 𝒞 ∈ all_with_in δ S, from of_directed_union δ S 𝒸 H 𝒸chain.directed_on,
  use [𝒞,H'],
  rintros s s_in_𝒸,
  exact set.subset_sUnion_of_mem s_in_𝒸,
end

/--
Given any `δ` and subset `S` of `α`, there exists a maximal `δ`-separated subset of `S`.
-/
theorem exists_max (δ : ℝ≥0) (S : set α) :
  ∃ s : set α, s ⊆ S
             ∧ coarsely_separated_with δ s
             ∧ (∀ t : set α, s ⊆ t → t ⊆ S →  coarsely_separated_with δ t → s = t) :=
begin
  let 𝒮 : set (set α) := all_with_in δ S,
  rcases zorn.zorn_subset 𝒮 (chain_has_ub δ S) with ⟨M,M_in_𝒮,M_max⟩,
  use [M,M_in_𝒮.left,M_in_𝒮.right],
  rintros t M_sub_t t_sub_S t_coarse,
  exact (M_max t ⟨t_sub_S, t_coarse⟩ M_sub_t).symm,
end

end coarsely_separated_with

/--
Given any `δ` and subset `S` of `α`, there exists a `δ`-separated and
`δ`-dense subset of `S`.
-/
theorem exists_coarsely_separated_coarsely_dense_with_in (δ : ℝ≥0) (S : set α) :
  ∃ s ⊆ S, coarsely_separated_with δ s
         ∧ coarsely_dense_with_in δ s S :=
begin
  rcases coarsely_separated_with.exists_max δ S with ⟨s, s_sub_S, s_sep, s_max_sep⟩,
  use [s,s_sub_S,s_sep],
  exact coarsely_dense_with_in.of_max_coarsely_separated_with_in ⟨s_sub_S, s_sep, s_max_sep⟩,
end
