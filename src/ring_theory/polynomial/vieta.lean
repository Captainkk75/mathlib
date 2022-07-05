/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import ring_theory.polynomial.basic
import ring_theory.polynomial.symmetric

/-!
# Vieta's Formula

The main result is `multiset.prod_X_add_C_eq_sum_esymm`, which shows that the product of
linear terms ` X + λ` with `λ` in a `multiset s` is equal to a linear combination of the
symmetric functions `esymm s`.

From this, we deduce `mv_polynomial.prod_X_add_C_eq_sum_esymm` which is the equivalent formula
for the product of linear terms `X + X i` with `i` in a `fintype σ` as a linear combination
of the symmetric polynomials `esymm σ R j`.

-/

open_locale big_operators polynomial

variables {R : Type*} [comm_semiring R]

namespace multiset

/-- TODO. This should go elsewhere... -/
lemma sum_powerset_len {α : Type*} (S : multiset α) :
  S.powerset = ∑ k in finset.range(S.card + 1), (S.powerset_len k) :=
begin
  apply eq.symm,
  apply multiset.eq_of_le_of_card_le,
  { apply multiset.le_of_disjoint_sum_le,
    { exact λ _ _, multiset.powerset_len_le_powerset _ _, },
    { intros _ _ _ _ hxny _ htx hty,
      rw multiset.mem_powerset_len at htx,
      rw multiset.mem_powerset_len at hty,
      rw ←htx.right at hxny,
      rw hty.right at hxny,
      exact ne.irrefl hxny, }},
  { rw multiset.card_powerset,
    rw ( _ : card (∑ (k : ℕ) in finset.range (card S + 1), powerset_len k S)
      = ∑ (k : ℕ) in finset.range (card S + 1), card (powerset_len k S)),
    { conv_rhs { congr, skip, funext, rw multiset.card_powerset_len },
      apply eq.le,
      exact (nat.sum_range_choose S.card).symm, },
    exact map_sum card (λ (k : ℕ), multiset.powerset_len k S) (finset.range (S.card + 1))},
end

/-- A sum version of Vieta's formula for `multiset`: the product of the linear terms `X + λ` where
`λ` runs through a multiset `s` is equal to a linear combination of the symmetric functions
`esymm s` of the `λ`'s .-/
lemma prod_X_add_C_eq_sum_esymm (s : multiset R) :
  (s.map (λ r, polynomial.X + polynomial.C r)).prod =
  ∑ j in finset.range (s.card + 1), (polynomial.C (s.esymm j) * polynomial.X ^ (s.card - j)) :=
begin
  classical,
  rw [prod_map_add, antidiagonal_powerset, map_map, sum_powerset_len, function.comp,
    finset.sum_eq_multiset_sum, finset.sum_eq_multiset_sum, ←join, ←bind, map_bind, sum_bind],
  rw map_congr (eq.refl _),
  intros _ _,
  rw [esymm, ←sum_hom', ←sum_map_mul_right, map_congr (eq.refl _)],
  intros _ ht,
  rw mem_powerset_len at ht,
  simp [ht, map_const, prod_repeat, prod_hom', map_id', card_sub],
end

/-- Vieta's formula for the coefficients of the product of linear terms `X + λ` where `λ` runs
through a multiset `s` : the `k`th coefficient is the symmetric function `esymm (card s - k) s`. -/
lemma prod_X_add_C_coeff (s : multiset R) {k : ℕ} (h : k ≤ s.card):
  polynomial.coeff (s.map (λ r, polynomial.X + polynomial.C r)).prod k =
    s.esymm (s.card - k) :=
begin
  convert polynomial.ext_iff.mp (prod_X_add_C_eq_sum_esymm s) k,
  rw polynomial.finset_sum_coeff,
  conv_rhs { congr, skip, funext, rw polynomial.coeff_C_mul_X_pow },
  rw finset.sum_eq_single_of_mem (s.card - k) _,
  { rw if_pos (nat.sub_sub_self h).symm, },
  { intros l h1 h2,
    rw [finset.mem_range, nat.lt_succ_iff] at h1,
    have : k ≠ card s - l,
    { contrapose! h2,
      zify at h2 ⊢,
      rw [h2, sub_sub_cancel], },
    rw if_neg this },
  { rw finset.mem_range,
    exact nat.sub_lt_succ s.card k }
end

end multiset

namespace mv_polynomial

open finset polynomial fintype

variables (σ : Type*) [fintype σ]

/-- A sum version of Vieta's formula for `mv_polynomial`: viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
lemma prod_C_add_X_eq_sum_esymm :
  (∏ i : σ, (polynomial.X + polynomial.C (X i)) : polynomial (mv_polynomial σ R) )=
  ∑ j in range (card σ + 1),
    (polynomial.C (esymm σ R j) * polynomial.X ^ (card σ - j)) :=
begin
  set s :=  (multiset.map (λ i : σ, (X i : mv_polynomial σ R)) finset.univ.val),
  rw (_ : card σ = s.card),
  { conv_rhs { congr, skip, funext, rw esymm_eq_multiset.esymm σ R j},
    rw finset.prod_eq_multiset_prod,
    convert multiset.prod_X_add_C_eq_sum_esymm s,
    rw multiset.map_map, },
  { rw multiset.card_map, exact rfl, }
end

lemma prod_X_add_C_coeff (k : ℕ) (h : k ≤ card σ):
  (∏ i : σ, (polynomial.X + polynomial.C (X i)) : polynomial (mv_polynomial σ R) ).coeff k =
  esymm σ R (card σ - k) :=
begin
  set s :=  (multiset.map (λ i : σ, (X i : mv_polynomial σ R)) finset.univ.val),
  rw (_ : card σ = s.card) at ⊢ h,
  { rw esymm_eq_multiset.esymm σ R (s.card - k),
    rw finset.prod_eq_multiset_prod,
    convert multiset.prod_X_add_C_coeff s h,
    rw multiset.map_map },
  all_goals { rw multiset.card_map, exact rfl, },
end

end mv_polynomial
