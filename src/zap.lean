/-
Copyright (c) 2022 X.-F. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: X-F. Roblot
-/

import number_theory.number_field
import analysis.complex.polynomial

section admit
namespace multiset

variables {R : Type*} [comm_ring R]

/-- import from PR15008 -/
def esymm (s : multiset R) (n : ℕ) : R := ((s.powerset_len n).map multiset.prod).sum

/-- import from PR15008 -/
lemma prod_X_sub_C_coeff (s : multiset R) {k : ℕ} (h : k ≤ s.card):
    polynomial.coeff (s.map (λ r, polynomial.X - polynomial.C r)).prod k =
    (-1)^k * s.esymm (s.card - k) :=
begin
  sorry,
end

end multiset
end admit

open set finite_dimensional complex
open_locale classical
open_locale big_operators
open_locale polynomial
open_locale nnreal

variables {K : Type*} [field K] [number_field K] {n : ℕ} (x : K)
open polynomial

noncomputable theory

example (s t : multiset ℝ) :
  s = t → s.prod = t.prod :=
begin
  exact congr_arg (λ (s : multiset ℝ), s.prod),
end

lemma bounded_coeffs_of_bounded_roots {p : ℂ[X]} {B : ℝ} (i : ℕ)
  (h0 : p.monic) (h1 : 0 ≤ B) (h2 : ∀ z ∈ p.roots, abs z ≤ B) :
  abs (p.coeff i) ≤ B^(p.nat_degree - i) * p.nat_degree.choose i  :=
begin
  have hsp : splits (ring_hom.id ℂ) p := is_alg_closed.splits_codomain p,
  have hcd :  multiset.card p.roots = p.nat_degree,
  { nth_rewrite 0 ←@polynomial.map_id ℂ _ p,
    exact (nat_degree_eq_card_roots hsp).symm, },
  by_cases hi : i ≤ p.nat_degree,
  { have hsp : splits (ring_hom.id ℂ) p := is_alg_closed.splits_codomain p,
    nth_rewrite 0 ←@polynomial.map_id ℂ _ p,
    rw eq_prod_roots_of_splits hsp,
    rw polynomial.map_id,
    rw ring_hom.id_apply,
    rw monic.def.mp h0,
    rw ring_hom.map_one,
    rw one_mul,
    rw multiset.prod_X_sub_C_coeff,
    swap, rwa hcd,
    rw [complex.abs_mul, (by norm_num : abs ((-1 : ℂ) ^ i) =  1), one_mul],
    apply le_trans (multiset.le_sum_of_subadditive complex.abs _ _ _ ),
    rotate, exact abs_zero, exact abs_add,
    rw multiset.map_map,
    suffices : ∀ r ∈ multiset.map (complex.abs ∘ multiset.prod)
      (multiset.powerset_len (multiset.card p.roots - i) p.roots), r ≤ B^(p.nat_degree - i),
    { convert multiset.sum_le_sum_sum _ this,
      simp only [hi, hcd, multiset.map_const, multiset.card_map, multiset.card_powerset_len,
        nat.choose_symm, multiset.sum_repeat, nsmul_eq_mul, mul_comm], },


    intros r hr,
    obtain ⟨t, ht⟩ := multiset.mem_map.mp hr,
    rw ←ht.right,
    lift B to ℝ≥0 using h1,
    lift (multiset.map complex.abs_hom t) to (multiset ℝ≥0) with t₀,
    swap,
    { intros x hx,
      obtain ⟨z, hz⟩ := multiset.mem_map.mp hx,
      rw ←hz.right,
      exact complex.abs_nonneg z, },
    have a1 : ∀ r ∈ t₀, r ≤ B,
    { intros r hr,
      have : (r : ℝ) ∈ multiset.map coe t₀, from multiset.mem_map_of_mem _ hr,
      rw h at this,
      obtain ⟨z, hz⟩ := multiset.mem_map.mp this,

      have : _, from multiset.mem_of_le (multiset.mem_powerset_len.mp ht.left).left hz.left,

      have : abs_hom z ≤ B, from h2 z this,
      simp only [*, nnreal.coe_le_coe] at *,
    },

    convert multiset.prod_le_sum_prod _ a1 using 1,
    { have : _, from congr_arg (λ (t : multiset ℝ), t.prod) h,
      rw multiset.prod_hom t complex.abs_hom at this,
      convert this.symm using 1,
      norm_cast, },
    { simp only [multiset.map_const, multiset.prod_repeat, nnreal.coe_pow, multiset.mem_powerset_len, function.comp_app,
  multiset.mem_map],
      congr,
      have : _, from congr_arg (λ (t : multiset ℝ), t.card) h,
      rw multiset.card_map at this,
      rw multiset.card_map at this,
      rw this,
      rw ←hcd,
      have : _, from multiset.mem_powerset_len.mp ht.left,
      exact this.right.symm, }},
  { push_neg at hi,
    rw [nat.choose_eq_zero_of_lt hi, coeff_eq_zero_of_nat_degree_lt, complex.abs_zero],
    rw_mod_cast mul_zero,
    { exact hi, }},
end
