/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.lp_space
import analysis.normed_space.pi_Lp

/-!
# Equivalences among $$L^p$$ spaces

In this file we collect a variety of equivalences among various $$L^p$$ spaces.  In particular,
when `α` is a `fintype`, given `E : α → Type u` and `p : ℝ≥0∞`, there is a natural linear isometric
equivalence `lp_pi_Lpₗᵢ : lp E p ≃ₗᵢ pi_Lp p E`.

We keep this as a separate file so that the various $$L^p$$ space files don't import the others.

## TODO

* Equivalence between `lp` and `measure_theory.Lp`, for `f : α → E` (i.e., functions rather than
  pi-types) and the counting measure on `α`
* Equivalence between `lp` and `bounded_continuous_function`, for `f : α → E` (i.e., functions
  rather than Π-types) and `p = ∞`, and the discrete topology on `α`

-/

open_locale ennreal

variables {α : Type*} [fintype α] {E : α → Type*} [Π i, normed_add_comm_group (E i)] (p : ℝ≥0∞)

/-- When `α` is a `fintype`, every `f : pre_lp E p` satisfies `mem_ℓp f p`. -/
lemma mem_ℓp.all (f : Π i, E i) : mem_ℓp f p :=
begin
  rcases p.trichotomy with (rfl | rfl | h),
  { exact mem_ℓp_zero_iff.mpr {i : α | f i ≠ 0}.to_finite, },
  { exact mem_ℓp_infty_iff.mpr (set.finite.bdd_above (set.range (λ (i : α), ∥f i∥)).to_finite) },
  { rw [mem_ℓp_gen_iff h, summable_iff_vanishing_norm],
    refine λ ε hε, ⟨finset.univ, λ s hs, _⟩,
    simp only [disjoint, finset.inf_eq_inter, finset.inter_univ, finset.bot_eq_empty,
      finset.le_eq_subset, finset.subset_empty] at hs,
    rwa [hs, finset.sum_empty, norm_zero], }
end

/-- The canonical `equiv` between `lp E p ≃ pi_Lp p E` when `E : α → Type u` with `[fintype α]`. -/
def equiv.lp_pi_Lp : lp E p ≃ pi_Lp p E :=
{ to_fun := λ f, f,
  inv_fun := λ f, ⟨f, mem_ℓp.all p f⟩,
  left_inv := λ f, lp.ext $ funext $ λ x, rfl,
  right_inv := λ f, funext $ λ x, rfl }

lemma equiv_lp_pi_Lp_norm (f : lp E p) : ∥equiv.lp_pi_Lp p f∥ = ∥f∥ :=
begin
  unfreezingI { rcases p.trichotomy with (rfl | rfl | h) },
  { rw [pi_Lp.norm_eq_card, lp.norm_eq_card_dsupport], refl },
  { rw [pi_Lp.norm_eq_csupr, lp.norm_eq_csupr], refl },
  { rw [pi_Lp.norm_eq_sum h, lp.norm_eq_tsum_rpow h, tsum_fintype], refl },
end

/-- The canonical `add_equiv` between `lp E p` and `pi_Lp p E` when `E : α → Type u` with
`[fintype α]` and `[fact (1 ≤ p)]`. -/
def add_equiv.lp_pi_Lp [fact (1 ≤ p)] : lp E p ≃+ pi_Lp p E :=
{ map_add' := λ f g, rfl,
  .. (equiv.lp_pi_Lp p) }

section equivₗᵢ
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [Π i, normed_space 𝕜 (E i)]

/-- The canonical `add_equiv` between `lp E p` and `pi_Lp p E` when `E : α → Type u` with
`[fintype α]` and `[fact (1 ≤ p)]`. -/
noncomputable def lp_pi_Lpₗᵢ [fact (1 ≤ p)] : lp E p ≃ₗᵢ[𝕜] pi_Lp p E :=
{ map_smul' := λ k f, rfl,
  norm_map' := equiv_lp_pi_Lp_norm p,
  .. (add_equiv.lp_pi_Lp p) }

end equivₗᵢ
