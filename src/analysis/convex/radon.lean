import analysis.convex.combination
import data.finset.basic

open_locale big_operators

universes u
variables {𝕜 : Type*} {E : Type u} [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E]

lemma radon_lemma {ι} {p : ι → E} (hp : function.injective p) (h : ¬ affine_independent 𝕜 p) :
  ∃ (M₁ M₂ ⊆ set.range p), disjoint M₁ M₂ ∧ ¬ disjoint (convex_hull 𝕜 M₁) (convex_hull 𝕜 M₂) :=
begin
  rw affine_independent_def at h,
  push_neg at h,
  rcases h with ⟨M, f, hf, hf', a, ha, ha'⟩,
  haveI : decidable_pred (λ i : ι, 0 < f i) := by { classical, apply_instance },
  let I₁ := M.filter (λ i : ι, 0 < f i),
  let I₂ := M.filter (λ i : ι, ¬ 0 < f i),
  refine ⟨p '' I₁, set.image_subset_range p I₁, p '' I₂, set.image_subset_range p I₂, _, _⟩,
  { rw set.disjoint_iff_forall_ne,
    rintros _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ h,
    rw hp h at hi,
    exact (finset.mem_filter.1 hj).2 (finset.mem_filter.1 hi).2 },
  { rw set.not_disjoint_iff,
    let k := ∑ x in I₁, f x,
    have HI₁ : ∀ j, j ∈ I₁ → 0 < f j := λ j hj, (finset.mem_filter.1 hj).2,
    have HI₁' : ∀ j, j ∈ I₁ → 0 ≤ f j := λ j hj, (HI₁ j hj).le,
    have hk : 0 ≤ k := finset.sum_nonneg HI₁',
    have Hnn : ∀ j, j ∈ I₁ → 0 ≤ f j / k := λ i hi, div_nonneg (HI₁' i hi) hk,
    have HS : ∑ i in I₁, f i / k = 1,
    { rw ←finset.sum_div,
      refine div_self (ne_of_gt (finset.sum_pos HI₁ _)),
      { by_contra H,
        rw finset.not_nonempty_iff_eq_empty at H,
        sorry } },
    refine ⟨∑ x in I₁, (f x / k) • p x, _, _⟩,
    { rw [finset.coe_filter],
      exact convex.sum_mem (convex_convex_hull _ _) Hnn HS
        (λ i hi, subset_convex_hull _ _ ⟨i, finset.mem_filter.1 hi, rfl⟩) },
    { have HI₂ : ∀ j, j ∈ I₂ → f j ≤ 0 := λ j hj, le_of_not_lt $ (finset.mem_filter.1 hj).2,
      have HS₁₂ : ∑ x in I₁, (f x / k) • p x = ∑ x in I₂, (- f x / k) • p x := sorry,
      have HS₁₂' : ∑ x in I₁, f x / k = ∑ x in I₂, - f x / k := sorry,
      rw HS₁₂,
      refine convex.sum_mem (convex_convex_hull _ _) (λ i hi, div_nonneg (le_neg_of_le_neg _) hk) _
        (λ i hi, subset_convex_hull _ _ ⟨i, hi, rfl⟩),
      { rw neg_zero,
        exact HI₂ i hi },
      { rwa ←HS₁₂' } } }
end
