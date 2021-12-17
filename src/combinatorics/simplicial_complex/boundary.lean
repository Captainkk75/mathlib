/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.link
import combinatorics.simplicial_complex.subdivision

/-!
# Boundary of a simplicial complex
-/

open finset geometry

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {K : simplicial_complex 𝕜 E}
  {s t : finset E} {A : set (finset E)} {n : ℕ}

def on_boundary (K : simplicial_complex 𝕜 E) (s : finset E) : Prop :=
s.nonempty ∧ ∃ t ∈ K.faces, s ⊂ t ∧ ∀ ⦃u⦄, u ∈ K.faces → s ⊂ u → t = u

def boundary (K : simplicial_complex 𝕜 E) : simplicial_complex 𝕜 E :=
K.of_subcomplex
  {s | s.nonempty ∧ ∃ t ∈ K.faces, s ⊆ t ∧ K.on_boundary t}
  (λ s ⟨hs, t, ht, hst, _⟩, K.down_closed ht hst hs)
  (λ s u ⟨hs, t, ht, hst, v⟩ hus hu, ⟨hu, t, ht, hus.trans hst, v⟩)

lemma boundary_le : K.boundary ≤ K := K.of_subcomplex_le _

lemma boundary_bot : (⊥ : simplicial_complex 𝕜 E).boundary = ⊥ := of_subcomplex_bot _

lemma mem_boundary_iff_subset_unique_facet :
  s ∈ K.boundary.faces ↔ s.nonempty ∧ ∃ (t ∈ K) (u ∈ K.facets), s ⊆ t ∧ t ⊂ u ∧
  ∀ ⦃v⦄, v ∈ K.faces → t ⊂ v → u = v :=
begin
  split,
  { rintro ⟨hs, t, ht, hst, ht', u, hu, htu, huunique⟩,
    exact ⟨hs, t, ht, u, ⟨hu, λ v hv huv, huunique hv ⟨htu.1.trans huv, λ hvt, htu.2 $
      huv.trans hvt⟩⟩, hst, htu, huunique⟩ },
  { rintro ⟨hs, t, ht, u, hu, hst, htu, huunique⟩,
    exact ⟨hs, t, ht, hst, K.nonempty ht, u, hu.1, htu, huunique⟩ }
end

lemma facets_disjoint_boundary : disjoint K.facets K.boundary.faces :=
begin
  rintro s ⟨⟨hs, hsunique⟩, hs, t, ht, hst, ht, u, hu, htu, huunique⟩,
  apply htu.2,
  rw ←hsunique hu (hst.trans  htu.1),
  exact hst,
end

lemma boundary_facet_iff : s ∈ K.boundary.facets ↔ K.on_boundary s :=
begin
  split,
  { rintro ⟨⟨hs, t, ht, hst, ht', u, hu, htu, huunique⟩, hsmax⟩,
    refine ⟨u, hu, finset.ssubset_of_subset_of_ssubset hst htu, _⟩,
    have hss' := hsmax ⟨K.nonempty ht, _, ht, subset.refl _, _, hu, htu, huunique⟩ st,
    subst hss',
    exact huunique },
  { rintro ⟨t, ht, hst, htunique⟩,
    refine ⟨⟨s, K.down_closed ht hst.1, subset.refl _, _, ht, hst, λ t', htunique⟩, _⟩,
    rintro V ⟨W, hW, hVW, u, hu, hWu, huunique⟩ hsV,
    apply finset.subset.antisymm hsV,
    classical,
    by_contra hVs,
    have := htunique (K.down_closed hW hVW) ⟨hsV, hVs⟩,
    subst this,
    have := htunique hu ⟨subset.trans hsV (subset.trans hVW hWu.1),
      λ hus, hWu.2 (subset.trans hus (subset.trans hsV hVW))⟩,
    subst this,
    exact hWu.2 hVW,
  }
end

lemma boundary_facet_iff' :
  s ∈ K.boundary.facets ↔ ∃ {t}, t ∈ K.facets ∧ s ⊂ t ∧ ∀ {t'}, t' ∈ K.faces → s ⊂ t' → t = t' :=
begin
  rw boundary_facet_iff,
  split,
  { rintro ⟨t, ht, hst, htunique⟩,
    have ht' : t ∈ K.facets,
    { use ht,
      rintro t' ht' htt',
      exact htunique ht' (finset.ssubset_of_ssubset_of_subset hst htt'),
    },
    exact ⟨t, ht', hst, (λ t', htunique)⟩ },
  { rintro ⟨t, ht, hst, htunique⟩,
    exact ⟨t, ht.1, hst, (λ t', htunique)⟩ }
end

lemma pure_boundary_of_pure (hK : K.pure n) : K.boundary.pure (n - 1) :=
begin
  rintro s hs,
  obtain ⟨t, ht, hst, htunique⟩ := boundary_facet_iff'.1 hs,
  cases n,
  { apply nat.eq_zero_of_le_zero,
    have htcard : t.card = 0 := hK ht,
    rw ←htcard,
    exact le_of_lt (finset.card_lt_card hst) },
  have htcard : t.card = n.succ := hK ht,
  have hscard : s.card ≤ n,
  { have := finset.card_lt_card hst,
    rw htcard at this,
    exact nat.le_of_lt_succ this },
  have : n - s.card + s.card ≤ t.card,
  { rw [hK ht, nat.sub_add_cancel hscard, nat.succ_eq_add_one],
    linarith },
  obtain ⟨W, hsW, hWt, hWcard⟩ := finset.exists_intermediate_set (n - s.card) this hst.1,
  rw nat.sub_add_cancel hscard at hWcard,
  have hW : W ∈ K.boundary.faces,
  { have htW : ¬t ⊆ W,
    { have hWtcard : W.card < t.card,
      { rw [hWcard, hK ht, nat.succ_eq_add_one],
        linarith },rintro htW,
      have : n.succ = n := by rw [← hK ht, ← hWcard,
        finset.eq_of_subset_of_card_le htW (le_of_lt hWtcard)],
      exact nat.succ_ne_self n this },
    refine ⟨W, K.down_closed (facets_subset ht) hWt, subset.refl W, t, ht.1, ⟨hWt, htW⟩, _⟩,
    rintro u hu hWu,
    exact htunique hu ⟨subset.trans hsW hWu.1, (λ hus, hWu.2 (finset.subset.trans hus hsW))⟩ },
  rw [nat.succ_sub_one, ←hWcard, hs.2 hW hsW],
end

lemma link_boundary : K.boundary.link A = (K.link A).boundary :=
begin
  ext V,
  split,
  { rintro ⟨hVdisj, W, s, hW, ⟨t, u, ht, hu, hst, htu, huunique⟩, hVs, hWs⟩,
    use V,
    split,
    { sorry
      /-split,
      exact (λ U hU, hVdisj hU),
      exact ⟨W, u, hW, facets_subset hu, subset.trans hVs (subset.trans hst htu.1),
        subset.trans hWs (subset.trans hst htu.1)⟩,-/
    },
    { /-use subset.refl V,
      use u,
      split,
      { sorry --waiting for link_facet_iff. May make this lemma require more assumptions
      },
      use ⟨finset.subset.trans hVs (finset.subset.trans hst htu.1),
        (λ huV, htu.2 (finset.subset.trans huV (finset.subset.trans hVs hst)))⟩,
      rintro U ⟨hUdisj, T, R, hT, hR, hUR, hTR⟩ hVU,
      apply huunique (K.down_closed hR hUR),-/
      sorry
    }
  },
  { sorry
  }
end

lemma boundary_boundary [finite_dimensional 𝕜 E] (hK : K.pure_of n) (hK' : ∀ {s}, s ∈ K.faces →
  (s : finset E).card = n - 1 → equiv {t | t ∈ K.faces ∧ s ⊆ t} (fin 2)) :
  K.boundary.boundary.faces = ∅ :=
begin
  rw ← facets_empty_iff_faces_empty,
  apply eq_empty_of_subset_empty,
  rintro V hV,
  obtain ⟨W, hW, hVW, hWunique⟩ := boundary_facet_iff'.1 hV,
  obtain ⟨s, hs, hsV, hsunique⟩ := boundary_facet_iff'.1 hW,
  sorry
end

lemma boundary_mono {K₁ K₂ : simplicial_complex 𝕜 E} (hK : K₁ ≤ K₂) : K₁.boundary ≤ K₂.boundary :=
begin
  /-cases K₂.faces.eq_empty_or_nonempty with hK₂empty hK₂nonempty,
  { rw hK₂empty,
  },
  rw subdivision_iff_partition at ⊢ hK,-/
  have hspace : K₁.boundary.space = K₂.boundary.space,
  { sorry
  },
  /-rw subdivision_iff_partition,
  split,
  { sorry
  },
  use le_of_eq hspace,
  rintro s₂ ⟨t₂, u₂, ht₂, hu₂, hs₂t₂, ht₂u₂, hu₂max⟩,
  obtain ⟨hempty, hspace, hpartition⟩ := subdivision_iff_partition.1 hK,
  obtain ⟨F, hF, hs₂F⟩ := hpartition (K₂.down_closed ht₂ hs₂t₂),
  use F, rw and.comm, use hs₂F,
  rintro s₁ hs₁,-/

  use hspace,
  rintro s₁ ⟨t₁, ht₁, hs₁t₁, u₁, hu₁, ht₁u₁, hu₁max⟩,
  cases s₁.eq_empty_or_nonempty with hs₁empty hs₁nonempty,
  { sorry},
  obtain ⟨s₂, hs₂, hs₁s₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hK).2
    (K₁.down_closed ht₁ hs₁t₁),
  obtain ⟨t₂, ht₂, ht₁t₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hK).2 ht₁,
  obtain ⟨u₂, hu₂, hu₁u₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hK).2 hu₁,
  obtain ⟨x, hxs₁⟩ := id hs₁nonempty,
  refine ⟨s₂, ⟨t₂, ht₂, _, u₂, hu₂, ⟨_, _⟩⟩,
    convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior
    (K₁.indep (K₁.down_closed ht₁ hs₁t₁)) (K₂.indep hs₂) hs₁s₂⟩,
  { apply subset_of_combi_interior_inter_convex_hull_nonempty hs₂ ht₂,
    obtain ⟨x, hxs₁⟩ := nonempty_combi_interior_of_nonempty (K₁.indep (K₁.down_closed ht₁ hs₁t₁))
      hs₁nonempty,
    use [x, hs₁s₂ hxs₁],
    apply convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior (K₁.indep ht₁)
      (K₂.indep ht₂) ht₁t₂,
    exact convex_hull_mono hs₁t₁ hxs₁.1 },
  { obtain ⟨y, hyt₁⟩ := nonempty_combi_interior_of_nonempty (K₁.indep ht₁) ⟨x, hs₁t₁ hxs₁⟩,
    split,
    { apply subset_of_combi_interior_inter_convex_hull_nonempty ht₂ hu₂,
      use [y, ht₁t₂ hyt₁],
      apply convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior (K₁.indep hu₁)
        (K₂.indep hu₂) hu₁u₂,
      exact convex_hull_mono ht₁u₁.1 hyt₁.1 },
    { rintro hu₂t₂,
      suffices ht₂u₂ : ¬t₂ ⊆ u₂,
      { apply (ht₁t₂ hyt₁).2,
        rw mem_combi_frontier_iff,
        use [u₂, ⟨hu₂t₂, ht₂u₂⟩],
        apply convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior (K₁.indep hu₁)
          (K₂.indep hu₂) hu₁u₂,
        exact convex_hull_mono ht₁u₁.1 hyt₁.1 },
      rintro ht₂u₂,
      have := finset.subset.antisymm ht₂u₂ hu₂t₂,
      subst this,
      suffices h : t₁.card = t₂.card,
      { have := finset.card_lt_card ht₁u₁,
        have := card_le_of_convex_hull_subset (K₁.indep hu₁)
          (convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior (K₁.indep hu₁)
          (K₂.indep ht₂) hu₁u₂),
        linarith },

      sorry
    },
  },
  { rintro v hv ht₂v,
    suffices hu₁v : combi_interior u₁ ⊆ combi_interior v,
    {   obtain ⟨z, hzu₁⟩ := nonempty_combi_interior_of_nonempty (K₁.indep hu₁)
        ⟨x, ht₁u₁.1 (hs₁t₁ hxs₁)⟩,
      exact disjoint_interiors hu₂ hv (hu₁u₂ hzu₁) (hu₁v hzu₁),
    },

    sorry
  }
end

--other attempt using subdivision_iff_partition
lemma boundary_mono' {K₁ K₂ : simplicial_complex 𝕜 E} (hK : K₁ ≤ K₂) :
  K₁.boundary ≤ K₂.boundary :=
begin
  rw subdivision_iff_partition,
  obtain ⟨hempty, hspace, hpartition⟩ := subdivision_iff_partition.1 hK,
  split,
  sorry,
  split,
  sorry,
  rintro s₂ hs₂,--rintro s₂ ⟨t₂, ht₂, hs₂t₂, u₂, hu₂, ht₂u₂, hu₂max⟩,
  obtain ⟨F, hF, hsF⟩ := hpartition (boundary_subset hs₂),
  --obtain ⟨F, hF, hsF⟩ := hpartition (K₂.down_closed ht₂ hs₂t₂),
  use F,
  rw and.comm,
  use hsF,
  rintro s₁ hs₁,
  have hs₁s₂ : combi_interior s₁ ⊆ combi_interior s₂,
  { rw hsF,
    exact subset_bUnion_of_mem hs₁ },
  sorry
end

/--
A m-simplex is on the boundary of a full dimensional complex iff it belongs to exactly one cell.
Dull?
-/
lemma boundary_subcell_iff_one_surface (hK : K.full_dimensional)
  (hscard : s.card = finite_dimensional.finrank 𝕜 E) :
  s ∈ K.boundary.faces ↔ nat.card {t | t ∈ K.faces ∧ s ⊂ t} = 1 :=
  -- It's probably a bad idea to use `nat.card` since it's incredibly underdeveloped for doing
  -- actual maths in
  -- Does this lemma need you to assume locally finite (at s)? If so, the set you care about is a
  -- subset of the set we know is finite, so we can convert to a finset and use normal card
begin
  split,
  { rintro ⟨t, ht, hst, u, hu, htu, huunique⟩,
    have : s = t,
    {   sorry
    },
    sorry--rw nat.card_eq_fintype_card,
  },
  -- have aux_lemma : ∀ {a b : E}, a ≠ b → a ∉ s → b ∉ s → s ∪ {a} ∈ K.faces → s ∪ {b} ∈ K.faces →
  --   ∃ w : E → 𝕜, w a < 0 ∧ ∑ y in s ∪ {a}, w y = 1 ∧ (s ∪ {a}).center_mass w id = b,
  -- {
  --   sorry
  -- },
  sorry
end

/--
A m-simplex is not on the boundary of a full dimensional complex iff it belongs to exactly two
cells.
-/
lemma not_boundary_subcell_iff_two_surfaces (hK : K.full_dimensional)
  (hscard : s.card = finite_dimensional.finrank 𝕜 E) :
  s ∉ K.boundary.faces ↔ nat.card {t | t ∈ K.faces ∧ s ⊂ t} = 2 :=
  -- It's probably a bad idea to use `nat.card` since it's incredibly underdeveloped for doing
  -- actual maths in
  -- Does this lemma need you to assume locally finite (at s)? If so, the set you care about is a
  -- subset of the set we know is finite, so we can convert to a finset and use normal card
begin
  -- have aux_lemma : ∀ {a b : E}, a ≠ b → a ∉ s → b ∉ s → s ∪ {a} ∈ K.faces → s ∪ {b} ∈ K.faces →
  --   ∃ w : E → 𝕜, w a < 0 ∧ ∑ y in s ∪ {a}, w y = 1 ∧ (s ∪ {a}).center_mass w id = b,
  -- {
  --   sorry
  -- },
  sorry
end

end affine
