/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.instances.irrational
import topology.algebra.order.archimedean
import topology.paracompact
import data.set.intervals.monotone

/-!
-/

open set filter topological_space
open_locale topological_space filter
noncomputable theory

@[derive [conditionally_complete_linear_order, linear_ordered_field, archimedean]]
def sorgenfrey_line : Type := ℝ

notation `ℝₗ` := sorgenfrey_line

namespace sorgenfrey_line

def to_real : ℝₗ ≃+* ℝ := ring_equiv.refl ℝ

instance : topological_space ℝₗ :=
topological_space.generate_from {s : set ℝₗ | ∃ a b : ℝₗ, Ico a b = s}

lemma is_open_Ico (a b : ℝₗ) : is_open (Ico a b) :=
topological_space.generate_open.basic _ ⟨a, b, rfl⟩

lemma is_open_Ici (a : ℝₗ) : is_open (Ici a) :=
Union_Ico_right a ▸ is_open_Union (is_open_Ico a)

lemma nhds_basis_Ico (a : ℝₗ) : (𝓝 a).has_basis ((<) a) (Ico a) :=
begin
  rw topological_space.nhds_generate_from,
  haveI : nonempty {x // x ≤ a} := set.nonempty_Iic_subtype,
  have : (⨅ (x : {i // i ≤ a}), 𝓟 (Ici ↑x)) = 𝓟 (Ici a),
  { refine (is_least.is_glb _).infi_eq,
    exact ⟨⟨⟨a, le_rfl⟩, rfl⟩, forall_range_iff.2 $
      λ b, principal_mono.2 $ Ici_subset_Ici.2 b.2⟩, },
  simp only [mem_set_of_eq, infi_and, infi_exists, @infi_comm _ (_ ∈ _),
    @infi_comm _ (set ℝₗ), infi_infi_eq_right],
  simp_rw [@infi_comm _ ℝₗ (_ ≤ _), infi_subtype', ← Ici_inter_Iio, ← inf_principal, ← inf_infi,
    ← infi_inf, this, infi_subtype],
  suffices : (⨅ x ∈ Ioi a, 𝓟 (Iio x)).has_basis ((<) a) Iio, from this.principal_inf _,
  refine has_basis_binfi_principal _ nonempty_Ioi,
  exact directed_on_iff_directed.2 (directed_of_inf $ λ x y hxy, Iio_subset_Iio hxy),
end

lemma nhds_basis_Ico_rat (a : ℝₗ) :
  (𝓝 a).has_countable_basis (λ r : ℚ, a < r) (λ r, Ico a r) :=
begin
  refine ⟨(nhds_basis_Ico a).to_has_basis (λ b hb, _) (λ r hr, ⟨_, hr, subset.rfl⟩),
    countable_encodable _⟩,
  rcases exists_rat_btwn hb with ⟨r, har, hrb⟩,
  exact ⟨r, har, Ico_subset_Ico_right hrb.le⟩
end

lemma nhds_basis_Ico_inv_nat_pos (a : ℝₗ) :
  (𝓝 a).has_countable_basis (λ n : ℕ, 0 < n) (λ n, Ico a (a + 1 / n)) :=
begin
  refine ⟨(nhds_basis_Ico a).to_has_basis (λ b hb, _)
    (λ n hn, ⟨_, lt_add_of_pos_right _ (one_div_pos.2 $ nat.cast_pos.2 hn), subset.rfl⟩),
    countable_encodable _⟩,
  rcases exists_nat_one_div_lt (sub_pos.2 hb) with ⟨k, hk⟩,
  rw [← nat.cast_add_one] at hk,
  exact ⟨k + 1, k.succ_pos, Ico_subset_Ico_right (le_sub_iff_add_le'.1 hk.le)⟩
end

lemma is_open_iff {s : set ℝₗ} : is_open s ↔ ∀ x ∈ s, ∃ y > x, Ico x y ⊆ s :=
is_open_iff_mem_nhds.trans $ forall₂_congr $ λ x hx, (nhds_basis_Ico x).mem_iff

lemma is_closed_iff {s : set ℝₗ} : is_closed s ↔ ∀ x ∉ s, ∃ y > x, disjoint (Ico x y) s :=
by simp only [← is_open_compl_iff, is_open_iff, mem_compl_iff, subset_compl_iff_disjoint,
  disjoint_iff_inter_eq_empty]

lemma exists_Ico_disjoint_closed {a : ℝₗ} {s : set ℝₗ} (hs : is_closed s) (ha : a ∉ s) :
  ∃ b > a, disjoint (Ico a b) s :=
is_closed_iff.1 hs a ha

@[simp] lemma map_to_real_nhds (a : ℝₗ) : map to_real (𝓝 a) = 𝓝[≥] (to_real a) :=
begin
  refine ((nhds_basis_Ico a).map _).eq_of_same_basis _,
  simpa only [to_real.image_eq_preimage] using nhds_within_Ici_basis_Ico (to_real a)
end

lemma nhds_eq_map (a : ℝₗ) : 𝓝 a = map to_real.symm (𝓝[≥] a.to_real) :=
by simp_rw [← map_to_real_nhds, map_map, (∘), to_real.symm_apply_apply, map_id']

lemma nhds_eq_comap (a : ℝₗ) : 𝓝 a = comap to_real (𝓝[≥] a.to_real) :=
by rw [← map_to_real_nhds, comap_map to_real.injective]

@[continuity] lemma continuous_to_real : continuous to_real :=
continuous_iff_continuous_at.2 $ λ x,
  by { rw [continuous_at, tendsto, map_to_real_nhds], exact inf_le_left }

instance : order_closed_topology ℝₗ :=
⟨is_closed_le_prod.preimage (continuous_to_real.prod_map continuous_to_real)⟩

instance : has_continuous_add ℝₗ :=
begin
  refine ⟨continuous_iff_continuous_at.2 _⟩,
  rintro ⟨x, y⟩,
  simp only [continuous_at, nhds_prod_eq, nhds_eq_map, nhds_eq_comap (x + y), prod_map_map_eq,
    tendsto_comap_iff, tendsto_map'_iff, (∘), ← nhds_within_prod_eq],
  exact (continuous_add.tendsto _).inf (maps_to.tendsto $ λ x hx, add_le_add hx.1 hx.2)
end

lemma is_clopen_Ici (a : ℝₗ) : is_clopen (Ici a) := ⟨is_open_Ici a, is_closed_Ici⟩

lemma is_clopen_Iio (a : ℝₗ) : is_clopen (Iio a) :=
by simpa only [compl_Ici] using (is_clopen_Ici a).compl

lemma is_clopen_Ico (a b : ℝₗ) : is_clopen (Ico a b) :=
(is_clopen_Ici a).inter (is_clopen_Iio b)

instance : totally_disconnected_space ℝₗ :=
begin
  refine ⟨λ s hs' hs x hx y hy, _⟩, clear hs',
  by_contra' hne : x ≠ y,
  wlog hlt : x < y := hne.lt_or_lt using [x y, y x],
  exact hlt.not_le (hs.subset_clopen (is_clopen_Ici y) ⟨y, hy, le_rfl⟩ hx)
end

instance : first_countable_topology ℝₗ := ⟨λ x, (nhds_basis_Ico_rat x).is_countably_generated⟩

instance : normal_space ℝₗ :=
begin
  refine ⟨λ s t hs ht hd, _⟩,
  choose! X hX hXd using λ x (hx : x ∈ s), exists_Ico_disjoint_closed ht (disjoint_left.1 hd hx),
  choose! Y hY hYd using λ y (hy : y ∈ t), exists_Ico_disjoint_closed hs (disjoint_right.1 hd hy),
  refine ⟨⋃ x ∈ s, Ico x (X x), ⋃ y ∈ t, Ico y (Y y), is_open_bUnion $ λ _ _, is_open_Ico _ _,
    is_open_bUnion $ λ _ _, is_open_Ico _ _, _, _, _⟩,
  { exact λ x hx, mem_Union₂.2 ⟨x, hx, left_mem_Ico.2 $ hX x hx⟩ },
  { exact λ y hy, mem_Union₂.2 ⟨y, hy, left_mem_Ico.2 $ hY y hy⟩ },
  { simp only [disjoint_Union_left, disjoint_Union_right, Ico_disjoint_Ico],
    intros y hy x hx,
    clear hs ht hd hX hY,
    cases le_total x y with hle hle,
    { calc min (X x) (Y y) ≤ X x : min_le_left _ _
      ... ≤ y : not_lt.1 (λ hyx, hXd x hx ⟨⟨hle, hyx⟩, hy⟩)
      ... ≤ max x y : le_max_right _ _ },
    { calc min (X x) (Y y) ≤ Y y : min_le_right _ _
      ... ≤ x : not_lt.1 $ λ hxy, hYd y hy ⟨⟨hle, hxy⟩, hx⟩
      ... ≤ max x y : le_max_left _ _ } }
end

lemma dense_range_coe_rat : dense_range (coe : ℚ → ℝₗ) :=
begin
  refine dense_iff_inter_open.2 _,
  rintro U Uo ⟨x, hx⟩,
  rcases is_open_iff.1 Uo _ hx with ⟨y, hxy, hU⟩,
  rcases exists_rat_btwn hxy with ⟨z, hxz, hzy⟩,
  exact ⟨z, hU ⟨hxz.le, hzy⟩, mem_range_self _⟩
end

instance : separable_space ℝₗ := ⟨⟨_, countable_range _, dense_range_coe_rat⟩⟩

instance : paracompact_space ℝₗ :=
begin
  refine ⟨λ α s ho hc, _⟩,
  rw Union_eq_univ_iff at hc,
  choose i hi using hc,
  
end

lemma is_closed_antidiagonal (c : ℝₗ) : is_closed {x : ℝₗ × ℝₗ | x.1 + x.2 = c} :=
is_closed_singleton.preimage continuous_add

lemma is_clopen_Ici_prod (x : ℝₗ × ℝₗ) : is_clopen (Ici x) :=
(Ici_prod_eq x).symm ▸ (is_clopen_Ici _).prod (is_clopen_Ici _)

lemma is_closed_of_subset_antidiagonal {s : set (ℝₗ × ℝₗ)} {c : ℝₗ}
  (hs : ∀ x ∈ s, (x : _).1 + x.2 = c) : is_closed s :=
begin
  rw [← closure_subset_iff_is_closed],
  rintro ⟨x, y⟩ H,
  obtain rfl : x + y = c,
  { change (x, y) ∈ {p : ℝₗ × ℝₗ | p.1 + p.2 = c},
    exact closure_minimal (hs : s ⊆ {x | x.1 + x.2 = c}) (is_closed_antidiagonal c) H },
  rcases mem_closure_iff.1 H (Ici (x, y)) (is_clopen_Ici_prod _).1 le_rfl
    with ⟨⟨x', y'⟩, ⟨hx : x ≤ x', hy : y ≤ y'⟩, H⟩,
  convert H,
  { refine hx.antisymm _,
    rwa [← add_le_add_iff_right, hs _ H, add_le_add_iff_left] },
  { refine hy.antisymm _,
    rwa [← add_le_add_iff_left, hs _ H, add_le_add_iff_right] }
end

lemma not_normal_space_prod : ¬normal_space (ℝₗ × ℝₗ) :=
begin
  introI,
  set S := {x : ℝₗ × ℝₗ | x.1 + x.2 = 0 ∧ ∃ r : ℚ, ↑r = x.1},
  set T := {x : ℝₗ × ℝₗ | x.1 + x.2 = 0 ∧ irrational x.1.to_real},
  have hSc : is_closed S, from is_closed_of_subset_antidiagonal (λ x hx, hx.1),
  have hTc : is_closed T, from is_closed_of_subset_antidiagonal (λ x hx, hx.1),
  have hd : disjoint S T,
  { rintro ⟨x, y⟩ ⟨⟨-, r, rfl : _ = x⟩, -, hr⟩,
    exact r.not_irrational hr },
  rcases normal_separation hSc hTc hd with ⟨U, V, Uo, Vo, SU, TV, UV⟩,
  have : ∀ x : ℝₗ, irrational x.to_real →
    ∃ k : ℕ, 0 < k ∧ Ico x (x + 1 / k) ×ˢ Ico (-x) (-x + 1 / k) ⊆ V,
  { intros x hx,
    have hV : V ∈ 𝓝 (x, -x), from Vo.mem_nhds (@TV (x, -x) ⟨add_neg_self x, hx⟩),
    have := λ y, (nhds_basis_Ico_inv_nat_pos y).to_has_basis,
    rcases ((this _).prod_nhds (this _)).mem_iff.1 hV with ⟨⟨k, l⟩, ⟨hk₀, hl₀⟩, H⟩,
    refine ⟨max k l, lt_max_iff.2 (or.inl hk₀),
      (set.prod_mono (Ico_subset_Ico_right _) (Ico_subset_Ico_right _)).trans H⟩,
    { exact add_le_add_left
        (one_div_le_one_div_of_le (nat.cast_pos.2 hk₀) $ nat.mono_cast $ le_max_left _ _) _ },
    { exact add_le_add_left
        (one_div_le_one_div_of_le (nat.cast_pos.2 hl₀) $ nat.mono_cast $ le_max_right _ _) _ } },
  choose! k hk₀ hkV,
  have H : {x : ℝ | irrational x} ⊆ ⋃ n ∈ {n : ℕ | 0 < n}, closure {x | k (to_real.symm x) = n},
    from λ x hx, mem_bUnion (hk₀ (to_real.symm x) hx) (subset_closure rfl),
  have Hd : dense (⋃ n ∈ {n : ℕ | 0 < n}, interior (closure {x | k (to_real.symm x) = n})),
    from is_Gδ_irrational.dense_bUnion_interior_of_closed dense_irrational
      (countable_encodable {n : ℕ | 0 < n}) (λ _ _, is_closed_closure) H,
  obtain ⟨N, hN₀, hN⟩ :
    ∃ n : ℕ, 0 < n ∧ (interior $ closure {x | k (to_real.symm x) = n}).nonempty,
    by simpa only [nonempty_Union, exists_prop] using Hd.nonempty,
  rcases rat.dense_range_cast.exists_mem_open is_open_interior hN with ⟨r, hr⟩,
  
end

end sorgenfrey_line
