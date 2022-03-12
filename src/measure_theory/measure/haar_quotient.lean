/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/

import measure_theory.measure.haar
import measure_theory.group.fundamental_domain
import topology.compact_open
import algebra.group.opposite

/-!
# Haar quotient measure

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup of a group `G` on `G` itself.

## Main results

* `measure_theory.is_fundamental_domain.smul_invariant_measure_map `: given a subgroup `Γ` of a
  topological group `G`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both
  left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure
  on `G ⧸ Γ`.

* `measure_theory.is_fundamental_domain.is_mul_left_invariant_map `: given a normal subgroup `Γ` of
  a topological group `G`, the pushforward to the quotient group `G ⧸ Γ` of the restriction of
  a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a left-invariant
  measure on `G ⧸ Γ`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
-/


lemma measure_theory.integral_tsum {α : Type*} {β : Type*} {m : measurable_space α}
  {μ : measure_theory.measure α} [encodable β] {E : Type*} [normed_group E] [normed_space ℝ E]
  [measurable_space E] [borel_space E] [complete_space E]
  [topological_space.second_countable_topology E] {f : β → α → E}
  (hf : ∀ (i : β), measurable (f i)) :
∫ (a : α), (∑' (i : β), f i a) ∂μ = ∑' (i : β), ∫ (a : α), f i a ∂μ :=
begin
  sorry,
end

open_locale ennreal

open measure_theory

lemma integrable.mul_ℒ_infinity  {G : Type*} {E : Type*} [normed_ring E] [normed_algebra ℝ E]
  [measurable_space E] [measurable_space G] {μ : measure G}
  (f : G → E)
  (f_measurable : measurable f)
  (g : G → E)
  (g_measurable : measurable g)
  (g_ℒ_infinity : mem_ℒp g ⊤ μ)
  (f_ℒ_1 : integrable f μ) :
  integrable (λ (x : G), f x * g x) μ :=
begin
  have ess_sup_bdd_by_bigger : ∀ (a:ennreal), ess_sup (λ x, ↑∥g x∥₊) μ < a →
    (λ x, ↑∥g x∥₊) ≤ᵐ[μ] (λ x, a),
  {
    intros a ha,
    sorry,

  },

  have : ess_sup (λ x, ↑∥g x∥₊) μ < ∞,
  {
    sorry,
  },
  obtain ⟨B, hB⟩ : ∃ B : nnreal, ess_sup (λ x, (∥g x∥₊:ennreal)) μ = B,
  {
    sorry,
  },

  have := ess_sup_bdd_by_bigger (B+1) _,

  rw integrable at f_ℒ_1 ⊢,

  rw measure_theory.has_finite_integral_iff_norm at f_ℒ_1 ⊢,

  split,
  {
    -- product of measurables is measurable
    sorry,
  },
  {
    calc ∫⁻ (x : G), ennreal.of_real (∥f x * g x∥) ∂μ ≤
      ∫⁻ (x : G), ennreal.of_real (∥f x∥ * ∥g x∥) ∂μ : _
      ... ≤  ∫⁻ (x : G), ennreal.of_real (∥f x∥ * (B+1)) ∂μ : _
      ... =  ∫⁻ (x : G), (ennreal.of_real (∥f x∥) * (B+1)) ∂μ : _
      ... = ∫⁻ (x : G), ennreal.of_real (∥f x∥) ∂μ * (B+1) : _
      ... < ⊤ : _ ,

    { mono,
      { exact rfl.le, },
      { intros x,
        apply ennreal.of_real_le_of_real,
        exact norm_mul_le _ _, }, },
    { apply measure_theory.lintegral_mono_ae,
      filter_upwards [this],
      intros x hx,
      apply ennreal.of_real_le_of_real,
      norm_cast at hx,
      refine mul_le_mul _ hx  _ _,
      refl,
      exact norm_nonneg _,
      exact norm_nonneg _, },
    {
      congr,
      ext1 x,
      rw ennreal.of_real_mul,
      repeat {sorry}, -- ALEX HOMEWORK
    },
    {
      refine measure_theory.lintegral_mul_const _ _,
      sorry, -- ∥ f ∥ is measurable
    },
    { apply ennreal.mul_lt_top f_ℒ_1.2.ne,
      simp, },

  },
  {
    norm_cast,
    rw hB,
    norm_cast,
    sorry, --ALEX HOMEWORK
  --  have := ennreal.add_lt_add,
  --  linarith,
  }

end

open set measure_theory topological_space

variables {G : Type*} [group G] [measurable_space G] [topological_space G]
  [topological_group G] [borel_space G]
  (μ : measure G)
  (Γ : subgroup G)

/-- Given a subgroup `Γ` of `G` and a right invariant measure `μ` on `G`, the measure is also
  invariant under the action of `Γ` on `G` by **right** multiplication. -/
@[to_additive "Given a subgroup `Γ` of an additive group `G` and a right invariant measure `μ` on
  `G`, the measure is also invariant under the action of `Γ` on `G` by **right** addition."]
instance subgroup.smul_invariant_measure [μ.is_mul_right_invariant] :
  smul_invariant_measure Γ.opposite G μ :=
{ measure_preimage_smul :=
begin
  rintros ⟨c, hc⟩ s hs,
  dsimp [(•)],
  refine measure_preimage_mul_right μ (mul_opposite.unop c) s,
end}

variables {Γ} {μ}

/-- Measurability of the action of the topological group `G` on the left-coset space `G/Γ`. -/
@[to_additive "Measurability of the action of the additive topological group `G` on the left-coset
  space `G/Γ`."]
instance quotient_group.has_measurable_smul [measurable_space (G ⧸ Γ)] [borel_space (G ⧸ Γ)] :
  has_measurable_smul G (G ⧸ Γ) :=
{ measurable_const_smul := λ g, (continuous_const_smul g).measurable,
  measurable_smul_const := λ x, (quotient_group.continuous_smul₁ x).measurable }

variables {𝓕 : set G} (h𝓕 : is_fundamental_domain Γ.opposite 𝓕 μ)
include h𝓕

/-- If `𝓕` is a fundamental domain for the action by right multiplication of a subgroup `Γ` of a
  topological group `G`, then its left-translate by an element of `g` is also a fundamental
  domain. -/
@[to_additive "If `𝓕` is a fundamental domain for the action by right addition of a subgroup `Γ`
  of an additive topological group `G`, then its left-translate by an element of `g` is also a
  fundamental domain."]
lemma measure_theory.is_fundamental_domain.smul (g : G) [μ.is_mul_left_invariant] :
  is_fundamental_domain ↥Γ.opposite (has_mul.mul g ⁻¹' 𝓕) μ :=
{ measurable_set := measurable_set_preimage (measurable_const_mul g) (h𝓕.measurable_set),
  ae_covers := begin
    let s := {x : G | ¬∃ (γ : ↥(Γ.opposite)), γ • x ∈ 𝓕},
    have μs_eq_zero : μ s = 0 := h𝓕.2,
    change μ {x : G | ¬∃ (γ : ↥(Γ.opposite)), g * γ • x ∈ 𝓕} = 0,
    have : {x : G | ¬∃ (γ : ↥(Γ.opposite)), g * γ • x ∈ 𝓕} = has_mul.mul g ⁻¹' s,
    { ext,
      simp [s, subgroup.smul_opposite_mul], },
    rw [this, measure_preimage_mul μ g s, μs_eq_zero],
  end,
  ae_disjoint := begin
    intros γ γ_ne_one,
    have μs_eq_zero : μ (((λ x, γ • x) '' 𝓕) ∩ 𝓕) = 0 := h𝓕.3 γ γ_ne_one,
    change μ (((λ x, γ • x) '' (has_mul.mul g ⁻¹' 𝓕)) ∩ (has_mul.mul g ⁻¹' 𝓕)) = 0,
    rw [subgroup.smul_opposite_image_mul_preimage, ← preimage_inter, measure_preimage_mul μ g _,
      μs_eq_zero],
  end }

variables [encodable Γ] [measurable_space (G ⧸ Γ)] [borel_space (G ⧸ Γ)]

/-- The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-
  invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. -/
@[to_additive "The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and
  right-invariant measure on an additive topological group `G` to a fundamental domain `𝓕` is a
  `G`-invariant measure on `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.smul_invariant_measure_map
  [μ.is_mul_left_invariant] [μ.is_mul_right_invariant] :
  smul_invariant_measure G (G ⧸ Γ) (measure.map quotient_group.mk (μ.restrict 𝓕)) :=
{ measure_preimage_smul :=
  begin
    let π : G → G ⧸ Γ := quotient_group.mk,
    have meas_π : measurable π :=
      continuous_quotient_mk.measurable,
    have 𝓕meas : measurable_set 𝓕 := h𝓕.measurable_set,
    intros g A hA,
    have meas_πA : measurable_set (π ⁻¹' A) := measurable_set_preimage meas_π hA,
    rw [measure.map_apply meas_π hA,
      measure.map_apply meas_π (measurable_set_preimage (measurable_const_smul g) hA),
      measure.restrict_apply' 𝓕meas, measure.restrict_apply' 𝓕meas],
    set π_preA := π ⁻¹' A,
    have : (quotient_group.mk ⁻¹' ((λ (x : G ⧸ Γ), g • x) ⁻¹' A)) = has_mul.mul g ⁻¹' π_preA,
    { ext1, simp },
    rw this,
    have : μ (has_mul.mul g ⁻¹' π_preA ∩ 𝓕) = μ (π_preA ∩ has_mul.mul (g⁻¹) ⁻¹' 𝓕),
    { transitivity μ (has_mul.mul g ⁻¹' (π_preA ∩ has_mul.mul g⁻¹ ⁻¹' 𝓕)),
      { rw preimage_inter,
        congr,
        rw [← preimage_comp, comp_mul_left, mul_left_inv],
        ext,
        simp, },
      rw measure_preimage_mul, },
    rw this,
    have h𝓕_translate_fundom : is_fundamental_domain Γ.opposite (has_mul.mul g⁻¹ ⁻¹' 𝓕) μ :=
      h𝓕.smul (g⁻¹),
    rw h𝓕.measure_set_eq h𝓕_translate_fundom meas_πA,
    rintros ⟨γ, γ_in_Γ⟩,
    ext,
    have : π (x * (mul_opposite.unop γ)) = π (x) := by simpa [quotient_group.eq'] using γ_in_Γ,
    simp [(•), this],
  end }

/-- Assuming `Γ` is a normal subgroup of a topological group `G`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a
  fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`. -/
@[to_additive "Assuming `Γ` is a normal subgroup of an additive topological group `G`, the
  pushforward to the quotient group `G ⧸ Γ` of the restriction of a both left- and right-invariant
  measure on `G` to a fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.is_mul_left_invariant_map [subgroup.normal Γ]
  [μ.is_mul_left_invariant] [μ.is_mul_right_invariant] :
  (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)).is_mul_left_invariant :=
{ map_mul_left_eq_self := begin
    intros x,
    apply measure.ext,
    intros A hA,
    obtain ⟨x₁, _⟩ := @quotient.exists_rep _ (quotient_group.left_rel Γ) x,
    haveI := h𝓕.smul_invariant_measure_map,
    convert measure_preimage_smul x₁ ((measure.map quotient_group.mk) (μ.restrict 𝓕)) A using 1,
    rw [← h, measure.map_apply],
    { refl, },
    { exact measurable_const_mul _, },
    { exact hA, },
  end }

variables [t2_space (G ⧸ Γ)] [second_countable_topology (G ⧸ Γ)] (K : positive_compacts (G ⧸ Γ))

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on `G ⧸ Γ`. -/
@[to_additive "Given a normal subgroup `Γ` of an additive topological group `G` with Haar measure
  `μ`, which is also right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward
  to the quotient group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on
  `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.map_restrict_quotient [subgroup.normal Γ]
  [measure_theory.measure.is_haar_measure μ] [μ.is_mul_right_invariant]
  (h𝓕_finite : μ 𝓕 < ⊤) : measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)
  = (μ (𝓕 ∩ (quotient_group.mk' Γ) ⁻¹' K)) • (measure_theory.measure.haar_measure K) :=
begin
  let π : G →* G ⧸ Γ := quotient_group.mk' Γ,
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  have 𝓕meas : measurable_set 𝓕 := h𝓕.measurable_set,
  haveI : is_finite_measure (μ.restrict 𝓕) :=
    ⟨by { rw [measure.restrict_apply' 𝓕meas, univ_inter], exact h𝓕_finite }⟩,
  -- the measure is left-invariant, so by the uniqueness of Haar measure it's enough to show that
  -- it has the stated size on the reference compact set `K`.
  haveI : (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)).is_mul_left_invariant :=
    h𝓕.is_mul_left_invariant_map,
  rw [measure.haar_measure_unique (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)) K,
    measure.map_apply meas_π, measure.restrict_apply' 𝓕meas, inter_comm],
  exact K.compact.measurable_set,
end







---------------------------- UNFOLDING TRICK ---------------

open_locale big_operators ennreal

-- theorem disjoint.inter {α : Type*} {s t : set α} (u : set α) (h : disjoint s t) :
-- disjoint (u ∩ s) (u ∩ t) := by apply_rules [disjoint.inter_right', disjoint.inter_left']

-- theorem disjoint.inter' {α : Type*} {s t : set α} (u : set α) (h : disjoint s t) :
-- disjoint (s ∩ u) (t ∩ u) := by apply_rules [disjoint.inter_left, disjoint.inter_right]


/-
-- see if this exists in fundamental domain
lemma integral_Union {ι : Type*} [encodable ι] {s : ι → set ℝ } (f : ℝ  → ℂ )
  (hm : ∀ i, measurable_set (s i)) (hd : pairwise (disjoint on s)) (hfi : integrable f  ) :
  (∫ a in (⋃ n, s n), f a ) = ∑' n, ∫ a in s n, f a  :=
sorry
-/

local notation `μ_𝓕` := measure.map (@quotient_group.mk G _ Γ) (μ.restrict 𝓕)

@[simp] lemma subgroup_mem_opposite_iff (γ : Gᵐᵒᵖ) : γ ∈ Γ.opposite ↔ mul_opposite.unop γ ∈ Γ :=
by simp [subgroup.opposite]



lemma ess_sup_of_g [μ.is_mul_left_invariant] [μ.is_mul_right_invariant]
  (g : G ⧸ Γ → ℝ≥0∞) (g_measurable : measurable g) :
  ess_sup g μ_𝓕 = ess_sup (λ (x : G), g x) μ :=
begin
  have hπ : measurable (quotient_group.mk : G → G ⧸ Γ) := sorry,
  rw ess_sup_map_measure_of_measurable g_measurable hπ,
  refine h𝓕.ess_sup_measure_restrict _,
  sorry,
end

#exit

/-- This is the "unfolding" trick -/
lemma unfolding_trick [μ.is_mul_left_invariant] [μ.is_mul_right_invariant]
  {f : G → ℂ}
  (f_summable: ∀ x : G, summable (λ (γ : Γ.opposite), f (γ⁻¹ • x))) -- NEEDED??
  (f_ℒ_1 : integrable f μ)
  {g : G ⧸ Γ → ℂ}
  (g_ℒ_infinity : mem_ℒp g ∞ μ_𝓕)
  {F : G ⧸ Γ → ℂ}
  (F_ae_measurable : ae_measurable F μ_𝓕) -- NEEDED??
  (hFf : ∀ (x : G), F (x : G ⧸ Γ) = ∑' (γ : Γ.opposite), f(γ • x)) :
  ∫ (x : G), f x * g (x : G ⧸ Γ) ∂μ = ∫ (x : G ⧸ Γ), F x * g x ∂μ_𝓕 :=
begin
--  set F : G ⧸ Γ → ℂ :=  λ x , ∑' (γ : Γ.opposite), f(γ • x)) ,
  have hFf' : ∀ (x : G), F (x : G ⧸ Γ) = ∑' (γ : Γ.opposite), f(γ⁻¹ • x),
  { intros x,
    rw hFf x,
    exact ((equiv.inv (Γ.opposite)).tsum_eq  (λ γ, f(γ • x))).symm, },
  let π : G → G ⧸ Γ := quotient_group.mk,
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  rw integral_map meas_π,
  have : ∀ (x : G), F (x : G ⧸ Γ) * g (x) = ∑' (γ : Γ.opposite), f (γ⁻¹ • x) * g (x),
  { intros x,
    rw hFf' x,
    convert (@tsum_smul_const _ Γ.opposite _ _ _ _ _ _ _ (λ γ, f (γ⁻¹ • x)) _ (g x) _).symm using 1,
    exact f_summable x, },
  refine eq.trans _ (integral_congr_ae (filter.eventually_of_forall this)).symm,
  rw measure_theory.integral_tsum,
  haveI := h𝓕.smul_invariant_measure_map,
  convert h𝓕.set_integral_eq_tsum (λ x, f x * g x) univ _,
  { simp, },
  { ext1 γ,
    simp only [smul_set_univ, univ_inter],
    congr,
    ext1 x,
    have : g ↑(γ⁻¹ • x) = g x,
    { obtain ⟨γ₀, hγ₀⟩ := γ,
      congr' 1,
      simpa [quotient_group.eq, (•)] using hγ₀, },
    rw this, },
  {
    apply integrable.mul_ℒ_infinity,
    { sorry },
      -- exact f_measurable, },
    {
      sorry, -- g is measurable on G
    },
    {
      --extract_goal,
      sorry, -- g_ℒ_infinity from G/Γ to G
    },
    { convert f_ℒ_1,
      simp, }, },
  { intros γ,
    have hf : ae_measurable f (measure.map ((•) γ⁻¹) μ),
    { rw measure_theory.map_smul,
      exact f_ℒ_1.ae_measurable },
    refine ((hf.comp_measurable (measurable_const_smul _)).mono_measure _).mul _,
    { exact measure.restrict_le_self },
    { exact g_ℒ_infinity.ae_measurable.comp_measurable meas_π } },
  { exact F_ae_measurable.mul g_ℒ_infinity.ae_measurable, },
end
