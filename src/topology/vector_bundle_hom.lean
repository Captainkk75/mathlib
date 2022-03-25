/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import topology.vector_bundle

/-! # The bundle of continuous linear maps between two vector bundles over the same base -/

noncomputable theory

open bundle set

namespace topological_vector_bundle

section defs
variables {𝕜₁ : Type*} [normed_field 𝕜₁]
variables {𝕜₂ : Type*} [normed_field 𝕜₂]
variables (σ : 𝕜₁ →+* 𝕜₂)
variables {B : Type*}
  (F₁ : Type*) (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜₁ (E₁ x)]
  [Π x : B, topological_space (E₁ x)] [Π x, has_continuous_add (E₁ x)]
  [Π x, has_continuous_smul 𝕜₁ (E₁ x)]
  (F₂ : Type*) (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜₂ (E₂ x)]
  [Π x : B, topological_space (E₂ x)] [Π x, has_continuous_add (E₂ x)]
  [Π x, has_continuous_smul 𝕜₂ (E₂ x)]

include F₁ F₂

-- In this definition we require the scalar rings `𝕜₁` and `𝕜₂` to be normed fields, although
-- something much weaker (maybe `comm_semiring`) would suffice mathematically -- this is because of
-- a typeclass inference bug with pi-types:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/vector.20bundles.20--.20typeclass.20inference.20issue
/-- The bundle of continuous `σ`-semilinear maps between the topological vector bundles `E₁` and
`E₂`.  Type synonym for `λ x, E₁ x →SL[σ] E₂ x`. -/
@[derive [add_comm_monoid, module 𝕜₂, inhabited], nolint unused_arguments]
def vector_bundle_continuous_linear_map (x : B) :=
E₁ x →SL[σ] E₂ x

instance vector_bundle_continuous_linear_map.add_monoid_hom_class (x : B) :
  add_monoid_hom_class (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂ x) (E₁ x) (E₂ x) :=
continuous_linear_map.add_monoid_hom_class

end defs

variables {𝕜₁ : Type*} [nondiscrete_normed_field 𝕜₁] {𝕜₂ : Type*} [nondiscrete_normed_field 𝕜₂]
  (σ : 𝕜₁ →+* 𝕜₂)

variables {B : Type*} [topological_space B]

namespace pretrivialization

variables (F₁ : Type*) [normed_group F₁] [normed_space 𝕜₁ F₁]
  (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜₁ (E₁ x)]
  [Π x : B, topological_space (E₁ x)] [topological_space (total_space E₁)]
  [Π x, has_continuous_add (E₁ x)] [Π x, has_continuous_smul 𝕜₁ (E₁ x)]
  [topological_vector_bundle 𝕜₁ F₁ E₁]

variables (F₂ : Type*) [normed_group F₂] [normed_space 𝕜₂ F₂]
  (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜₂ (E₂ x)]
  [Π x : B, topological_space (E₂ x)] [topological_space (total_space E₂)]
  [Π x, has_continuous_add (E₂ x)] [Π x, has_continuous_smul 𝕜₂ (E₂ x)]
  [topological_vector_bundle 𝕜₂ F₂ E₂]


variables (e₁ : trivialization 𝕜₁ F₁ E₁) (e₂ : trivialization 𝕜₂ F₂ E₂)

include e₁ e₂
variables {F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `topological_vector_bundle.pretrivialization.continuous_linear_map`,
the induced pretrivialization for the continuous semilinear maps from `E₁` to `E₂`. -/
def continuous_linear_map.to_fun'
  (p : total_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂)) :
  B × (F₁ →SL[σ] F₂) :=
begin
  obtain ⟨x, L⟩ := p,
  refine ⟨x, _⟩,
  by_cases h : x ∈ e₁.base_set ∧ x ∈ e₂.base_set,
  { let φ₁ := e₁.continuous_linear_equiv_at x h.1,
    let φ₂ := e₂.continuous_linear_equiv_at x h.2,
    exact ((φ₂ : E₂ x →L[𝕜₂] F₂).comp L).comp (φ₁.symm : F₁ →L[𝕜₁] E₁ x) },
  { exact 0 }
end

variables {σ e₁ e₂}

lemma continuous_linear_map.to_fun'_apply {x : B} (h₁ : x ∈ e₁.base_set) (h₂ : x ∈ e₂.base_set)
  (L : E₁ x →SL[σ] E₂ x) :
  continuous_linear_map.to_fun' σ e₁ e₂ ⟨x, L⟩ =
  ⟨x, ((e₂.continuous_linear_equiv_at x h₂ : E₂ x →L[𝕜₂] F₂).comp L).comp
    ((e₁.continuous_linear_equiv_at x h₁).symm : F₁ →L[𝕜₁] E₁ x)⟩ :=
begin
  dsimp [continuous_linear_map.to_fun'],
  rw dif_pos,
  exact ⟨h₁, h₂⟩
end

lemma continuous_linear_map.to_fun'_apply' {x : B} (h₁ : x ∈ e₁.base_set) (h₂ : x ∈ e₂.base_set)
  (L : E₁ x →SL[σ] E₂ x) :
  continuous_linear_map.to_fun' σ e₁ e₂
    (@coe _ _ (@coe_to_lift _ _
      (@total_space.has_coe_t B (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) x)) L)
  = ⟨x, ((e₂.continuous_linear_equiv_at x h₂ : E₂ x →L[𝕜₂] F₂).comp L).comp
      ((e₁.continuous_linear_equiv_at x h₁).symm : F₁ →L[𝕜₁] E₁ x)⟩ :=
continuous_linear_map.to_fun'_apply h₁ h₂ L

variables (σ e₁ e₂)

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `topological_vector_bundle.pretrivialization.continuous_linear_map`,
the induced pretrivialization for the continuous semilinear maps from `E₁` and `E₂`. -/
def continuous_linear_map.inv_fun' (p : B × (F₁ →SL[σ] F₂)) :
  total_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
begin
  obtain ⟨x, f⟩ := p,
  refine ⟨x, _⟩,
  by_cases h : x ∈ e₁.base_set ∧ x ∈ e₂.base_set,
  { let φ₁ := e₁.continuous_linear_equiv_at x h.1,
    let φ₂ := e₂.continuous_linear_equiv_at x h.2,
    exact ((φ₂.symm : F₂ →L[𝕜₂] E₂ x).comp f).comp (φ₁ : E₁ x →L[𝕜₁] F₁) },
  { exact 0 }
end

variables {σ e₁ e₂}

lemma continuous_linear_map.inv_fun'_apply {x : B} (h₁ : x ∈ e₁.base_set) (h₂ : x ∈ e₂.base_set)
  (f : F₁ →SL[σ] F₂) :
  continuous_linear_map.inv_fun' σ e₁ e₂ ⟨x, f⟩
  = total_space_mk (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) x
    ((((e₂.continuous_linear_equiv_at x h₂).symm : F₂ →L[𝕜₂] E₂ x).comp f).comp
      ((e₁.continuous_linear_equiv_at x h₁) : E₁ x →L[𝕜₁] F₁)) :=
begin
  dsimp [continuous_linear_map.inv_fun'],
  rw dif_pos,
  exact ⟨h₁, h₂⟩
end

variables (σ e₁ e₂) [ring_hom_isometric σ]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
pretrivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`.  That is, the map which
will later become a trivialization, after this direct sum is equipped with the right topological
vector bundle structure. -/
def continuous_linear_map :
  pretrivialization 𝕜₂ (F₁ →SL[σ] F₂) (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
{ to_fun := continuous_linear_map.to_fun' σ e₁ e₂,
  inv_fun := continuous_linear_map.inv_fun' σ e₁ e₂,
  source := (proj (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂)) ⁻¹'
    (e₁.base_set ∩ e₂.base_set),
  target := (e₁.base_set ∩ e₂.base_set) ×ˢ (set.univ : set (F₁ →SL[σ] F₂)),
  map_source' := λ ⟨x, L⟩ h, ⟨h, set.mem_univ _⟩,
  map_target' := λ ⟨x, f⟩ h, h.1,
  left_inv' := λ ⟨x, L⟩ ⟨h₁, h₂⟩,
  begin
    rw [continuous_linear_map.to_fun'_apply h₁ h₂, continuous_linear_map.inv_fun'_apply h₁ h₂],
    simp only [sigma.mk.inj_iff, eq_self_iff_true, heq_iff_eq, true_and],
    ext v,
    simp only [continuous_linear_map.coe_comp', continuous_linear_equiv.coe_coe, function.comp_app,
      continuous_linear_equiv.symm_apply_apply],
  end,
  right_inv' := λ ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩,
  begin
    rw [continuous_linear_map.inv_fun'_apply h₁ h₂, continuous_linear_map.to_fun'_apply h₁ h₂],
    simp only [prod.mk.inj_iff, eq_self_iff_true, true_and],
    ext v,
    simp only [continuous_linear_map.coe_comp', continuous_linear_equiv.coe_coe, function.comp_app,
      continuous_linear_equiv.apply_symm_apply],
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  base_set := e₁.base_set ∩ e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ ⟨x, f⟩ h, rfl,
  linear := λ x ⟨h₁, h₂⟩,
  { map_add := λ L L', by simp [continuous_linear_map.to_fun'_apply' h₁ h₂],
    map_smul := λ c L, by simp [continuous_linear_map.to_fun'_apply' h₁ h₂], } }

variables {σ e₁ e₂}

@[simp] lemma base_set_continuous_linear_map :
  (continuous_linear_map σ e₁ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

lemma continuous_linear_map_apply {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set)
  (L : E₁ x →SL[σ] E₂ x) :
  continuous_linear_map σ e₁ e₂ ⟨x, L⟩
  = ⟨x, ((e₂.continuous_linear_equiv_at x hx₂ : E₂ x →L[𝕜₂] F₂).comp L).comp
      ((e₁.continuous_linear_equiv_at x hx₁).symm : F₁ →L[𝕜₁] E₁ x)⟩ :=
continuous_linear_map.to_fun'_apply hx₁ hx₂ L

lemma continuous_linear_map_symm_apply {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set)
  (f : F₁ →SL[σ] F₂) :
  (continuous_linear_map σ e₁ e₂).to_local_equiv.symm (x, f)
  = ⟨x, (((e₂.continuous_linear_equiv_at x hx₂).symm : F₂ →L[𝕜₂] E₂ x).comp f).comp
      ((e₁.continuous_linear_equiv_at x hx₁) : E₁ x →L[𝕜₁] F₁)⟩ :=
continuous_linear_map.inv_fun'_apply hx₁ hx₂ f

end pretrivialization

open pretrivialization
variables [ring_hom_isometric σ] (F₁ : Type*) [normed_group F₁] [normed_space 𝕜₁ F₁]
  [complete_space F₁]
  (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜₁ (E₁ x)]
  [Π x : B, topological_space (E₁ x)] [topological_space (total_space E₁)]
  [Π x, has_continuous_add (E₁ x)] [Π x, has_continuous_smul 𝕜₁ (E₁ x)]
  [topological_vector_bundle 𝕜₁ F₁ E₁]

variables (F₂ : Type*) [normed_group F₂] [normed_space 𝕜₂ F₂] [complete_space F₂]
  (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜₂ (E₂ x)]
  [Π x : B, topological_space (E₂ x)] [topological_space (total_space E₂)]
  [Π x, has_continuous_add (E₂ x)] [Π x, has_continuous_smul 𝕜₂ (E₂ x)]
  [topological_vector_bundle 𝕜₂ F₂ E₂]


example (e : F₁ ≃L[𝕜₁] F₁) : continuous_at (λ f : F₁ →L[𝕜₁] F₁, ring.inverse f) e :=
normed_ring.inverse_continuous_at e.to_unit

variables {F₁ F₂}

noncomputable!
def continuous_linear_equiv.arrow_congr_linear_equivL (u : F₁ ≃L[𝕜₁] F₁)
  (v : F₂ ≃L[𝕜₂] F₂) : (F₁ →SL[σ] F₂) ≃L[𝕜₂] (F₁ →SL[σ] F₂) :=
begin
  let Φ₁ : (F₁ →L[𝕜₁] F₁) →SL[σ] (F₁ →SL[σ] F₂) →L[𝕜₂] (F₁ →SL[σ] F₂) :=
  (continuous_linear_map.compSL F₁ F₁ F₂ (ring_hom.id 𝕜₁) σ : (F₁ →SL[σ] F₂) →L[𝕜₂] (F₁ →L[𝕜₁] F₁) →SL[σ] F₁ →SL[σ] F₂).flip,
  let Φ₂ := continuous_linear_map.compSL F₁ F₂ F₂ σ (ring_hom.id 𝕜₂),
  apply continuous_linear_equiv.mk (continuous_linear_equiv.arrow_congr_linear_equiv σ u v) _ _,
  { exact ((Φ₂ v).comp (Φ₁ u.symm)).continuous },
  { exact ((Φ₁ u).comp (Φ₂ v.symm)).continuous },
end

@[simp]
lemma continuous_linear_equiv.arrow_congr_linear_equivL_apply (u : F₁ ≃L[𝕜₁] F₁)
  (v : F₂ ≃L[𝕜₂] F₂) (f : F₁ →SL[σ] F₂) :
  continuous_linear_equiv.arrow_congr_linear_equivL σ u v f = (v : F₂ →L[𝕜₂] F₂).comp (f.comp (u.symm : F₁ →L[𝕜₁] F₁)) := rfl

def foo (u : F₁ →L[𝕜₁] F₁)
  (v : F₂ →L[𝕜₂] F₂) : (F₁ →SL[σ] F₂) →ₗ[𝕜₂] (F₁ →SL[σ] F₂) :=
{ to_fun := λ φ, v.comp (φ.comp $ ring.inverse u),
  map_add' := λ φ ψ, by simp,
  map_smul' := λ r φ, by simp }

def bar (u : F₁ →L[𝕜₁] F₁)
  (v : F₂ →L[𝕜₂] F₂) : (F₁ →SL[σ] F₂) →L[𝕜₂] (F₁ →SL[σ] F₂) :=
begin
  let Φ₁ : (F₁ →L[𝕜₁] F₁) →SL[σ] (F₁ →SL[σ] F₂) →L[𝕜₂] (F₁ →SL[σ] F₂) :=
  (continuous_linear_map.compSL F₁ F₁ F₂ (ring_hom.id 𝕜₁) σ : (F₁ →SL[σ] F₂) →L[𝕜₂] (F₁ →L[𝕜₁] F₁) →SL[σ] F₁ →SL[σ] F₂).flip,
  let Φ₂ := continuous_linear_map.compSL F₁ F₂ F₂ σ (ring_hom.id 𝕜₂),
  exact continuous_linear_map.mk (foo σ u v) ((Φ₂ v).comp (Φ₁ $ ring.inverse u)).continuous,
end

@[simp] lemma bar_apply (u : F₁ →L[𝕜₁] F₁)
  (v : F₂ →L[𝕜₂] F₂) (f : F₁ →SL[σ] F₂) : bar σ u v f = v.comp (f.comp $ ring.inverse u) := rfl

lemma barL (u : F₁ ≃L[𝕜₁] F₁) (v : F₂ ≃L[𝕜₂] F₂) :
  (continuous_linear_equiv.arrow_congr_linear_equivL σ u v : (F₁ →SL[σ] F₂) →L[𝕜₂] (F₁ →SL[σ] F₂)) = bar σ u v :=
begin
  apply continuous_linear_map.ext,
  simp
end


@[simp] lemma continuous_linear_equiv.coe_to_unit {R : Type*} [ring R] {M : Type*}
[topological_space M] [add_comm_group M]
  [module R M] [topological_add_group M] (e : M ≃L[R] M) : (e.to_unit : M →L[R] M) = (e : M →L[R] M) :=
  rfl

lemma continuous_linear_map.continuous_compL
  (𝕜 : Type*) (E : Type*) (Fₗ : Type*) (Gₗ : Type*) [normed_group E]
  [normed_group Fₗ] [normed_group Gₗ] [nondiscrete_normed_field 𝕜]
  [normed_space 𝕜 E] [normed_space 𝕜 Fₗ] [normed_space 𝕜 Gₗ] :
  continuous (λ p : (Fₗ →L[𝕜] Gₗ) × (E →L[𝕜] Fₗ), continuous_linear_map.compL _ _ _ _ p.1 p.2) :=
 is_bounded_bilinear_map_comp.continuous.comp continuous_swap

lemma continuous_on_bar :
  continuous_on (function.uncurry $ bar σ: (F₁ →L[𝕜₁] F₁) × (F₂ →L[𝕜₂] F₂) → ((F₁ →SL[σ] F₂) →L[𝕜₂] F₁ →SL[σ] F₂))  ((range $ (coe : (F₁ ≃L[𝕜₁] F₁) → (F₁ →L[𝕜₁] F₁))) ×ˢ (range $ (coe : (F₂ ≃L[𝕜₂] F₂) → (F₂ →L[𝕜₂] F₂)))) :=
begin
  set G₁ := (F₁ →L[𝕜₁] F₁),
  set G₂ := (F₂ →L[𝕜₂] F₂),
  set H := F₁ →SL[σ] F₂,
  rintros ⟨f, g⟩ ⟨⟨φ, rfl : ↑φ = f⟩, ⟨ψ, rfl : ↑ψ = g⟩⟩,
  apply continuous_at.continuous_within_at,
  have : continuous_at ring.inverse (φ : F₁ →L[𝕜₁] F₁),
    from normed_ring.inverse_continuous_at φ.to_unit,
  let Φ₁ : G₁ →SL[σ] H →L[𝕜₂] H :=
  by exact (continuous_linear_map.compSL F₁ F₁ F₂ (ring_hom.id 𝕜₁) σ : H →L[𝕜₂] G₁ →SL[σ] H).flip,
  let Φ₂ := continuous_linear_map.compSL F₁ F₂ F₂ σ (ring_hom.id 𝕜₂),
  have C₁ := (Φ₁.continuous.continuous_at.comp this).prod_map' Φ₂.continuous.continuous_at,
  let Θ := continuous_linear_map.compL 𝕜₂ H H H,
  change continuous_at
    ((λ p: (H →L[𝕜₂] H) × (H →L[𝕜₂] H), Θ p.1 p.2) ∘ (prod.map (Φ₁ ∘ ring.inverse) Φ₂)) _,
  apply continuous_at.comp _ C₁,
  apply continuous.continuous_at,
  apply continuous_linear_map.continuous_compL,
end

variables (F₁ F₂)

/-- The continuous `σ`-semilinear maps between two topological vector bundles form a
`topological_vector_prebundle` (this is an auxiliary construction for the
`topological_vector_bundle` instance, in which the pretrivializations are collated but no
topology on the total space is yet provided). -/
def _root_.vector_bundle_continuous_linear_map.topological_vector_prebundle :
  topological_vector_prebundle 𝕜₂ (F₁ →SL[σ] F₂)
  (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
{ pretrivialization_atlas := {f | ∃ (e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁)
    (e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂), f = pretrivialization.continuous_linear_map σ e₁ e₂ },
  pretrivialization_at := λ x, pretrivialization.continuous_linear_map σ
    (trivialization_at 𝕜₁ F₁ E₁ x) (trivialization_at 𝕜₂ F₂ E₂ x),
  mem_base_pretrivialization_at := λ x,
    ⟨mem_base_set_trivialization_at 𝕜₁ F₁ E₁ x, mem_base_set_trivialization_at 𝕜₂ F₂ E₂ x⟩,
  pretrivialization_mem_atlas := λ x,
    ⟨_, trivialization_mem_atlas 𝕜₁ F₁ E₁ x, _, trivialization_mem_atlas 𝕜₂ F₂ E₂ x, rfl⟩,
  continuous_coord_change := begin
    rintros _ ⟨e₁, he₁, e₂, he₂, rfl⟩ _ ⟨e₁', he₁', e₂', he₂', rfl⟩,
    let s₁ := e₁.base_set ∩ e₁'.base_set,
    let s₂ := e₂.base_set ∩ e₂'.base_set,
    let ε₁ := coord_change he₁ he₁',
    let ε₂ := coord_change he₂ he₂',
    let Φ₁ : (F₁ →L[𝕜₁] F₁) →SL[σ] (F₁ →SL[σ] F₂) →L[𝕜₂] (F₁ →SL[σ] F₂),
    { apply continuous_linear_map.flip,
      exact (continuous_linear_map.compSL F₁ F₁ F₂ (ring_hom.id 𝕜₁) σ) },
    let Φ₂ := continuous_linear_map.compSL F₁ F₂ F₂ σ (ring_hom.id 𝕜₂),
    let ε := λ b, continuous_linear_equiv.arrow_congr_linear_equivL σ (ε₁ b) (ε₂ b),
    refine ⟨s₁ ∩ s₂, _, _ , ε, _, _⟩,
    { rw topological_fiber_bundle.pretrivialization.symm_trans_source_eq,
      simp [s₁, s₂],
      mfld_set_tac },
    { rw topological_fiber_bundle.pretrivialization.symm_trans_target_eq,
      simp [s₁, s₂],
      mfld_set_tac },
    { have hε₁ : continuous_on (λ b, ↑(ε₁ b)) s₁ := continuous_on_coord_change he₁ he₁',
      have hε₂ : continuous_on (λ b, ↑(ε₂ b)) s₂ := continuous_on_coord_change he₂ he₂',
      have : ∀ b ∈ s₁ ∩ s₂, (ε b : (F₁ →SL[σ] F₂) →L[𝕜₂] F₁ →SL[σ] F₂) = bar σ ↑(ε₁ b) ↑(ε₂ b),
      { intros b hb,
        apply barL },
        apply continuous_on.congr _ this,
      let f : B → (F₁ →L[𝕜₁] F₁) × (F₂ →L[𝕜₂] F₂) := λ (b : B), (↑(ε₁ b), ↑(ε₂ b)),
      have : continuous_on f (s₁ ∩ s₂) := (hε₁.mono (inter_subset_left s₁ s₂)).prod (hε₂.mono (inter_subset_right s₁ s₂)),
      exact (continuous_on_bar σ).comp this (λ b hb, ⟨⟨ε₁ b, rfl⟩, ⟨ε₂ b, rfl⟩⟩) },
    { intros b hb φ,
      sorry }
  end }

/-- Topology on the continuous `σ`-semilinear_maps between the respective fibres at a point of two
vector bundles over the same base.  The topology we put on the continuous
`σ`-semilinear_maps is the topology coming from the operator norm on maps from `F₁` to `F₂`. -/
instance (x : B) : topological_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂ x) :=
(vector_bundle_continuous_linear_map.topological_vector_prebundle
  σ F₁ E₁ F₂ E₂).fiber_topology x

/-- Topology on the total space of the continuous `σ`-semilinear_maps between two vector
bundles over the same base. -/
instance : topological_space (total_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂)) :=
(vector_bundle_continuous_linear_map.topological_vector_prebundle
  σ F₁ E₁ F₂ E₂).total_space_topology

/-- The continuous `σ`-semilinear_maps between two vector bundles form a vector bundle. -/
instance vector_bundle_continuous_linear_map.topological_vector_bundle :
  topological_vector_bundle 𝕜₂ (F₁ →SL[σ] F₂)
    (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
(vector_bundle_continuous_linear_map.topological_vector_prebundle
  σ F₁ E₁ F₂ E₂).to_topological_vector_bundle

variables {F₁ E₁ F₂ E₂}

/-- Given elements `e₁`, `e₂` of the trivialization atlases of vector bundles `E₁`, `E₂`
respectively over a base `B`, the induced trivialization for the continuous `σ`-semilinear maps from
`E₁` to `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`. -/
def trivialization.continuous_linear_map
  {e₁ : trivialization 𝕜₁ F₁ E₁} (he₁ : e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁)
  {e₂ : trivialization 𝕜₂ F₂ E₂} (he₂ : e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂) :
  trivialization 𝕜₂ (F₁ →SL[σ] F₂) (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
(vector_bundle_continuous_linear_map.topological_vector_prebundle
  σ F₁ E₁ F₂ E₂).trivialization_of_mem_pretrivialization_atlas
  ⟨e₁, he₁, e₂, he₂, rfl⟩

lemma trivialization.base_set_continuous_linear_map
  {e₁ : trivialization 𝕜₁ F₁ E₁} (he₁ : e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁)
  {e₂ : trivialization 𝕜₂ F₂ E₂} (he₂ : e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂) :
  (trivialization.continuous_linear_map σ he₁ he₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

lemma trivialization.continuous_linear_map_mem_atlas
  {e₁ : trivialization 𝕜₁ F₁ E₁} (he₁ : e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁)
  {e₂ : trivialization 𝕜₂ F₂ E₂} (he₂ : e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂) :
  trivialization.continuous_linear_map σ he₁ he₂ ∈
    trivialization_atlas 𝕜₂ (F₁ →SL[σ] F₂) (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
sorry

lemma trivialization.continuous_linear_map_apply
  {e₁ : trivialization 𝕜₁ F₁ E₁} (he₁ : e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁)
  {e₂ : trivialization 𝕜₂ F₂ E₂} (he₂ : e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂) {x : B}
  (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) (L : E₁ x →SL[σ] E₂ x) :
  trivialization.continuous_linear_map σ he₁ he₂ ⟨x, L⟩
  = ⟨x, (e₂.continuous_linear_equiv_at x hx₂ : E₂ x →L[𝕜₂] F₂).comp (L.comp
      ((e₁.continuous_linear_equiv_at x hx₁).symm : F₁ →L[𝕜₁] E₁ x))⟩ :=
pretrivialization.continuous_linear_map_apply hx₁ hx₂ L

lemma trivialization.continuous_linear_equiv_at_continuous_linear_map
  {e₁ : trivialization 𝕜₁ F₁ E₁} (he₁ : e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁)
  {e₂ : trivialization 𝕜₂ F₂ E₂} (he₂ : e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂) {x : B}
  (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set)  :
  ((trivialization.continuous_linear_map σ he₁ he₂).continuous_linear_equiv_at
    x ⟨hx₁, hx₂⟩).to_linear_equiv
  = continuous_linear_equiv.arrow_congr_linear_equiv σ
      (e₁.continuous_linear_equiv_at x hx₁)
      (e₂.continuous_linear_equiv_at x hx₂) :=
begin
  ext1,
  simp [trivialization.continuous_linear_map_apply σ he₁ he₂ hx₁ hx₂],
end

end topological_vector_bundle
