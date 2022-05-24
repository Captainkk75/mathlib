/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Dilations of emetric and metric spaces
Authors: Hanting Zhang
-/
import topology.metric_space.antilipschitz
import data.fun_like.basic

/-!
# Dilations

We define dilations, i.e., maps between emetric spaces that
satisfy `edist (f x) (f y) = r * edist x y`.

Defines `ratio f`, which is the ratio of some `f : dilation α β`.
Note that `ratio f : ℝ≥0`, so we do not exclude the degenerate case of dilations
which collapse into constant maps. Statements that do need strict dilations should
just say `f : dilation α β` and `hr : ratio f ≠ 0`.

TODO: Introduce dilation equivs. Refactor the isometry API
to match the `*_hom_class` API below.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `pseudo_metric_space` and we specialize to `metric_space` when needed.
-/

noncomputable theory

open function set
open_locale topological_space ennreal nnreal

section defs

variables (α : Type*) (β : Type*) [pseudo_emetric_space α] [pseudo_emetric_space β]

/-- A dilation is a map that uniformly scales the edistance between any two points.  -/
structure dilation :=
(to_fun : α → β)
(edist_eq' : ∃ r : ℝ≥0, ∀ x y : α, edist (to_fun x) (to_fun y) = r * edist x y)

attribute [nolint has_inhabited_instance] dilation

/--
`dilation_class F α β r` states that `F` is a type of `r`-dilations.

You should extend this typeclass when you extend `dilation`.
-/
class dilation_class (F : Type*) (α β : out_param $ Type*)
  [pseudo_emetric_space α] [pseudo_emetric_space β] extends fun_like F α (λ _, β) :=
(edist_eq' : ∀ (f : F), ∃ r : ℝ≥0, ∀ (x y : α), edist (f x) (f y) = r * edist x y)

attribute [nolint dangerous_instance] dilation_class.to_fun_like

end defs

namespace dilation
variables {α : Type*} {β : Type*} {γ : Type*} {F : Type*} {G : Type*}

section setup
variables [pseudo_emetric_space α] [pseudo_emetric_space β]

instance to_dilation_class :
  dilation_class (dilation α β) α β :=
{ coe := to_fun,
  coe_injective' := λ f g h, by { cases f; cases g; congr', },
  edist_eq' := λ f, edist_eq' f }

instance : has_coe_to_fun (dilation α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : dilation α β} : f.to_fun = (f : α → β) := rfl

@[simp] lemma coe_mk (f : α → β) (h) : ⇑(⟨f, h⟩ : dilation α β) = f := rfl

lemma congr_fun {f g : dilation α β} (h : f = g) (x : α) : f x = g x := fun_like.congr_fun h x
lemma congr_arg (f : dilation α β) {x y : α} (h : x = y) : f x = f y := fun_like.congr_arg f h

@[ext] theorem ext {f g : dilation α β} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

lemma ext_iff {f g : dilation α β} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

@[simp] lemma mk_coe (f : dilation α β) (h) : dilation.mk f h = f := ext $ λ _, rfl

/-- Copy of a `dilation` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : dilation α β) (f' : α → β) (h : f' = ⇑f) : dilation α β :=
{ to_fun := f',
  edist_eq' := h.symm ▸ f.edist_eq' }

/-- The ratio of a dilation `f`. Uses `Exists.some`, the `some_spec` counterpart
is the lemma `edist_eq` below -/
def ratio [dilation_class F α β] (f : F) : ℝ≥0 :=
(dilation_class.edist_eq' f).some

@[simp] lemma edist_eq [dilation_class F α β] (f : F) (x y : α) :
  edist (f x) (f y) = ratio f * edist x y :=
(dilation_class.edist_eq' f).some_spec x y

@[simp] lemma dist_eq {α β} {F : Type*}
  [pseudo_metric_space α] [pseudo_metric_space β] [dilation_class F α β]
  (f : F) (x y : α) : dist (f x) (f y) = ratio f * dist x y :=
by simp only [dist_edist, ennreal.to_real_mul, edist_eq, ennreal.coe_to_real]

@[simp] lemma nndist_eq {α β} {F : Type*}
  [pseudo_metric_space α] [pseudo_metric_space β] [dilation_class F α β]
  (f : F) (x y : α) : nndist (f x) (f y) = ratio f * nndist x y :=
begin
  apply subtype.ext _,
  simp only [coe_nndist, dist_eq, nonneg.coe_mul],
end

/-- The `ratio` is equal to the distance ratio for any two points with nonzero finite distance.
`dist` and `nndist` versions below -/
lemma ratio_unique [dilation_class F α β] {f : F} {x y : α} {r : ℝ≥0}
  (hxy : edist x y ≠ 0 ∧ edist x y ≠ ⊤) (hr : edist (f x) (f y) = r * edist x y) :
  r = ratio f :=
begin
  have h := edist_eq f x y,
  rwa [hr, ennreal.mul_eq_mul_right hxy.1 hxy.2, ennreal.coe_eq_coe] at h,
end

/-- The `ratio` is equal to the distance ratio for any two points
with nonzero finite distance; `dist version` -/
lemma ratio_unique' {α β} {F : Type*} [pseudo_metric_space α] [pseudo_metric_space β]
  [dilation_class F α β] {f : F} {x y : α} {r : ℝ≥0}
  (hxy : dist x y ≠ 0) (hr : dist (f x) (f y) = r * dist x y) :
  r = ratio f :=
begin
  have h := dist_eq f x y,
  rw [hr, (mul_eq_mul_right_iff)] at h,
  have := or.resolve_right h hxy,
  rwa nnreal.coe_eq at this,
end

/-- The `ratio` is equal to the distance ratio for any two points
with nonzero finite distance; `nndist version` -/
lemma ratio_unique'' {α β} {F : Type*} [pseudo_metric_space α] [pseudo_metric_space β]
  [dilation_class F α β] {f : F} {x y : α} {r : ℝ≥0}
  (hxy : nndist x y ≠ 0) (hr : nndist (f x) (f y) = r * nndist x y) :
  r = ratio f :=
begin
  have h := nndist_eq f x y,
  rwa [hr, mul_comm, mul_comm (ratio f), nnreal.mul_eq_mul_left hxy] at h,
end

/-- Alternative `dilation` constructor when the distance hypothesis is over `dist` -/
lemma mk' {α β} {F : Type*}
  [pseudo_metric_space α] [pseudo_metric_space β]
  (f : α → β) (h : ∃ (r : ℝ≥0), ∀ (x y : α), dist (f x) (f y) = r * dist x y) :
  dilation α β :=
{ to_fun := f,
  edist_eq' :=
  begin
    rcases h with ⟨r, h⟩,
    refine ⟨r, λ x y, _⟩,
    rw [edist_dist, edist_dist, ← ennreal.of_real_to_real ennreal.coe_ne_top,
      ← ennreal.of_real_mul],
    refine _root_.congr_arg _ (h x y),
    exact nnreal.zero_le_coe,
  end }

/-- Alternative `dilation` constructor when the distance hypothesis is over `nndist` -/
lemma mk'' {α β} {F : Type*}
  [pseudo_metric_space α] [pseudo_metric_space β]
  (f : α → β) (h : ∃ (r : ℝ≥0), ∀ (x y : α), nndist (f x) (f y) = r * nndist x y) :
  dilation α β :=
{ to_fun := f,
  edist_eq' :=
  begin
    rcases h with ⟨r, h⟩,
    refine ⟨r, λ x y, _⟩,
    rw [edist_nndist, edist_nndist, ← ennreal.coe_mul, h x y],
  end }

end setup

section pseudo_emetric_dilation
variables [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]
variables [dilation_class F α β] [dilation_class G β γ]
variables (f : F) (g : G) {x y z : α}  {s : set α}

lemma lipschitz : lipschitz_with (ratio f) (f : α → β) :=
λ x y, (edist_eq f x y).le

-- TODO: add `instance ennreal.div_inv_comm_monoid`
-- TODO: fix `antilipschitz_with` decl header
lemma antilipschitz (hr : ratio f ≠ 0) : antilipschitz_with ((ratio f)⁻¹) (f : α → β) :=
λ x y, begin
  -- `div_eq_mul_inv` should be `div_eq_inv_mul`
  rw [mul_comm, ← ennreal.div_le_iff_le_mul, div_eq_mul_inv, mul_comm, ennreal.coe_inv hr],
  simp only [inv_inv, edist_eq, le_refl],
  left, simp [hr],
  left, simp [hr],
end

/-- A dilation from an emetric space is injective -/
lemma injective {α : Type*} [emetric_space α]  [dilation_class F α β] (f : F) (hr : ratio f ≠ 0) :
  injective f := (dilation.antilipschitz f hr).injective

/-- Any map on a subsingleton is a dilation -/
def of_subsingleton [subsingleton α] (f : α → β) : dilation α β :=
{ to_fun := f,
  edist_eq' := ⟨0, λ x y, by { rw subsingleton.elim x y, simp, }⟩ }

/-- The identity is a dilation -/
def id (α) [pseudo_emetric_space α] : dilation α α :=
{ to_fun := _root_.id,
  edist_eq' := ⟨1, λ x y, by simp only [id.def, ennreal.coe_one, one_mul]⟩ }

instance : inhabited (dilation α α) := ⟨id α⟩

@[simp] lemma id_apply (x : α) : id α x = x := rfl

lemma id_ratio {α} [metric_space α] [nontrivial α] : ratio (id α) = 1 :=
begin
  rcases exists_pair_ne α with ⟨x, y, hne⟩,
  have := dist_eq (id α) x y,
  rw ← dist_ne_zero at hne,
  rwa [id_apply, id_apply, eq_comm, ← div_eq_iff_mul_eq hne,
    div_self hne, eq_comm, nnreal.coe_eq_one] at this,
end

/-- The composition of dilations is a dilation -/
def comp (g : dilation β γ) (f : dilation α β) :
  dilation α γ :=
{ to_fun := g ∘ f,
  edist_eq' := ⟨ratio g * ratio f, λ x y, by { simp only [edist_eq, ennreal.coe_mul], ring, }⟩ }

lemma comp_assoc {δ : Type*} [pseudo_emetric_space δ]
  (f : dilation α β) (g : dilation β γ) (h : dilation γ δ) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp] lemma coe_comp (g : dilation β γ) (f : dilation α β) :
  (g.comp f : α → γ) = g ∘ f := rfl

lemma comp_apply (g : dilation β γ) (f : dilation α β) (x : α) :
  (g.comp f : α → γ) x = (g (f x)) := rfl

@[simp] lemma comp_ratio {α β γ} [metric_space α] [nontrivial α]
  [pseudo_metric_space β] [pseudo_metric_space γ]
  (g : dilation β γ) (f : dilation α β) :
  ratio g * ratio f = ratio (g.comp f) :=
begin
  rcases exists_pair_ne α with ⟨x, y, hα⟩,
  rw ← dist_ne_zero at hα,
  have hgf := dist_eq (g.comp f) x y,
  simp only [dist_eq, coe_comp, ← mul_assoc, mul_eq_mul_right_iff] at hgf,
  rw ← nnreal.coe_eq,
  rw nnreal.coe_mul,
  refine or.resolve_right hgf hα,
end

@[simp] lemma comp_id (f : dilation α β) : f.comp (id α) = f := ext $ λ x, rfl

@[simp] lemma id_comp (f : dilation α β) : (id β).comp f = f := ext $ λ x, rfl

instance : monoid (dilation α α) :=
{ one := id α,
  mul := comp,
  mul_one := comp_id,
  one_mul := id_comp,
  mul_assoc := λ f g h, comp_assoc _ _ _ }

lemma one_def : (1 : dilation α α) = id α := rfl
lemma mul_def (f g : dilation α α) : f * g = f.comp g := rfl

@[simp] lemma coe_one : ⇑(1 : dilation α α) = _root_.id := rfl
@[simp] lemma coe_mul (f g : dilation α α) : ⇑(f * g) = f ∘ g := rfl

lemma cancel_right {g₁ g₂ : dilation β γ} {f : dilation α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, dilation.ext $ hf.forall.2 (ext_iff.1 h), λ h, h ▸ rfl⟩

lemma cancel_left {g : dilation β γ} {f₁ f₂ : dilation α β} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, dilation.ext $ λ x, hg $ by rw [← comp_apply, h, comp_apply], λ h, h ▸ rfl⟩

/-- The constant function of is a dilation -/
def const (α) [pseudo_emetric_space α] (b : β) :
  dilation α β :=
{ to_fun := λ _, b,
  edist_eq' := ⟨0, λ x y, by simp⟩ }

@[simp] lemma const_apply (b : β) (x : α) :
  (const α b) x = b := rfl

@[simp] lemma const_ratio {α} [metric_space α] [nontrivial α]
  {β} [pseudo_metric_space β] (b : β) :
  ratio (const α b) = 0 :=
begin
  rcases exists_pair_ne α with ⟨x, y, hα⟩,
  rw ← dist_ne_zero at hα,
  have := dist_eq (const α b) x y,
  simp only [const_apply, dist_self] at this,
  rw [eq_comm, mul_eq_zero, nnreal.coe_eq_zero] at this,
  exact or.resolve_right this hα,
end

/-- A dilation from a metric space is a uniform inducing map -/
theorem uniform_inducing (hr : ratio f ≠ 0) :
  uniform_inducing (f : α → β) :=
(antilipschitz f hr).uniform_inducing (lipschitz f).uniform_continuous

lemma tendsto_nhds_iff {ι : Type*} {g : ι → α} {a : filter ι} {b : α} (hr : ratio f ≠ 0) :
  filter.tendsto g a (𝓝 b) ↔ filter.tendsto ((f : α → β) ∘ g) a (𝓝 (f b)) :=
(uniform_inducing f hr).inducing.tendsto_nhds_iff

/-- A dilation is continuous. -/
lemma to_continuous : continuous (f : α → β) :=
(lipschitz f).continuous

/-- Dilations multiply the diameter by their ratio in pseudoemetric spaces. -/
lemma ediam_image (s : set α) :
  emetric.diam ((f: α → β) '' s) = ratio f * emetric.diam s :=
begin
  apply le_antisymm,
  { exact lipschitz_with.ediam_image_le (lipschitz f) s },
  by_cases hr : ratio f ≠ 0,
  { rw [mul_comm, ← ennreal.le_div_iff_mul_le, div_eq_mul_inv, mul_comm, ← ennreal.coe_inv hr],
    refine antilipschitz_with.le_mul_ediam_image (antilipschitz f hr) s,
    left, simp [hr],
    left, simp [hr], },
  rw not_not at hr,
  simp [hr],
end

lemma ediam_range :
  emetric.diam (range (f : α → β)) = ratio f * emetric.diam (univ : set α) :=
by { rw ← image_univ, exact ediam_image f univ }

lemma maps_to_emetric_ball  (hr : ratio f ≠ 0) (x : α) (r' : ℝ≥0∞) :
  maps_to (f : α → β) (emetric.ball x r') (emetric.ball (f x) (ratio f * r')) :=
begin
  intros y hy,
  simp only [emetric.mem_ball, edist_eq] at *,
  rwa ennreal.mul_lt_mul_left _ _,
  simp [hr],
  simp [hr],
end

lemma maps_to_emetric_closed_ball (x : α) (r' : ℝ≥0∞) :
  maps_to (f : α → β) (emetric.closed_ball x r') (emetric.closed_ball (f x) (ratio f * r')) :=
begin
  by_cases hr : ratio f ≠ 0,
  { intros y hy,
    simp only [emetric.mem_closed_ball, edist_eq] at *,
    rwa ennreal.mul_le_mul_left _ _,
    simp [hr],
    simp [hr], },
  rw not_not at hr,
  simp [hr, maps_to],
end

lemma comp_continuous_on_iff
  {γ} [topological_space γ] {g : γ → α} {s : set γ} (hr : ratio f ≠ 0) :
  continuous_on ((f : α → β) ∘ g) s ↔ continuous_on g s :=
(uniform_inducing f hr).inducing.continuous_on_iff.symm

lemma comp_continuous_iff
  {γ} [topological_space γ] {g : γ → α} (hr : ratio f ≠ 0) :
  continuous ((f : α → β) ∘ g) ↔ continuous g :=
(uniform_inducing f hr).inducing.continuous_iff.symm

end pseudo_emetric_dilation --section

section emetric_dilation
variables [emetric_space α]

/-- A dilation from a metric space is a uniform embedding -/
theorem uniform_embedding [pseudo_emetric_space β] [dilation_class F α β]
  (f : F) (hr : ratio f ≠ 0) : uniform_embedding f :=
(antilipschitz f hr).uniform_embedding (lipschitz f).uniform_continuous

/-- A dilation from a metric space is an embedding -/
theorem embedding [pseudo_emetric_space β] [dilation_class F α β]
  (f : F) (hr : ratio f ≠ 0) : embedding (f : α → β) :=
(uniform_embedding f hr).embedding

/-- A dilation from a complete emetric space is a closed embedding -/
theorem closed_embedding
  [complete_space α] [emetric_space β] [dilation_class F α β]
  (f : F) (hr : ratio f ≠ 0) : closed_embedding (f : α → β) :=
(antilipschitz f hr).closed_embedding (lipschitz f).uniform_continuous

end emetric_dilation --section

section pseudo_metric_dilation
variables [pseudo_metric_space α] [pseudo_metric_space β] [dilation_class F α β] (f : F)

/-- A dilation preserves the diameter in pseudometric spaces. -/
lemma diam_image (s : set α) : metric.diam ((f : α → β) '' s) = ratio f * metric.diam s :=
by { simp [metric.diam, metric.diam, ediam_image, ennreal.to_real_mul], }

lemma diam_range : metric.diam (range (f : α → β)) = ratio f * metric.diam (univ : set α) :=
by rw [← image_univ, diam_image]

lemma maps_to_ball (hr : ratio f ≠ 0) (x : α) (r' : ℝ) :
  maps_to (f : α → β) (metric.ball x r') (metric.ball (f x) (ratio f * r')) :=
begin
  intros y hy,
  rw [metric.mem_ball, dist_eq],
  refine mul_lt_mul' (le_refl _) _ dist_nonneg _,
  rwa metric.mem_ball at hy,
  rwa [nnreal.coe_pos, pos_iff_ne_zero],
end

lemma maps_to_sphere (x : α) (r' : ℝ) :
  maps_to (f : α → β) (metric.sphere x r') (metric.sphere (f x) (ratio f * r')) :=
begin
  intros y hy,
  rw metric.mem_sphere at hy,
  rw [metric.mem_sphere, dist_eq, hy],
end

lemma maps_to_closed_ball (x : α) (r' : ℝ) :
  maps_to (f : α → β) (metric.closed_ball x r') (metric.closed_ball (f x) (ratio f * r')) :=
begin
  intros y hy,
  rw [metric.mem_closed_ball] at hy,
  rw [metric.mem_closed_ball, dist_eq],
  refine mul_le_mul (le_refl _) hy dist_nonneg nnreal.zero_le_coe,
end

end pseudo_metric_dilation -- section

end dilation
