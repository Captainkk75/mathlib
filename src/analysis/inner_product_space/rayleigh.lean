/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/
import analysis.inner_product_space.calculus
import analysis.inner_product_space.dual
import analysis.inner_product_space.adjoint
import analysis.calculus.lagrange_multipliers
import analysis.normed_space.compact_map
import linear_algebra.eigenspace
import algebra.star.self_adjoint

/-!
# The Rayleigh quotient

The Rayleigh quotient of a self-adjoint operator `T` on an inner product space `E` is the function
`λ x, ⟪T x, x⟫ / ∥x∥ ^ 2`.

The main results of this file are `is_self_adjoint.has_eigenvector_of_is_max_on` and
`is_self_adjoint.has_eigenvector_of_is_min_on`, which state that if `E` is complete, and if the
Rayleigh quotient attains its global maximum/minimum over some sphere at the point `x₀`, then `x₀`
is an eigenvector of `T`, and the `supr`/`infi` of `λ x, ⟪T x, x⟫ / ∥x∥ ^ 2` is the corresponding
eigenvalue.

The corollaries `is_self_adjoint.has_eigenvalue_supr_of_finite_dimensional` and
`is_self_adjoint.has_eigenvalue_supr_of_finite_dimensional` state that if `E` is finite-dimensional
and nontrivial, then `T` has some (nonzero) eigenvectors with eigenvalue the `supr`/`infi` of
`λ x, ⟪T x, x⟫ / ∥x∥ ^ 2`.

## TODO

A slightly more elaborate corollary is that if `E` is complete and `T` is a compact operator, then
`T` has some (nonzero) eigenvector with eigenvalue either `⨆ x, ⟪T x, x⟫ / ∥x∥ ^ 2` or
`⨅ x, ⟪T x, x⟫ / ∥x∥ ^ 2` (not necessarily both).

-/

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y
open_locale nnreal complex_conjugate topological_space filter

open module.End metric

namespace continuous_linear_map
variables (T : E →L[𝕜] E)
local notation `rayleigh_quotient` := λ x : E, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2

lemma rayleigh_smul (x : E) {c : 𝕜} (hc : c ≠ 0) :
  rayleigh_quotient (c • x) = rayleigh_quotient x :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  have : ∥c∥ ≠ 0 := by simp [hc],
  have : ∥x∥ ≠ 0 := by simp [hx],
  field_simp [norm_smul, T.re_apply_inner_self_smul],
  ring
end

lemma image_rayleigh_eq_image_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  rayleigh_quotient '' {0}ᶜ = rayleigh_quotient '' (sphere 0 r) :=
begin
  ext a,
  split,
  { rintros ⟨x, (hx : x ≠ 0), hxT⟩,
    have : ∥x∥ ≠ 0 := by simp [hx],
    let c : 𝕜 := ↑∥x∥⁻¹ * r,
    have : c ≠ 0 := by simp [c, hx, hr.ne'],
    refine ⟨c • x, _, _⟩,
    { field_simp [norm_smul, is_R_or_C.norm_eq_abs, abs_of_nonneg hr.le] },
    { rw T.rayleigh_smul x this,
      exact hxT } },
  { rintros ⟨x, hx, hxT⟩,
    exact ⟨x, nonzero_of_mem_sphere hr ⟨x, hx⟩, hxT⟩ },
end

lemma supr_rayleigh_eq_supr_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  (⨆ x : {x : E // x ≠ 0}, rayleigh_quotient x) = ⨆ x : sphere (0:E) r, rayleigh_quotient x :=
show (⨆ x : ({0} : set E)ᶜ, rayleigh_quotient x) = _,
by simp only [@csupr_set _ _ _ _ rayleigh_quotient, T.image_rayleigh_eq_image_rayleigh_sphere hr]

lemma infi_rayleigh_eq_infi_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  (⨅ x : {x : E // x ≠ 0}, rayleigh_quotient x) = ⨅ x : sphere (0:E) r, rayleigh_quotient x :=
show (⨅ x : ({0} : set E)ᶜ, rayleigh_quotient x) = _,
by simp only [@cinfi_set _ _ _ _ rayleigh_quotient, T.image_rayleigh_eq_image_rayleigh_sphere hr]

lemma rayleigh_le_norm (x : E) : rayleigh_quotient x ≤ ∥T∥ :=
begin
  by_cases hx : x = 0,
  { simp only [hx, div_zero, nat.one_ne_zero, norm_zero, ne.def, norm_nonneg, not_false_iff,
               bit0_eq_zero, zero_pow'] },
  have h : T.re_apply_inner_self x ≤ ∥T x∥ * ∥x∥ := re_inner_le_norm (T x) x,
  refine (div_le_iff _).mpr _,
  refine pow_two_pos_of_ne_zero _ (ne_of_gt (norm_pos_iff.mpr hx)),
  calc _ ≤ ∥T x∥ * ∥x∥       : h
      ... ≤ ∥T∥ * ∥x∥ * ∥x∥  : mul_le_mul_of_nonneg_right (le_op_norm _ _) (norm_nonneg _)
      ... = ∥T∥ * ∥x∥ ^ 2    : by rw [mul_assoc, pow_two],
end

lemma neg_rayleigh_le_norm (x : E) : -rayleigh_quotient x ≤ ∥T∥ :=
begin
  have h := rayleigh_le_norm (-T) x,
  rw [norm_neg] at h,
  simp only [re_apply_inner_self, neg_apply, inner_neg_left, add_monoid_hom.map_neg] at h,
  simp only [re_apply_inner_self, ←neg_div, h],
end

lemma supr_rayleigh_le_norm : (⨆ x, rayleigh_quotient x) ≤ ∥T∥ :=
csupr_le (λ x, rayleigh_le_norm T x)

lemma supr_neg_rayleigh_le_norm : (⨆ x, -rayleigh_quotient x) ≤ ∥T∥ :=
csupr_le (λ x, neg_rayleigh_le_norm T x)

lemma rayleigh_bdd_above : bdd_above (set.range rayleigh_quotient) :=
begin
  refine set.nonempty_def.mpr ⟨∥T∥, mem_upper_bounds.mpr (λ x hx, _)⟩,
  rw [set.mem_range] at hx,
  rcases hx with ⟨y, hy⟩,
  rw [←hy],
  exact rayleigh_le_norm T y
end

lemma neg_rayleigh_bdd_above : bdd_above (set.range (-rayleigh_quotient)) :=
begin
  refine set.nonempty_def.mpr ⟨∥T∥, mem_upper_bounds.mpr (λ x hx, _)⟩,
  rw [set.mem_range] at hx,
  rcases hx with ⟨y, hy⟩,
  rw [←hy],
  exact neg_rayleigh_le_norm T y
end

lemma supr_rayleigh_nonneg : (0 : ℝ) ≤ (⨆ x, rayleigh_quotient x) :=
le_csupr_of_le (rayleigh_bdd_above T) 0 (by simp)

lemma supr_neg_rayleigh_nonneg : (0 : ℝ) ≤ (⨆ x, (-rayleigh_quotient) x) :=
le_csupr_of_le (neg_rayleigh_bdd_above T) 0 (by simp)

lemma re_apply_inner_self_eq_rayleigh_mul_norm_sq (x : E) :
  T.re_apply_inner_self x = (rayleigh_quotient x) * ∥x∥ ^ 2 :=
begin
  by_cases h : ∥x∥ = 0,
  { rw [norm_eq_zero] at h,
    simp [re_apply_inner_self, h] },
  change ∥x∥ ≠ 0 at h,
  field_simp [re_apply_inner_self],
end

lemma re_apply_inner_self_le_supr_rayleigh_mul_norm_sq (x : E) :
  T.re_apply_inner_self x ≤ (⨆ z, rayleigh_quotient z) * ∥x∥ ^ 2 :=
begin
  rw [re_apply_inner_self_eq_rayleigh_mul_norm_sq T x],
  refine mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) 2),
  exact le_csupr (rayleigh_bdd_above T) _,
end

lemma re_apply_inner_self_le_max_supr_rayleigh_mul_norm_sq (x : E) :
  T.re_apply_inner_self x ≤
    max (⨆ z, rayleigh_quotient z) (⨆ z, (-rayleigh_quotient) z) * ∥x∥ ^ 2 :=
le_trans (re_apply_inner_self_le_supr_rayleigh_mul_norm_sq T x) $
  mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ∥x∥)

lemma neg_re_apply_inner_self_le_supr_rayleigh_mul_norm_sq (x : E) :
  -T.re_apply_inner_self x ≤ (⨆ z, (-rayleigh_quotient) z) * ∥x∥ ^ 2 :=
begin
  rw [re_apply_inner_self_eq_rayleigh_mul_norm_sq T x],
  simp only [neg_mul_eq_neg_mul],
  refine mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) 2),
  exact le_csupr (neg_rayleigh_bdd_above T) _,
end

lemma neg_re_apply_inner_self_le_max_supr_rayleigh_mul_norm_sq (x : E) :
  -T.re_apply_inner_self x ≤
    max (⨆ z, rayleigh_quotient z) (⨆ z, (-rayleigh_quotient) z) * ∥x∥ ^ 2 :=
le_trans (neg_re_apply_inner_self_le_supr_rayleigh_mul_norm_sq T x) $
  mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg ∥x∥)

lemma _root_.is_R_or_C.of_real_mul_inv_re (r : ℝ) (z : 𝕜) :
  is_R_or_C.re ((r : 𝕜)⁻¹ * z) = r⁻¹ * is_R_or_C.re z :=
by rw [←is_R_or_C.of_real_inv, is_R_or_C.of_real_mul_re]

lemma _root_.is_R_or_C.of_real_mul_conj_re (r : ℝ) (z : 𝕜) :
  is_R_or_C.re ((conj (r : 𝕜)) * z) = r * is_R_or_C.re z :=
begin
  simp only [is_R_or_C.conj_of_real, is_R_or_C.mul_re, zero_mul, is_R_or_C.of_real_re, sub_zero, is_R_or_C.of_real_im],
end

lemma _root_.is_R_or_C.of_real_mul_conj_inv_re (r : ℝ) (z : 𝕜) :
  is_R_or_C.re ((conj (r⁻¹ : 𝕜)) * z) = r⁻¹ * is_R_or_C.re z :=
by rw [←is_R_or_C.of_real_inv, is_R_or_C.of_real_mul_conj_re]


end continuous_linear_map

namespace inner_product_space
namespace is_self_adjoint

section general
open continuous_linear_map

variables {T : E →L[𝕜] E}
local notation `rayleigh_quotient` := λ x : E, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2

lemma norm_eq_max_supr_rayleigh_sphere (hT : is_self_adjoint T.to_linear_map) :
  ∥T∥ = max (⨆ x : sphere (0:E) 1, T.re_apply_inner_self x)
            (⨆ x : sphere (0:E) 1, -T.re_apply_inner_self x) :=
begin
  refine op_norm_eq_of_bounds _ (λ x, _) _,
  { sorry },
  { set L := real.sqrt (∥T x∥ / ∥x∥) with hL,
    set rT := max (⨆ z : sphere (0:E) 1, T.re_apply_inner_self z)
                  (⨆ z : sphere (0:E) 1, -T.re_apply_inner_self z) with hrT,
    set x₁ := (L : 𝕜) • x + (L⁻¹ : 𝕜) • (T x) with hx₁,
    set x₂ := (L : 𝕜) • x - (L⁻¹ : 𝕜) • (T x) with hx₂,
    by_cases h_ntriv : T x = 0,
    { simp only [h_ntriv, norm_zero],
      --exact mul_nonneg (le_max_iff.mpr (or.inl (supr_rayleigh_nonneg T))) (norm_nonneg _),
      sorry },
    change T x ≠ 0 at h_ntriv,
    have hTx_ntriv : ∥T x∥ ≠ 0 := λ H, by { rw [norm_eq_zero] at H, exact h_ntriv H },
    have hx_ntriv : ∥x∥ ≠ 0,
    { intro H,
      rw [norm_eq_zero] at H,
      rw [H] at h_ntriv,
      exact h_ntriv (map_zero _) },
    have hL_nonneg : 0 ≤ L := real.sqrt_nonneg _,
    have hLinv_nonneg : 0 ≤ L⁻¹ := inv_nonneg.mpr hL_nonneg,
    have hL_sq : L^2 = ∥T x∥ / ∥x∥ := real.sq_sqrt (div_nonneg (norm_nonneg _) (norm_nonneg _)),
    have hLinv_sq_nonneg : 0 ≤ ∥x∥ / ∥T x∥ := div_nonneg (norm_nonneg _) (norm_nonneg _),
    have hL_sq_nonneg : 0 ≤ ∥T x∥ / ∥x∥ := div_nonneg (norm_nonneg _) (norm_nonneg _),
    have hLinv_sq : (L⁻¹)^2 = ∥x∥ / ∥T x∥,
    { simp only [←real.sqrt_inv, inv_div],
      rw [real.sq_sqrt hLinv_sq_nonneg] },
    have hL_ntriv : L ≠ 0,
    { intro H,
      rw [real.sqrt_eq_zero hL_sq_nonneg, div_eq_zero_iff] at H,
      exact or.elim H hTx_ntriv hx_ntriv },
    have hL_mul₁ : L * L⁻¹ = 1 := mul_inv_cancel hL_ntriv,
    have hL_mul₂ : L⁻¹ * L = 1 := (mul_comm L L⁻¹) ▸ hL_mul₁,
    have gizmo : ⟪T (T x), x⟫ = ⟪T x, T x⟫ := hT _ _,
    have h₁ : T.re_apply_inner_self x₁ - T.re_apply_inner_self x₂ = 4 * ∥T x∥ ^ 2,
    { simp only [hx₁, hx₂, re_apply_inner_self_apply, inner_add_left, inner_add_right, inner_smul_left,
            inner_smul_right, ←inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
            hL_mul₁, hL_mul₂, is_R_or_C.of_real_mul_re, is_R_or_C.re.map_add, is_R_or_C.re.map_sub,
            is_R_or_C.of_real_mul_inv_re, continuous_linear_map.map_add, continuous_linear_map.map_sub,
            continuous_linear_map.map_smul, is_R_or_C.of_real_mul_conj_re, is_R_or_C.of_real_mul_conj_inv_re, gizmo],
      ring_nf,
      field_simp },
    have h₄ : T.re_apply_inner_self x₁ ≤ rT * ∥x₁∥^2 := sorry,
      --re_apply_inner_self_le_max_supr_rayleigh_mul_norm_sq _ _,
    have h₅ : -T.re_apply_inner_self x₂ ≤ rT * ∥x₂∥^2 := sorry,
      --neg_re_apply_inner_self_le_max_supr_rayleigh_mul_norm_sq _ _,
    have h₆ := calc
      4 * ∥T x∥^2 ≤ rT * ∥x₁∥^2 + rT * ∥x₂∥^2          : by { rw [←h₁, sub_eq_add_neg], exact add_le_add h₄ h₅ }
             ...  = rT * (∥x₁∥ * ∥x₁∥) + rT * (∥x₂∥ * ∥x₂∥)      : by simp only [pow_two]
             ...  = rT * (∥x₁∥ * ∥x₁∥ + ∥x₂∥ * ∥x₂∥)     : by ring
             ...  = rT * (2 * (L^2 * ∥x∥ * ∥x∥ + (L⁻¹)^2 * ∥T x∥ * ∥T x∥)) :
              begin
                simp only [parallelogram_law_with_norm, norm_smul, is_R_or_C.norm_of_real,
                           real.norm_of_nonneg hL_nonneg, real.norm_of_nonneg hLinv_nonneg,
                           ←is_R_or_C.of_real_inv],
                ring
              end
             ...  = 4 * rT * ∥T x∥ * ∥x∥  :
              begin
                simp only [hL_sq, hLinv_sq],
                field_simp,
                ring
              end,
    have h₇ : 0 < 4 * ∥T x∥ := mul_pos (by norm_num) (norm_pos_iff.mpr h_ntriv),
    rw [←mul_le_mul_left h₇],
    calc 4 * ∥T x∥ * ∥T x∥ = 4 * ∥T x∥ ^ 2          : by rw [mul_assoc, ←pow_two]
                      ... ≤ 4 * rT * ∥T x∥ * ∥x∥   : h₆
                      ... = _                      : by ring },
  { sorry },
  --{ intros N hN h,
  --  refine max_le _ _,
  --  { refine csupr_le (λ x, _),
  --    by_cases h_ntriv : x = 0,
  --    { have : (0 : ℝ)^2 = 0 := by rw [pow_two, mul_zero],
  --      simp only [h_ntriv, norm_zero, this, div_zero _],
  --      exact hN },
  --    change x ≠ 0 at h_ntriv,
  --    refine (div_le_iff _).mpr _,
  --    { rw pow_two,
  --      rw [←norm_pos_iff] at h_ntriv,
  --      exact mul_pos h_ntriv h_ntriv },
  --    simp only [T.re_apply_inner_self_apply],
  --    refine le_trans (re_inner_le_norm (T x) x) _,
  --    rw [pow_two, ←mul_assoc],
  --    refine mul_le_mul_of_nonneg_right (h x) (norm_nonneg _) },
  --  { refine csupr_le (λ x, _),
  --    by_cases h_ntriv : x = 0,
  --    { have : (0 : ℝ)^2 = 0 := by rw [pow_two, mul_zero],
  --      simp only [h_ntriv, norm_zero, this, div_zero, pi.neg_apply, neg_zero],
  --      exact hN },
  --    change x ≠ 0 at h_ntriv,
  --    dsimp,
  --    rw [←neg_div],
  --    refine (div_le_iff _).mpr _,
  --    { rw pow_two,
  --      rw [←norm_pos_iff] at h_ntriv,
  --      exact mul_pos h_ntriv h_ntriv },
  --    simp only [T.re_apply_inner_self_apply, ←map_neg, ←inner_neg_right],
  --    refine le_trans (re_inner_le_norm (T x) (-x)) _,
  --    rw [norm_neg, pow_two, ←mul_assoc],
  --    refine mul_le_mul_of_nonneg_right (h x) (norm_nonneg _) } }
end

end general

section real
variables {F : Type*} [inner_product_space ℝ F]

lemma has_strict_fderiv_at_re_apply_inner_self
  {T : F →L[ℝ] F} (hT : is_self_adjoint (T : F →ₗ[ℝ] F)) (x₀ : F) :
  has_strict_fderiv_at T.re_apply_inner_self (bit0 (innerSL (T x₀))) x₀ :=
begin
  convert T.has_strict_fderiv_at.inner (has_strict_fderiv_at_id x₀),
  ext y,
  simp [bit0, hT.apply_clm x₀ y, real_inner_comm x₀]
end

variables [complete_space F] {T : F →L[ℝ] F}
local notation `rayleigh_quotient` := λ x : F, T.re_apply_inner_self x / ∥(x:F)∥ ^ 2

lemma linearly_dependent_of_is_local_extr_on (hT : is_self_adjoint (T : F →ₗ[ℝ] F))
  {x₀ : F} (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:F) ∥x₀∥) x₀) :
  ∃ a b : ℝ, (a, b) ≠ 0 ∧ a • x₀ + b • T x₀ = 0 :=
begin
  have H : is_local_extr_on T.re_apply_inner_self {x : F | ∥x∥ ^ 2 = ∥x₀∥ ^ 2} x₀,
  { convert hextr,
    ext x,
    simp [dist_eq_norm] },
  -- find Lagrange multipliers for the function `T.re_apply_inner_self` and the
  -- hypersurface-defining function `λ x, ∥x∥ ^ 2`
  obtain ⟨a, b, h₁, h₂⟩ := is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at_1d H
    (has_strict_fderiv_at_norm_sq x₀) (hT.has_strict_fderiv_at_re_apply_inner_self x₀),
  refine ⟨a, b, h₁, _⟩,
  apply (inner_product_space.to_dual_map ℝ F).injective,
  simp only [linear_isometry.map_add, linear_isometry.map_smul, linear_isometry.map_zero],
  change a • innerSL x₀ + b • innerSL (T x₀) = 0,
  apply smul_right_injective (F →L[ℝ] ℝ) (two_ne_zero : (2:ℝ) ≠ 0),
  simpa only [bit0, add_smul, smul_add, one_smul, add_zero] using h₂
end

lemma eq_smul_self_of_is_local_extr_on_real (hT : is_self_adjoint (T : F →ₗ[ℝ] F))
  {x₀ : F} (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:F) ∥x₀∥) x₀) :
  T x₀ = (rayleigh_quotient x₀) • x₀ :=
begin
  obtain ⟨a, b, h₁, h₂⟩ := hT.linearly_dependent_of_is_local_extr_on hextr,
  by_cases hx₀ : x₀ = 0,
  { simp [hx₀] },
  by_cases hb : b = 0,
  { have : a ≠ 0 := by simpa [hb] using h₁,
    refine absurd _ hx₀,
    apply smul_right_injective F this,
    simpa [hb] using h₂ },
  let c : ℝ := - b⁻¹ * a,
  have hc : T x₀ = c • x₀,
  { have : b * (b⁻¹ * a) = a := by field_simp [mul_comm],
    apply smul_right_injective F hb,
    simp [c, ← neg_eq_of_add_eq_zero h₂, ← mul_smul, this] },
  convert hc,
  have : ∥x₀∥ ≠ 0 := by simp [hx₀],
  field_simp,
  simpa [inner_smul_left, real_inner_self_eq_norm_mul_norm, sq] using congr_arg (λ x, ⟪x, x₀⟫_ℝ) hc,
end

end real

section complete_space
variables [complete_space E] {T : E →L[𝕜] E}
local notation `rayleigh_quotient` := λ x : E, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2

lemma eq_smul_self_of_is_local_extr_on (hT : is_self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  T x₀ = (↑(rayleigh_quotient x₀) : 𝕜) • x₀ :=
begin
  letI := inner_product_space.is_R_or_C_to_real 𝕜 E,
  let S : E →L[ℝ] E :=
    @continuous_linear_map.restrict_scalars 𝕜 E E _ _ _ _ _ _ _ ℝ _ _ _ _ T,
  have hSA : is_self_adjoint (S : E →ₗ[ℝ] E) := λ x y, by
  { have := hT x y,
    simp only [continuous_linear_map.coe_coe] at this,
    simp only [real_inner_eq_re_inner, this, continuous_linear_map.coe_restrict_scalars,
      continuous_linear_map.coe_coe, linear_map.coe_restrict_scalars_eq_coe] },
  exact eq_smul_self_of_is_local_extr_on_real hSA hextr,
end

/-- For a self-adjoint operator `T`, a local extremum of the Rayleigh quotient of `T` on a sphere
centred at the origin is an eigenvector of `T`. -/
lemma has_eigenvector_of_is_local_extr_on (hT : is_self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) ↑(rayleigh_quotient x₀) x₀ :=
begin
  refine ⟨_, hx₀⟩,
  rw module.End.mem_eigenspace_iff,
  exact hT.eq_smul_self_of_is_local_extr_on hextr
end

/-- For a self-adjoint operator `T`, a maximum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global supremum of the Rayleigh
quotient. -/
lemma has_eigenvector_of_is_max_on (hT : is_self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_max_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) ↑(⨆ x : {x : E // x ≠ 0}, rayleigh_quotient x) x₀ :=
begin
  convert hT.has_eigenvector_of_is_local_extr_on hx₀ (or.inr hextr.localize),
  have hx₀' : 0 < ∥x₀∥ := by simp [hx₀],
  have hx₀'' : x₀ ∈ sphere (0:E) (∥x₀∥) := by simp,
  rw T.supr_rayleigh_eq_supr_rayleigh_sphere hx₀',
  refine is_max_on.supr_eq hx₀'' _,
  intros x hx,
  dsimp,
  have : ∥x∥ = ∥x₀∥ := by simpa using hx,
  rw this,
  exact div_le_div_of_le (sq_nonneg ∥x₀∥) (hextr hx)
end

/-- For a self-adjoint operator `T`, a minimum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global infimum of the Rayleigh
quotient. -/
lemma has_eigenvector_of_is_min_on (hT : is_self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_min_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) ↑(⨅ x : {x : E // x ≠ 0}, rayleigh_quotient x) x₀ :=
begin
  convert hT.has_eigenvector_of_is_local_extr_on hx₀ (or.inl hextr.localize),
  have hx₀' : 0 < ∥x₀∥ := by simp [hx₀],
  have hx₀'' : x₀ ∈ sphere (0:E) (∥x₀∥) := by simp,
  rw T.infi_rayleigh_eq_infi_rayleigh_sphere hx₀',
  refine is_min_on.infi_eq hx₀'' _,
  intros x hx,
  dsimp,
  have : ∥x∥ = ∥x₀∥ := by simpa using hx,
  rw this,
  exact div_le_div_of_le (sq_nonneg ∥x₀∥) (hextr hx)
end

end complete_space

section compact
variables [complete_space E] {T : E →L[𝕜] E}

local notation `rayleigh_quotient` := λ x : E, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2
local notation `rayleigh_quotient_sphere` := λ x : sphere (0:E) 1, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2
lemma exists_eigenvalue_of_compact [nontrivial E] (hT : is_self_adjoint T.to_linear_map)
  (hT_cpct : compact_map T) :
  ∃ c, has_eigenvalue T.to_linear_map c :=
begin
  haveI : nonempty (sphere (0:E) 1) := sorry,
  by_cases h_triv : T = 0,
  { rcases exists_ne (0 : E) with ⟨w, hw⟩,
    refine ⟨0, has_eigenvalue_of_has_eigenvector ⟨_, hw⟩⟩,
    simp only [mem_eigenspace_iff, h_triv, zero_smul, continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_zero,
              linear_map.zero_apply] },
  { change T ≠ 0 at h_triv,
    --have h₁ := exists_seq_tendsto_Inf (set.nonempty_def.mpr (@continuous_linear_map.bounds_nonempty _ _ _ _ _ _ _ _ _ _ _ _ T)) (continuous_linear_map.bounds_bdd_below),
    --rcases h₁ with ⟨u, ⟨h_antitone, ⟨hu₁,hu₂⟩⟩⟩,
    rcases max_eq_iff.mp (norm_eq_max_supr_rayleigh_sphere hT).symm with ⟨h_supr,-⟩|⟨h_infi,-⟩,
    { set a := (⨆ x, rayleigh_quotient_sphere x),
      refine ⟨a, _⟩,
      --have h₁' : (set.range rayleigh_quotient).nonempty := ⟨0, ⟨0, by simp⟩⟩,
      -- First use filter.comap applied to nhds (supr) to get a filter f₁ on vectors
      set f₁ : filter (sphere (0:E) 1) :=
        filter.comap (λ x, rayleigh_quotient x) (𝓝[set.range rayleigh_quotient_sphere] a),
      set f₂ : filter E := filter.map (λ x : sphere (0:E) 1, T x) f₁,
      set f₃ : filter E := filter.map (λ x : sphere (0:E) 1, (a : 𝕜) • x) f₁,
      have h_bdd_range : bdd_above (set.range rayleigh_quotient_sphere),
      { sorry },
      have h_range_nonempty : (set.range rayleigh_quotient_sphere).nonempty,
      { sorry },
      have h_ne_bot : (𝓝[set.range rayleigh_quotient_sphere] a).ne_bot :=
        is_lub.nhds_within_ne_bot (is_lub_csupr h_bdd_range) h_range_nonempty,
      have hf₂ : f₂ ≤ 𝓟 (set.range (λ x : sphere (0:E) 1, T x)) := by
      { rw [filter.le_principal_iff, filter.mem_map, filter.mem_comap],
        sorry },
      haveI f₁_ne_bot : f₁.ne_bot :=
        filter.ne_bot.comap_of_range_mem h_ne_bot self_mem_nhds_within,
      haveI f₂_ne_bot : f₂.ne_bot := by apply_instance,
      haveI f₃_ne_bot : f₃.ne_bot := by apply_instance,
      -- The image of T on the sphere is compact since T is a compact operator
      have h_img_cpct : is_compact (set.range (λ x : sphere (0:E) 1, T x)),
      { sorry },
      -- f₂ is guaranteed to have a cluster point z for some vector z by compactness of T
      have hf₂' := h_img_cpct hf₂,
      rcases hf₂' with ⟨z, ⟨hz₁, hz₂⟩⟩,
      set f₄ : filter (sphere (0:E) 1) := filter.comap (λ x, T x) (𝓝 z),
      -- show that z is also a cluster point of f₃
      have hz' : cluster_pt z f₃,
      { sorry },
      refine has_eigenvalue_of_has_eigenvector ⟨_, show (a⁻¹ : 𝕜) • z ≠ 0, from _⟩,
      { rw [mem_eigenspace_iff],
        simp only [smul_smul, continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe, continuous_linear_map.map_smul],
        rw [mul_comm, ←smul_smul],
        congr,
        refine eq_of_nhds_ne_bot _,
        sorry },
      { sorry },
      -- Use tendsto_iff_dist_tendsto_zero to show f₁ also converges to nhds z
      -- Declare z as the eigenvector
      },
    { sorry }
  }
  -- is_lub_csupr   ι 𝕜 E
end

lemma subsingleton_of_no_eigenvalue_of_compact (hT : is_self_adjoint T.to_linear_map)
  (hT_cpct : compact_map T) (hT' : ∀ μ : 𝕜, module.End.eigenspace (T : E →ₗ[𝕜] E) μ = ⊥) :
  subsingleton E :=
(subsingleton_or_nontrivial E).resolve_right
  (λ h, by exactI absurd (hT' _) (hT.exists_eigenvalue_of_compact hT_cpct).some_spec)

end compact


section finite_dimensional
variables [finite_dimensional 𝕜 E] [_i : nontrivial E] {T : E →ₗ[𝕜] E}

include _i

/-- The supremum of the Rayleigh quotient of a self-adjoint operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
lemma has_eigenvalue_supr_of_finite_dimensional (hT : is_self_adjoint T) :
  has_eigenvalue T ↑(⨆ x : {x : E // x ≠ 0}, is_R_or_C.re ⟪T x, x⟫ / ∥(x:E)∥ ^ 2) :=
begin
  haveI := finite_dimensional.proper_is_R_or_C 𝕜 E,
  let T' : E →L[𝕜] E := T.to_continuous_linear_map,
  have hT' : is_self_adjoint (T' : E →ₗ[𝕜] E) := hT,
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
  have H₁ : is_compact (sphere (0:E) ∥x∥) := is_compact_sphere _ _,
  have H₂ : (sphere (0:E) ∥x∥).nonempty := ⟨x, by simp⟩,
  -- key point: in finite dimension, a continuous function on the sphere has a max
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_forall_ge H₂ T'.re_apply_inner_self_continuous.continuous_on,
  have hx₀ : ∥x₀∥ = ∥x∥ := by simpa using hx₀',
  have : is_max_on T'.re_apply_inner_self (sphere 0 ∥x₀∥) x₀,
  { simpa only [← hx₀] using hTx₀ },
  have hx₀_ne : x₀ ≠ 0,
  { have : ∥x₀∥ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, ne.def, not_false_iff],
    simpa [← norm_eq_zero, ne.def] },
  exact has_eigenvalue_of_has_eigenvector (hT'.has_eigenvector_of_is_max_on hx₀_ne this)
end

/-- The infimum of the Rayleigh quotient of a self-adjoint operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
lemma has_eigenvalue_infi_of_finite_dimensional (hT : is_self_adjoint T) :
  has_eigenvalue T ↑(⨅ x : {x : E // x ≠ 0}, is_R_or_C.re ⟪T x, x⟫ / ∥(x:E)∥ ^ 2) :=
begin
  haveI := finite_dimensional.proper_is_R_or_C 𝕜 E,
  let T' : E →L[𝕜] E := T.to_continuous_linear_map,
  have hT' : is_self_adjoint (T' : E →ₗ[𝕜] E) := hT,
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
  have H₁ : is_compact (sphere (0:E) ∥x∥) := is_compact_sphere _ _,
  have H₂ : (sphere (0:E) ∥x∥).nonempty := ⟨x, by simp⟩,
  -- key point: in finite dimension, a continuous function on the sphere has a min
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_forall_le H₂ T'.re_apply_inner_self_continuous.continuous_on,
  have hx₀ : ∥x₀∥ = ∥x∥ := by simpa using hx₀',
  have : is_min_on T'.re_apply_inner_self (sphere 0 ∥x₀∥) x₀,
  { simpa only [← hx₀] using hTx₀ },
  have hx₀_ne : x₀ ≠ 0,
  { have : ∥x₀∥ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, ne.def, not_false_iff],
    simpa [← norm_eq_zero, ne.def] },
  exact has_eigenvalue_of_has_eigenvector (hT'.has_eigenvector_of_is_min_on hx₀_ne this)
end

omit _i

lemma subsingleton_of_no_eigenvalue_finite_dimensional
  (hT : is_self_adjoint T) (hT' : ∀ μ : 𝕜, module.End.eigenspace (T : E →ₗ[𝕜] E) μ = ⊥) :
  subsingleton E :=
(subsingleton_or_nontrivial E).resolve_right
  (λ h, by exactI absurd (hT' _) hT.has_eigenvalue_supr_of_finite_dimensional)

end finite_dimensional

end is_self_adjoint
end inner_product_space
