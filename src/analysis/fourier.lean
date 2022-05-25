/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.complex.circle
import analysis.special_functions.complex.circle
import analysis.special_functions.complex.log
import analysis.inner_product_space.l2_space
import measure_theory.function.continuous_map_dense
import measure_theory.function.l2_space
import measure_theory.measure.haar
import measure_theory.group.integration
import measure_theory.integral.circle_integral
import analysis.special_functions.integrals
import topology.metric_space.emetric_paracompact
import topology.continuous_function.stone_weierstrass

/-!

# Fourier analysis on the circle

This file contains basic results on Fourier series.

## Main definitions

* `circle_measure`: measure on the circle transported from the measure `1 / (2 * π) • volume` on
  `(-π, π]` via `exp_map_circle`.
* instances `measure_space`, `is_probability_measure` for the circle with respect to this measure.
* for `n : ℤ`, `fourier n` is the monomial `λ z, z ^ n`, bundled as a continuous map from `circle`
  to `ℂ`
* for `n : ℤ` and `p : ℝ≥0∞`, `fourier_Lp p n` is an abbreviation for the monomial `fourier n`
  considered as an element of the Lᵖ-space `Lp ℂ p circle_measure`, via the embedding
  `continuous_map.to_Lp`
* `fourier_series` is the canonical isometric isomorphism from `Lp ℂ 2 circle_measure` to `ℓ²(ℤ, ℂ)`
  induced by taking Fourier series

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(circle, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows from
the Stone-Weierstrass theorem after checking that it is a subalgebra, closed under conjugation, and
separates points.

The theorem `span_fourier_Lp_closure_eq_top` states that for `1 ≤ p < ∞` the span of the monomials
`fourier_Lp` is dense in `Lp ℂ p circle_measure`, i.e. that its `submodule.topological_closure` is
`⊤`.  This follows from the previous theorem using general theory on approximation of Lᵖ functions
by continuous functions.

The theorem `orthonormal_fourier` states that the monomials `fourier_Lp 2 n` form an orthonormal
set (in the L² space of the circle).

The last two results together provide that the functions `fourier_Lp 2 n` form a Hilbert basis for
L²; this is named as `fourier_series`.

Parseval's identity, `tsum_sq_fourier_series_repr`, is a direct consequence of the construction of
this Hilbert basis.
-/

noncomputable theory
open_locale real ennreal complex_conjugate classical
open real complex topological_space continuous_map measure_theory measure_theory.measure
  algebra submodule set interval_integral

/-! ### Choice of measure on the circle -/

section circle_measure
/-! We make the circle into a measure space, using the measure transported from `(-π, π]`,
 normalized to have total measure 1. -/

instance : measurable_space circle := borel circle
instance : borel_space circle := ⟨rfl⟩

lemma measurable_arg' : measurable arg' :=
begin
  let t1 := { z : ℂ | 0 < arg z}, let t2 := t1ᶜ,
  apply measurable_of_measurable_union_cover t1 t2 _ _ (by simp),
  { have : (λ (a : t1), arg' a) = (λ (a : t1), arg a),
    { ext, rw arg', split_ifs, refl, exfalso, exact h x.property }, rw this,
    exact measurable_arg.comp measurable_subtype_coe },
  { have : (λ (a : t2), arg' a) = (λ (a : t2), arg a + (2 * π)),
    { ext, rw arg', split_ifs, exfalso, exact x.property h, refl, }, rw this,
    exact (measurable_arg.add_const _).comp measurable_subtype_coe },
  { exact measurable_set_lt measurable_const measurable_arg },
  { exact (measurable_set_lt measurable_const measurable_arg).compl },
end

def circle_m_equiv : measurable_equiv (Ioc 0 (2* π)) circle :=
{ measurable_inv_fun := by
  { rw circle.circle_equiv, rw circle.arg'_equiv,
    simp only [equiv.inv_fun_as_coe, equiv.symm_symm, equiv.coe_fn_mk, equiv.coe_fn_symm_mk],
    rw ←(measurable_embedding.subtype_coe
          (@measurable_set_Ioc ℝ _ _ _ _ _ _ _)).measurable_comp_iff,
    exact measurable_arg'.comp continuous_subtype_coe.measurable },
  measurable_to_fun := (exp_map_circle.continuous.borel_measurable).comp measurable_subtype_coe,
  .. circle.circle_equiv }

/-- Measure on the circle, normalized to have total measure 1. -/
def circle_measure : measure circle :=
  (ennreal.of_real (1 / (2 * π)) • volume).map circle_m_equiv

lemma circle_measure_univ : circle_measure univ = 1 :=
begin
  dsimp only [circle_measure],
  rw [circle_m_equiv.map_apply, preimage_univ, measure.smul_apply, id.smul_eq_mul,
    ←volume_image_subtype_coe (@measurable_set_Ioc ℝ _ _ _ _ _ _ _), image_univ,
    subtype.range_coe, real.volume_Ioc, ←ennreal.of_real_mul (one_div_nonneg.mpr two_pi_pos.le)],
  ring_nf, field_simp [real.pi_ne_zero],
end

instance : is_probability_measure circle_measure := ⟨circle_measure_univ⟩

instance : measure_space circle := { volume := circle_measure,  .. circle.measurable_space }

lemma integrable_circle_iff (f : circle → ℂ) :
  integrable f circle_measure ↔ integrable_on (f ∘ exp_map_circle) (Ioc 0 (2 * π)) :=
begin
  rw [circle_measure, measure_theory.measure.map_smul,
    integrable_smul_measure _ ennreal.of_real_ne_top],
  swap, { rw [ne.def, ennreal.of_real_eq_zero, not_le, one_div_pos], exact two_pi_pos },
  rw circle_m_equiv.measurable_embedding.integrable_map_iff,
  have : f ∘ circle_m_equiv = f ∘ exp_map_circle ∘ coe := by { ext1, refl, }, rw this,
  convert (@measurable_embedding.integrable_map_iff _ _ _ _ _ _ _ _
    (measurable_embedding.subtype_coe _) (f ∘ exp_map_circle)).symm,
  rw integrable_on, congr' 1, symmetry,
  apply map_comap_subtype_coe, all_goals { exact measurable_set_Ioc },
end

lemma integral_circle_eq (f : circle → ℂ) :
  integral circle_measure f = 1 / (2 * π) * ∫ θ in 0..(2 * π), f (exp_map_circle θ) :=
begin
  dsimp only [circle_measure],
  rw [integral_map_equiv, measure_theory.integral_smul_measure,
    ennreal.to_real_of_real (one_div_nonneg.mpr two_pi_pos.le),
    real_smul, of_real_div, of_real_one, of_real_mul, of_real_bit0],
  congr' 1, symmetry,
  rw integral_of_le (by linarith [pi_pos] : 0 ≤ 2 * π),
  exact set_integral_eq_subtype measurable_set_Ioc _,
end

lemma integrable_circle_iff_circle_integrable (f : ℂ → ℂ) :
  integrable (f ∘ coe) circle_measure ↔ (circle_integrable f 0 1) :=
begin
  rw [circle_integrable, integrable_circle_iff],
  rw interval_integrable_iff_integrable_Ioc_of_le (by linarith [pi_pos] : 0 ≤ (2 * π)),
  suffices : eq_on ((f ∘ coe) ∘ ⇑exp_map_circle) (λ (θ : ℝ), f (circle_map 0 1 θ)) (Ioc 0 (2 * π)),
  { exact ⟨λ h, integrable_on.congr_fun h this measurable_set_Ioc,
      λ h, integrable_on.congr_fun h this.symm measurable_set_Ioc⟩,  },
  intros x hx, simp [circle_map]
end

lemma integral_circle_eq_circle_integral (f : ℂ → ℂ) (hf : circle_integrable f 0 1):
  circle_integral f 0 1 = (2 * π * I) * integral circle_measure (λ z, z * f z) :=
begin
  simp_rw [integral_circle_eq, circle_integral, deriv_circle_map, ←mul_assoc,
    (by ring : 2 * ↑π * I * (1 / (2 * ↑π)) = I * ((2 * π) / (2 * π)))],
  rw [div_self, mul_one, ←integral_const_mul], swap, { simp [pi_pos.ne'] },
  apply integral_congr, intros x hx,
  simp only [circle_map, of_real_one, one_mul, zero_add, id.smul_eq_mul, exp_map_circle_apply],
  ring,
end

end circle_measure

/-! ### Monomials on the circle -/

section monomials

/-- The family of monomials `λ z, z ^ n`, parametrized by `n : ℤ` and considered as bundled
continuous maps from `circle` to `ℂ`. -/
@[simps] def fourier (n : ℤ) : C(circle, ℂ) :=
{ to_fun := λ z, z ^ n,
  continuous_to_fun := continuous_subtype_coe.zpow₀ n $ λ z, or.inl (ne_zero_of_mem_circle z) }

@[simp] lemma fourier_zero {z : circle} : fourier 0 z = 1 := rfl

@[simp] lemma fourier_neg {n : ℤ} {z : circle} : fourier (-n) z = conj (fourier n z) :=
by simp [← coe_inv_circle_eq_conj z]

@[simp] lemma fourier_add {m n : ℤ} {z : circle} :
  fourier (m + n) z = (fourier m z) * (fourier n z) :=
by simp [zpow_add₀ (ne_zero_of_mem_circle z)]

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ`; equivalently, polynomials in
`z` and `conj z`. -/
def fourier_subalgebra : subalgebra ℂ C(circle, ℂ) := algebra.adjoin ℂ (range fourier)

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` is in fact the linear span of
these functions. -/
lemma fourier_subalgebra_coe : fourier_subalgebra.to_submodule = span ℂ (range fourier) :=
begin
  apply adjoin_eq_span_of_subset,
  refine subset.trans _ submodule.subset_span,
  intros x hx,
  apply submonoid.closure_induction hx (λ _, id) ⟨0, rfl⟩,
  rintros _ _ ⟨m, rfl⟩ ⟨n, rfl⟩,
  refine ⟨m + n, _⟩,
  ext1 z,
  exact fourier_add,
end

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` separates points. -/
lemma fourier_subalgebra_separates_points : fourier_subalgebra.separates_points :=
begin
  intros x y hxy,
  refine ⟨_, ⟨fourier 1, _, rfl⟩, _⟩,
  { exact subset_adjoin ⟨1, rfl⟩ },
  { simp [hxy] }
end

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` is invariant under complex
conjugation. -/
lemma fourier_subalgebra_conj_invariant :
  conj_invariant_subalgebra (fourier_subalgebra.restrict_scalars ℝ) :=
begin
  rintros _ ⟨f, hf, rfl⟩,
  change _ ∈ fourier_subalgebra,
  change _ ∈ fourier_subalgebra at hf,
  apply adjoin_induction hf,
  { rintros _ ⟨n, rfl⟩,
    suffices : fourier (-n) ∈ fourier_subalgebra,
    { convert this,
      ext1,
      simp },
    exact subset_adjoin ⟨-n, rfl⟩ },
  { intros c,
    exact fourier_subalgebra.algebra_map_mem (conj c) },
  { intros f g hf hg,
    convert fourier_subalgebra.add_mem hf hg,
    exact alg_hom.map_add _ f g, },
  { intros f g hf hg,
    convert fourier_subalgebra.mul_mem hf hg,
    exact alg_hom.map_mul _ f g, }
end

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` is dense. -/
lemma fourier_subalgebra_closure_eq_top : fourier_subalgebra.topological_closure = ⊤ :=
continuous_map.subalgebra_complex_topological_closure_eq_top_of_separates_points
  fourier_subalgebra
  fourier_subalgebra_separates_points
  fourier_subalgebra_conj_invariant

/-- The linear span of the monomials `z ^ n` is dense in `C(circle, ℂ)`. -/
lemma span_fourier_closure_eq_top : (span ℂ (range fourier)).topological_closure = ⊤ :=
begin
  rw ← fourier_subalgebra_coe,
  exact congr_arg subalgebra.to_submodule fourier_subalgebra_closure_eq_top,
end

/-- The family of monomials `λ z, z ^ n`, parametrized by `n : ℤ` and considered as elements of
the `Lp` space of functions on `circle` taking values in `ℂ`. -/
abbreviation fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) : Lp ℂ p circle_measure :=
to_Lp p circle_measure ℂ (fourier n)

lemma coe_fn_fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) :
  ⇑(fourier_Lp p n) =ᵐ[circle_measure] fourier n :=
coe_fn_to_Lp circle_measure (fourier n)

/-- For each `1 ≤ p < ∞`, the linear span of the monomials `z ^ n` is dense in
`Lp ℂ p circle_measure`. -/
lemma span_fourier_Lp_closure_eq_top {p : ℝ≥0∞} [fact (1 ≤ p)] (hp : p ≠ ∞) :
  (span ℂ (range (fourier_Lp p))).topological_closure = ⊤ :=
begin
  convert (continuous_map.to_Lp_dense_range ℂ hp circle_measure ℂ).topological_closure_map_submodule
    span_fourier_closure_eq_top,
  rw [map_span, range_comp],
  simp
end

/-- The monomials `z ^ n` are an orthonormal set with respect to Haar measure on the circle. -/
lemma orthonormal_fourier : orthonormal ℂ (fourier_Lp 2) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw continuous_map.inner_to_Lp circle_measure (fourier i) (fourier j),
  split_ifs,
  { simp [h, is_probability_measure.measure_univ, ←fourier_neg, ←fourier_add, -fourier_to_fun] },
  simp only [← fourier_add, ← fourier_neg],
  have hij : -i + j ≠ 0 := by { rw add_comm, exact sub_ne_zero.mpr (ne.symm h) },
  rw [fourier, integral_circle_eq, continuous_map.coe_mk],
  convert mul_zero _,
  simp_rw [exp_map_circle_apply, ←exp_int_mul, ←mul_assoc],
  convert integral_exp_mul_complex (_ : I * (-i + j) ≠ 0),
  { ext1 θ, congr' 1, simp only [int.cast_add, int.cast_neg], ring },
  { symmetry, rw div_eq_zero_iff, left, rw sub_eq_zero,
    rw exp_eq_exp_iff_exists_int, use (j - i), rw int.cast_sub, rw complex.of_real_mul,
    rw complex.of_real_bit0, rw complex.of_real_one, simp, ring_nf, },
  { apply mul_ne_zero, exact I_ne_zero, rwa [←int.cast_neg, ←int.cast_add, int.cast_ne_zero],}
end

end monomials

section fourier

/-- We define `fourier_series` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 circle_measure`, which
by definition is an isometric isomorphism from `Lp ℂ 2 circle_measure` to `ℓ²(ℤ, ℂ)`. -/
def fourier_series : hilbert_basis ℤ ℂ (Lp ℂ 2 circle_measure) :=
hilbert_basis.mk orthonormal_fourier (span_fourier_Lp_closure_eq_top (by norm_num))

/-- The elements of the Hilbert basis `fourier_series` for `Lp ℂ 2 circle_measure` are the functions
`fourier_Lp 2`, the monomials `λ z, z ^ n` on the circle considered as elements of `L2`. -/
@[simp] lemma coe_fourier_series : ⇑fourier_series = fourier_Lp 2 := hilbert_basis.coe_mk _ _

/-- Under the isometric isomorphism `fourier_series` from `Lp ℂ 2 circle_measure` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is the integral over the circle of `λ t, t ^ (-i) * f t`. -/
lemma fourier_series_repr (f : Lp ℂ 2 circle_measure) (i : ℤ) :
  fourier_series.repr f i = ∫ t : circle, t ^ (-i) * f t ∂ circle_measure :=
begin
  transitivity ∫ t : circle, conj ((fourier_Lp 2 i : circle → ℂ) t) * f t ∂ circle_measure,
  { simp [fourier_series.repr_apply_apply f i, measure_theory.L2.inner_def] },
  apply measure_theory.integral_congr_ae,
  filter_upwards [coe_fn_fourier_Lp 2 i] with _ ht,
  rw [ht, ← fourier_neg],
  simp [-fourier_neg]
end

/-- The Fourier series of an `L2` function `f` sums to `f`, in the `L2` topology on the circle. -/
lemma has_sum_fourier_series (f : Lp ℂ 2 circle_measure) :
  has_sum (λ i, fourier_series.repr f i • fourier_Lp 2 i) f :=
by simpa using hilbert_basis.has_sum_repr fourier_series f

/-- **Parseval's identity**: the sum of the squared norms of the Fourier coefficients equals the
`L2` norm of the function. -/
lemma tsum_sq_fourier_series_repr (f : Lp ℂ 2 circle_measure) :
  ∑' i : ℤ, ∥fourier_series.repr f i∥ ^ 2 = ∫ t : circle, ∥f t∥ ^ 2 ∂ circle_measure :=
begin
  have H₁ : ∥fourier_series.repr f∥ ^ 2 = ∑' i, ∥fourier_series.repr f i∥ ^ 2,
  { exact_mod_cast lp.norm_rpow_eq_tsum _ (fourier_series.repr f),
    norm_num },
  have H₂ : ∥fourier_series.repr f∥ ^ 2 = ∥f∥ ^2 := by simp,
  have H₃ := congr_arg is_R_or_C.re (@L2.inner_def circle ℂ ℂ _ _ _ _ f f),
  rw ← integral_re at H₃,
  { simp only [← norm_sq_eq_inner] at H₃,
    rw [← H₁, H₂],
    exact H₃ },
  { exact L2.integrable_inner f f },
end

end fourier
