import measure_theory.covering.vitali
import measure_theory.covering.differentiation

-- TODO Tidy up this mess

noncomputable theory

open set filter function metric measure_theory measure_theory.measure_space
open_locale nnreal ennreal topological_space

variables {α : Type*} [metric_space α] [measurable_space α] {μ : measure α} {f : ℝ≥0 → ℝ≥0} {d : ℝ}
variables (hfd : ∀ (t : ℝ≥0), ∀ᶠ (ε : ℝ≥0) in 𝓝 0, f (t * ε) = t^d * f ε)
variables (hfμ : ∀ᶠ (ε : ℝ≥0) in 𝓝 0, ∀ x, μ (closed_ball x ε) = f ε)

/- TODO Consider weakening `hfd` to allow for curved spaces. [In a Riemannian
manifold the ratio of volume to the Euclidean case has an even expansion about radius = 0 with
leading term 1 but with the negative of scalar curvature appearing as the coefficient of the
degree-two term. For example on the (homogeneous) space that is the unit two sphere, the area of a
disc of radius `r` is `2π * (1 - cos r)` (for `r` small).] -/
include hfd hfμ

/-- Technical / convenience lemma for use with `vitali.vitali_family`. -/
lemma vitali.exists_mem_Ioc_measure_closed_ball_le (x : α) {ε : ℝ} (hε : 0 < ε) :
  ∃ r ∈ Ioc (0 : ℝ) ε, μ (closed_ball x (6 * r)) ≤ (6^d : ℝ≥0) * μ (closed_ball x r) :=
begin
  suffices : ∀ᶠ r in 𝓝[>] 0, μ (closed_ball x (6 * r)) = (6^d : ℝ≥0) * μ (closed_ball x r),
  { obtain ⟨v, hv₀, hv₁⟩ := this.exists_mem,
    obtain ⟨δ, hδ₀ : 0 < δ, hδ₁⟩ := mem_nhds_within_Ioi_iff_exists_Ioo_subset.mp hv₀,
    refine ⟨min (δ/2) ε, by simp [hε, half_pos hδ₀], _⟩,
    have hδv : min (δ / 2) ε ∈ v, { apply hδ₁, simp [half_pos hδ₀, hε, half_lt_self hδ₀], },
    rw hv₁ _ hδv,
    exact le_refl _, },
  clear hε ε,
  rw [eventually_nhds_within_iff, eventually_iff_exists_mem],
  obtain ⟨R, hR₀, hR₁⟩ := nnreal.nhds_zero_basis.eventually_iff.mp (hfμ.and (hfd 6)),
  simp only [mem_Iio] at hR₁,
  refine ⟨Iio $ R/6, Iio_mem_nhds _, λ y hy₀ hy₁, _⟩,
  { norm_cast,
    apply nnreal.div_pos hR₀,
    rw ← nnreal.coe_lt_coe,
    norm_cast,
    linarith, },
  { rw [mem_Iio, lt_div_iff' (by linarith : 0 < (6 : ℝ))] at hy₀,
    replace hy₁ := (mem_Ioi.mp hy₁).le,
    have h₁ : (⟨y, hy₁⟩ : ℝ≥0) < R,
    { rw ← nnreal.coe_lt_coe,
      have aux : y ≤ 6 * y, { linarith, },
      exact lt_of_le_of_lt aux hy₀, },
    have h₂ : (⟨6*y, by linarith⟩ : ℝ≥0) < R := hy₀,
    obtain h₃ := (hR₁ h₂).1 x,
    obtain ⟨h₄, h₅⟩ := hR₁ h₁,
    specialize h₄ x,
    simp only [subtype.coe_mk] at h₃ h₄ h₅,
    rw [h₃, h₄],
    norm_cast,
    exact h₅, },
end

variables (μ f d)

/-- A version of the Lebesgue Density Theorem. -/
lemma closed_ball.ae_tendsto_measure_inter_div
  [proper_space α] [borel_space α] [is_locally_finite_measure μ] (S : set α) :
  ∀ᵐ x ∂μ.restrict S, ∀ (w : ℕ → α) (δ : ℕ → ℝ)
    (hδ₀ : ∀ j, 0 < δ j) (hδ₁ : tendsto δ at_top (𝓝 0)) (hδ₂ : ∀ j, x ∈ closed_ball (w j) (δ j)),
    tendsto (λ j, μ (S ∩ closed_ball (w j) (δ j)) / μ (closed_ball (w j) (δ j))) at_top (𝓝 1) :=
begin
  refine ((vitali.vitali_family μ _
    (vitali.exists_mem_Ioc_measure_closed_ball_le hfd hfμ)).ae_tendsto_measure_inter_div S).mono
    (λ x hx w δ hδ₀ hδ₁ hδ₂, _),
  let g₁ : ℕ → set α := λ j, closed_ball (w j) (δ j),
  let g₂ : set α → ℝ≥0∞ := λ a, μ (S ∩ a) / μ a,
  change tendsto g₂ (map g₁ at_top) (𝓝 1),
  refine hx.mono_left (λ X hX', _),
  obtain ⟨ε, hε, hX⟩ := (vitali_family.mem_filter_at_iff _).mp hX', clear hX',
  simp only [mem_map, mem_at_top_sets, ge_iff_le, mem_preimage, g₁],
  simp only [vitali.vitali_family, mem_set_of_eq, and_imp] at hX,
  obtain ⟨R, hR₀, hR₁⟩ := nnreal.nhds_zero_basis.eventually_iff.mp (hfμ.and (hfd 6)),
  simp only [mem_Iio] at hR₁,
  rw ← nnreal.coe_pos at hR₀,
  have hRε : 0 < min (ε/2) (R/6), { simp only [lt_min_iff], split; linarith, },
  obtain ⟨n, hn₀⟩ := metric.tendsto_at_top.mp hδ₁ _ hRε,
  simp only [ge_iff_le, dist_zero_right, real.norm_eq_abs, lt_min_iff,
    abs_eq_self.mpr (hδ₀ _).le] at hn₀,
  have hn₁ : ∀ j, n ≤ j → δ j < ε / 2 := λ j hj, (hn₀ j hj).1,
  have hn₂ : ∀ j, n ≤ j → 6 * δ j < R := λ j hj, by linarith [(hn₀ j hj).2],
  refine ⟨n, λ j hj, hX _ (hδ₂ j) is_closed_ball _ _ (λ y hy, _)⟩,
  { exact (nonempty_ball.mpr (hδ₀ j)).mono ball_subset_interior_closed_ball, },
  { have hdiam : 3 * diam (closed_ball (w j) (δ j)) ≤ 6 * δ j,
    { linarith [@diam_closed_ball _ _ (w j) _ (hδ₀ j).le], },
    refine (measure_mono (closed_ball_subset_closed_ball hdiam)).trans _,
    have h₁ : (⟨6 * δ j, by { linarith [hδ₀ j], }⟩ : ℝ≥0) < R,
    { rw ← nnreal.coe_lt_coe, exact hn₂ j hj, },
    have h₂ : (⟨δ j, (hδ₀ j).le⟩ : ℝ≥0) < R,
    { rw [← nnreal.coe_lt_coe, ← mul_lt_mul_left (by linarith : 0 < (6 : ℝ))],
      simp only [subtype.coe_mk],
      refine (hn₂ j hj).trans _,
      linarith, },
    obtain ⟨h₃, h₄⟩ := hR₁ h₂,
    specialize h₃ (w j),
    obtain h₅ := (hR₁ h₁).1 x,
    simp only [subtype.coe_mk] at h₃ h₄ h₅,
    rw [h₃, h₅],
    norm_cast,
    rw ← h₄,
    convert le_refl _, },
  { simp only [mem_closed_ball] at hδ₂ hy ⊢,
    specialize hδ₂ j,
    specialize hn₁ j hj,
    simp only [mem_closed_ball] at hδ₂ hy ⊢,
    calc dist y x ≤ dist y (w j) + dist (w j) x : dist_triangle _ _ _
              ... ≤ ε : by { rw dist_comm (w j), linarith, } },
end
