import measure_theory.measure.haar
import algebra.order.floor

noncomputable theory

open set filter function metric measure_theory
open_locale nnreal topological_space

-- TODO Relocate this + build basic API
/-- A measure-preserving map is said to be ergodic with a respect to a measure, if the only
invariant sets either have measure zero or their complement has measure zero. -/
@[protect_proj]
structure ergodic {α : Type*} [measurable_space α] (f : α → α) (μ : measure α . volume_tac) extends
  measure_preserving f μ μ : Prop :=
(zero_one_law : ∀ s, measurable_set s → f ⁻¹' s ⊆ s → μ s = 0 ∨ μ sᶜ = 0)

-- TODO Generalise to allow any period (not just 1) and then make `real.angle` and `add_circle` both
-- distinguished special cases.
/-- The "additive circle": `ℝ ⧸ ℤ`.

See also `circle` and `real.angle`. -/
@[derive [add_comm_group, topological_space, topological_add_group]]
def add_circle := ℝ ⧸ add_subgroup.zmultiples (1 : ℝ)

/-- The quotient map `ℝ → ℝ ⧸ ℤ`. -/
def real.to_add_circle (x : ℝ) : add_circle := quotient_add_group.mk x

namespace add_circle

instance : inhabited add_circle := ⟨(0 : ℝ).to_add_circle⟩

/-- The natural equivalence between `ℝ ⧸ ℤ` and the half-open unit interval in `ℝ`. -/
def equiv_Ico : add_circle ≃ Ico (0 : ℝ) 1 :=
{ inv_fun := quotient_add_group.mk' _ ∘ coe,
  to_fun :=
  begin
    letI := quotient_add_group.left_rel (add_subgroup.zmultiples (1 : ℝ)),
    have : ∀ (x y : ℝ) (h: x ≈ y),
    (⟨int.fract x, int.fract_nonneg x, int.fract_lt_one x⟩ : Ico (0 : ℝ) 1) =
    (⟨int.fract y, int.fract_nonneg y, int.fract_lt_one y⟩ : Ico (0 : ℝ) 1),
    { intros,
      obtain ⟨k, hk⟩ := add_subgroup.mem_zmultiples_iff.mp (quotient_add_group.left_rel_apply.mp h),
      rw (by { rw [← k.smul_one_eq_coe, hk], abel, } : y = k + x),
      ext,
      simp only [int.fract_int_add, subtype.coe_mk], },
    exact quotient.lift _ this,
  end,
  right_inv :=
  begin
    rintros ⟨x, hx, hx'⟩,
    ext,
    simpa only [quotient_add_group.coe_mk', comp_app, subtype.coe_mk] using
      int.fract_eq_self.mpr ⟨hx, hx'⟩,
  end,
  left_inv :=
  begin
    rintros ⟨x⟩,
    change quotient_add_group.mk (int.fract x) = quotient_add_group.mk x,
    rw [quotient_add_group.eq', add_comm, ← sub_eq_add_neg, int.self_sub_fract,
      add_subgroup.mem_zmultiples_iff],
    exact ⟨⌊x⌋, by simp⟩,
  end }

instance : has_coe add_circle (Ico (0 : ℝ) 1) := ⟨equiv_Ico⟩

@[simp] lemma coe_to_add_circle_mk (x : ℝ) :
  ((x.to_add_circle : Ico (0 : ℝ) 1) : ℝ) = int.fract x :=
rfl

lemma continuous_equiv_Ico_symm : continuous equiv_Ico.symm :=
continuous_coinduced_rng.comp continuous_induced_dom

instance : metric_space add_circle :=
metric_space.of_metrizable
  (λ x y, min (|(x : ℝ) - (y : ℝ)|) (1 - |(x : ℝ) - (y : ℝ)|))
  (λ x, by simp only [sub_self, abs_zero, tsub_zero, min_eq_left, zero_le_one])
  (λ x y, by rw abs_sub_comm)
  (begin
    rintros ⟨x⟩ ⟨y⟩ ⟨z⟩,
    let d₁ := |int.fract x - int.fract z|,
    let d₂ := |int.fract x - int.fract y|,
    let d₃ := |int.fract y - int.fract z|,
    change min d₁ (1 - d₁) ≤ min d₂ (1 - d₂) + min d₃ (1 - d₃),
    have ht₁ : d₁ ≤ d₂ + d₃ := abs_sub_le (int.fract x) (int.fract y) (int.fract z),
    have ht₂ : d₂ ≤ d₃ + d₁,
    { convert abs_sub_le (int.fract y) (int.fract z) (int.fract x); rw abs_sub_comm, },
    have ht₃ : d₃ ≤ d₁ + d₂,
    { convert abs_sub_le (int.fract z) (int.fract x) (int.fract y); rw abs_sub_comm, },
    have ht₄ : d₁ + d₂ + d₃ ≤ 2,
    { change | _ | + | _ | + | _ | ≤ (2 : ℝ),
      rcases abs_cases (int.fract x - int.fract z) with ⟨h₁₁, h₁₂⟩ | ⟨h₁₁, h₁₂⟩;
      rcases abs_cases (int.fract x - int.fract y) with ⟨h₂₁, h₂₂⟩ | ⟨h₂₁, h₂₂⟩;
      rcases abs_cases (int.fract y - int.fract z) with ⟨h₃₁, h₃₂⟩ | ⟨h₃₁, h₃₂⟩;
      rw [h₁₁, h₂₁, h₃₁];
      linarith [int.fract_nonneg x, int.fract_lt_one x,
                int.fract_nonneg y, int.fract_lt_one y,
                int.fract_nonneg z, int.fract_lt_one z], },
    rcases min_cases d₁ (1 - d₁) with ⟨h₁₁, h₁₂⟩ | ⟨h₁₁, h₁₂⟩;
    rcases min_cases d₂ (1 - d₂) with ⟨h₂₁, h₂₂⟩ | ⟨h₂₁, h₂₂⟩;
    rcases min_cases d₃ (1 - d₃) with ⟨h₃₁, h₃₂⟩ | ⟨h₃₁, h₃₂⟩;
    rw [h₁₁, h₂₁, h₃₁]; linarith,
  end)
  (λ U,
  begin
    refine ⟨λ hU, _, λ hU, _⟩,
    { rintros ⟨x⟩ (hx : x.to_add_circle ∈ U),
      sorry, },
    { sorry, },
  end)
  (begin
    -- TODO Golf this, adding missing helper lemmas if necessary.
    rintros ⟨x⟩ ⟨y⟩ (h : min (|int.fract x - int.fract y|) (1 - |int.fract x - int.fract y|) = 0),
    change quotient_add_group.mk x = quotient_add_group.mk y,
    rw [quotient_add_group.eq', add_comm, ← sub_eq_add_neg, add_subgroup.mem_zmultiples_iff,
      ← int.fract_add_floor x, ← int.fract_add_floor y, add_sub_add_comm],
    by_cases hxy : |int.fract x - int.fract y| ≤ 1 - |int.fract x - int.fract y|,
    { refine ⟨⌊y⌋ - ⌊x⌋, _⟩,
      simp only [min_def, hxy, if_true, abs_eq_zero, sub_eq_zero] at h,
      simp only [h, int.smul_one_eq_coe, int.cast_sub, sub_self, zero_add], },
    { simp only [min_def, hxy, if_false, sub_eq_zero] at h,
      rw abs_sub_comm at h,
      cases (abs_eq zero_le_one).mp h.symm with h' h';
      rw h',
      { exact ⟨1 + (⌊y⌋ - ⌊x⌋), by simp⟩, },
      { exact ⟨-1 + (⌊y⌋ - ⌊x⌋), by simp⟩, }, },
  end)

lemma dist_eq {x y : add_circle} :
  dist x y = min (|(x : ℝ) - (y : ℝ)|) (1 - |(x : ℝ) - (y : ℝ)|) :=
rfl

instance : compact_space add_circle := sorry

instance : measurable_space add_circle := borel add_circle

instance : borel_space add_circle := ⟨rfl⟩

instance : measure_space add_circle := ⟨measure.add_haar_measure ⊤⟩

instance : is_finite_measure (volume : measure add_circle) := compact_space.is_finite_measure

@[simp] lemma volume_closed_ball (x : add_circle) (r : ℝ) :
  volume (closed_ball x r) = min 1 (2 * r.to_nnreal) :=
sorry

lemma eventually_volume_closed_ball :
  ∀ᶠ (r : ℝ≥0) in 𝓝 0, ∀ (x : add_circle), volume (closed_ball x r) = 2 * r :=
begin
  rw nnreal.nhds_zero_basis.eventually_iff,
  refine ⟨1/2, by simp, λ r hr x, _⟩,
  simp only [mem_Iio, one_div, nnreal.lt_inv_iff_mul_lt, ne.def, bit0_eq_zero, one_ne_zero,
    not_false_iff, mul_comm r] at hr,
  simp only [real.to_nnreal_coe, min_eq_right_iff, volume_closed_ball],
  norm_cast,
  exact hr.le,
end

/-- Given `t c : ℝ`, this is the map `x ↦ t*x + c` on the circle. -/
protected def affine_map (t c : ℝ) (x : add_circle) : add_circle := (t * x + c).to_add_circle

lemma ergodic_affine_map {q : ℕ} {c : ℝ} (hq : 2 ≤ q) :
  ergodic $ add_circle.affine_map q c :=
sorry

end add_circle
