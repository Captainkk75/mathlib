/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.upcrossing
import measure_theory.function.uniform_integrable
import measure_theory.constructions.polish

/-!

# Martingale convergence theorems

The martingale convergence theorems are a collection of theorems characterizing the convergence
of a martingale provided it satisfies some boundedness conditions. This file contains the
almost everywhere martingale convergence theorem which provides an almost everywhere limit to
an L¹ bounded submartingale.

## Main results

* `measure_theory.submartingale.ae_tendsto_limit_process`: the almost everywhere martingale
  convergence theorem: an L¹-bounded submartingale adapted to the filtration `ℱ` converges almost
  everywhere to its limit process.
* `measure_theory.submartingale.mem_ℒ1_limit_process`: the limit process of an L¹-bounded
  submartingale is integrable.

-/

open topological_space filter measure_theory.filtration
open_locale nnreal ennreal measure_theory probability_theory big_operators topological_space

namespace measure_theory

variables {Ω ι : Type*} {m0 : measurable_space Ω} {μ : measure Ω} {ℱ : filtration ℕ m0}
variables {a b : ℝ} {f : ℕ → Ω → ℝ} {ω : Ω} {R : ℝ≥0}

section ae_convergence

/-!

### Almost everywhere martingale convergence theorem

We will now prove the almost everywhere martingale convergence theorem.

The a.e. martingale convergence theorem states: if `f` is an L¹-bounded `ℱ`-submartingale, then
it converges almost everywhere to an integrable function which is measurable with respect to
the σ-algebra `ℱ∞ := ⨆ n, ℱ n`.

Mathematically, we proceed by first noting that a real sequence $(x_n)$ converges if
(a) $\limsup_{n \to \infty} |x_n| < \infty$, (b) for all $a < b \in \mathbb{Q}$ we have the
number of upcrossings of $(x_n)$ from below $a$ to above $b$ is finite.
Thus, for all $\omega$ satisfying $\limsup_{n \to \infty} |f_n(\omega)| < \infty$ and the number of
upcrossings of $(f_n(\omega))$ from below $a$ to above $b$ is finite for all $a < b \in \mathbb{Q}$,
we have $(f_n(\omega))$ is convergent.

Hence, assuming $(f_n)$ is L¹-bounded, using Fatou's lemma, we have
$$
  \mathbb{E] \limsup_{n \to \infty} |f_n| \le \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
implying $\limsup_{n \to \infty} |f_n| < \infty$ a.e. Furthermore, by the upcrossing estimate,
the number of upcrossings is finite almost everywhere implying $f$ converges pointwise almost
everywhere.

Thus, denoting $g$ the a.e. limit of $(f_n)$, $g$ is $\mathcal{F}_\infty$-measurable as for all
$n$, $f_n$ is $\mathcal{F}_n$-measurable and $\mathcal{F}_n \le \mathcal{F}_\infty$. Finally, $g$
is integrable as $|g| \le \liminf_{n \to \infty} |f_n|$ so
$$
  \mathbb{E}|g| \le \mathbb{E} \limsup_{n \to \infty} |f_n| \le
    \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
as required.

Implementation wise, we have `tendsto_of_no_upcrossings` which showed that
a bounded sequence converges if it does not visit below $a$ and above $b$ infinitely often
for all $a, b ∈ s$ for some dense set $s$. So, we may skip the first step provided we can prove
that the realizations are bounded almost everywhere. Indeed, suppose $(|f_n(\omega)|)$ is not
bounded, then either $f_n(\omega) \to \pm \infty$ or one of $\limsup f_n(\omega)$ or
$\liminf f_n(\omega)$ equals $\pm \infty$ while the other is finite. But the first case
contradicts $\liminf |f_n(\omega)| < \infty$ while the second case contradicts finite upcrossings.

-/

/-- If a stochastic process has bounded upcrossing from below `a` to above `b`,
then it does not frequently visit both below `a` and above `b`. -/
lemma not_frequently_of_upcrossings_lt_top (hab : a < b) (hω : upcrossings a b f ω ≠ ∞) :
  ¬((∃ᶠ n in at_top, f n ω < a) ∧ (∃ᶠ n in at_top, b < f n ω)) :=
begin
  rw [← lt_top_iff_ne_top, upcrossings_lt_top_iff] at hω,
  replace hω : ∃ k, ∀ N, upcrossings_before a b f N ω < k,
  { obtain ⟨k, hk⟩ := hω,
    exact ⟨k + 1, λ N, lt_of_le_of_lt (hk N) k.lt_succ_self⟩ },
  rintro ⟨h₁, h₂⟩,
  rw frequently_at_top at h₁ h₂,
  refine not_not.2 hω _,
  push_neg,
  intro k,
  induction k with k ih,
  { simp only [zero_le', exists_const] },
  { obtain ⟨N, hN⟩ := ih,
    obtain ⟨N₁, hN₁, hN₁'⟩ := h₁ N,
    obtain ⟨N₂, hN₂, hN₂'⟩ := h₂ N₁,
    exact ⟨(N₂ + 1), nat.succ_le_of_lt $ lt_of_le_of_lt hN
      (upcrossings_before_lt_of_exists_upcrossing hab hN₁ hN₁' hN₂ hN₂')⟩ }
end

/-- A stochastic process that frequently visits below `a` and above `b` have infinite
upcrossings. -/
lemma upcrossings_eq_top_of_frequently_lt (hab : a < b)
  (h₁ : ∃ᶠ n in at_top, f n ω < a) (h₂ : ∃ᶠ n in at_top, b < f n ω) :
  upcrossings a b f ω = ∞ :=
classical.by_contradiction (λ h, not_frequently_of_upcrossings_lt_top hab h ⟨h₁, h₂⟩)

/-- A realization of a stochastic process with bounded upcrossings and bounded liminfs is
convergent.

We use the spelling `< ∞` instead of the standard `≠ ∞` in the assumptions since it is not as easy
to change `<` to `≠` under binders. -/
lemma tendsto_of_uncrossing_lt_top
  (hf₁ : liminf at_top (λ n, (∥f n ω∥₊ : ℝ≥0∞)) < ∞)
  (hf₂ : ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞) :
  ∃ c, tendsto (λ n, f n ω) at_top (𝓝 c) :=
begin
  by_cases h : is_bounded_under (≤) at_top (λ n, |f n ω|),
  { rw is_bounded_under_le_abs at h,
    refine tendsto_of_no_upcrossings rat.dense_range_cast _ h.1 h.2,
    { intros a ha b hb hab,
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := ⟨ha, hb⟩,
      exact not_frequently_of_upcrossings_lt_top hab (hf₂ a b (rat.cast_lt.1 hab)).ne } },
  { obtain ⟨a, b, hab, h₁, h₂⟩ := ennreal.exists_upcrossings_of_not_bounded_under hf₁.ne h,
    exact false.elim ((hf₂ a b hab).ne
      (upcrossings_eq_top_of_frequently_lt (rat.cast_lt.2 hab) h₁ h₂)) }
end

/-- An L¹-bounded submartingale has bounded upcrossings almost everywhere. -/
lemma submartingale.upcrossings_ae_lt_top' [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) (hab : a < b) :
  ∀ᵐ ω ∂μ, upcrossings a b f ω < ∞ :=
begin
  refine ae_lt_top (hf.adapted.measurable_upcrossings hab) _,
  have := hf.mul_lintegral_upcrossings_le_lintegral_pos_part a b,
  rw [mul_comm, ← ennreal.le_div_iff_mul_le] at this,
  { refine (lt_of_le_of_lt this (ennreal.div_lt_top _ _)).ne,
    { have hR' : ∀ n, ∫⁻ ω, ∥f n ω - a∥₊ ∂μ ≤ R + ∥a∥₊ * μ set.univ,
      { simp_rw snorm_one_eq_lintegral_nnnorm at hbdd,
        intro n,
        refine (lintegral_mono _ : ∫⁻ ω, ∥f n ω - a∥₊ ∂μ ≤ ∫⁻ ω, ∥f n ω∥₊ + ∥a∥₊ ∂μ).trans _,
        { intro ω,
          simp_rw [sub_eq_add_neg, ← nnnorm_neg a, ← ennreal.coe_add, ennreal.coe_le_coe],
          exact nnnorm_add_le _ _ },
        { simp_rw [ lintegral_add_right _ measurable_const, lintegral_const],
          exact add_le_add (hbdd _) le_rfl } },
      refine ne_of_lt (supr_lt_iff.2 ⟨R + ∥a∥₊ * μ set.univ, ennreal.add_lt_top.2
          ⟨ennreal.coe_lt_top, ennreal.mul_lt_top ennreal.coe_lt_top.ne (measure_ne_top _ _)⟩,
          λ n, le_trans _ (hR' n)⟩),
      refine lintegral_mono (λ ω, _),
      rw [ennreal.of_real_le_iff_le_to_real, ennreal.coe_to_real, coe_nnnorm],
      by_cases hnonneg : 0 ≤ f n ω - a,
      { rw [lattice_ordered_comm_group.pos_of_nonneg _ hnonneg,
          real.norm_eq_abs, abs_of_nonneg hnonneg] },
      { rw lattice_ordered_comm_group.pos_of_nonpos _ (not_le.1 hnonneg).le,
        exact norm_nonneg _ },
      { simp only [ne.def, ennreal.coe_ne_top, not_false_iff] } },
    { simp only [hab, ne.def, ennreal.of_real_eq_zero, sub_nonpos, not_le] } },
  { simp only [hab, ne.def, ennreal.of_real_eq_zero, sub_nonpos, not_le, true_or]},
  { simp only [ne.def, ennreal.of_real_ne_top, not_false_iff, true_or] }
end

lemma submartingale.upcrossings_ae_lt_top [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞ :=
begin
  simp only [ae_all_iff, eventually_imp_distrib_left],
  rintro a b hab,
  exact hf.upcrossings_ae_lt_top' hbdd (rat.cast_lt.2 hab),
end

/-- An L¹-bounded submartingale converges almost everywhere. -/
lemma submartingale.exists_ae_tendsto_of_bdd [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ ω ∂μ, ∃ c, tendsto (λ n, f n ω) at_top (𝓝 c) :=
begin
  filter_upwards [hf.upcrossings_ae_lt_top hbdd, ae_bdd_liminf_at_top_of_snorm_bdd one_ne_zero
    (λ n, (hf.strongly_measurable n).measurable.mono (ℱ.le n) le_rfl) hbdd] with ω h₁ h₂,
  exact tendsto_of_uncrossing_lt_top h₂ h₁,
end

lemma submartingale.exists_ae_trim_tendsto_of_bdd [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ ω ∂(μ.trim (Sup_le (λ m ⟨n, hn⟩, hn ▸ ℱ.le _) : (⨆ n, ℱ n) ≤ m0)),
    ∃ c, tendsto (λ n, f n ω) at_top (𝓝 c) :=
begin
  rw [ae_iff, trim_measurable_set_eq],
  { exact hf.exists_ae_tendsto_of_bdd hbdd },
  { exact measurable_set.compl (@measurable_set_exists_tendsto _ _ _ _ _ _ (⨆ n, ℱ n) _ _ _ _ _
    (λ n, ((hf.strongly_measurable n).measurable.mono (le_Sup ⟨n, rfl⟩) le_rfl))) }
end

/-- **Almost everywhere martingale convergence theorem**: An L¹-bounded submartingale converges
almost everywhere to a `⨆ n, ℱ n`-measurable function. -/
lemma submartingale.ae_tendsto_limit_process [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ ω ∂μ, tendsto (λ n, f n ω) at_top (𝓝 (ℱ.limit_process f μ ω)) :=
begin
  classical,
  suffices : ∃ g, strongly_measurable[⨆ n, ℱ n] g ∧ ∀ᵐ ω ∂μ, tendsto (λ n, f n ω) at_top (𝓝 (g ω)),
  { rw [limit_process, dif_pos this],
    exact (classical.some_spec this).2 },
  set g' : Ω → ℝ := λ ω, if h : ∃ c, tendsto (λ n, f n ω) at_top (𝓝 c) then h.some else 0,
  have hle : (⨆ n, ℱ n) ≤ m0 := Sup_le (λ m ⟨n, hn⟩, hn ▸ ℱ.le _),
  have hg' : ∀ᵐ ω ∂(μ.trim hle), tendsto (λ n, f n ω) at_top (𝓝 (g' ω)),
  { filter_upwards [hf.exists_ae_trim_tendsto_of_bdd hbdd] with ω hω,
    simp_rw [g', dif_pos hω],
    exact hω.some_spec },
  have hg'm : @ae_strongly_measurable _ _ _ (⨆ n, ℱ n) g' (μ.trim hle) :=
    (@ae_measurable_of_tendsto_metrizable_ae' _ _ (⨆ n, ℱ n) _ _ _ _ _ _ _
      (λ n, ((hf.strongly_measurable n).measurable.mono
      (le_Sup ⟨n, rfl⟩ : ℱ n ≤ ⨆ n, ℱ n) le_rfl).ae_measurable) hg').ae_strongly_measurable,
  obtain ⟨g, hgm, hae⟩ := hg'm,
  have hg : ∀ᵐ ω ∂μ.trim hle, tendsto (λ n, f n ω) at_top (𝓝 (g ω)),
  { filter_upwards [hae, hg'] with ω hω hg'ω,
    exact hω ▸ hg'ω },
  exact ⟨g, hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩,
end

/-- The limiting process of an Lᵖ-bounded submartingale is Lᵖ. -/
lemma submartingale.mem_ℒp_limit_process {p : ℝ≥0∞}
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) p μ ≤ R) :
  mem_ℒp (ℱ.limit_process f μ) p μ :=
mem_ℒp_limit_process_of_snorm_bdd
  (λ n, ((hf.strongly_measurable n).mono (ℱ.le n)).ae_strongly_measurable) hbdd

end ae_convergence

end measure_theory
