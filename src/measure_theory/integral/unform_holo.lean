import measure_theory.integral.complex
import measure_theory.measure.complex_lebesgue
import measure_theory.integral.divergence_theorem
import analysis.analytic.basic
import analysis.calculus.parametric_interval_integral
import data.complex.basic

open topological_space set measure_theory interval_integral metric filter function
open_locale interval real nnreal ennreal topological_space big_operators

noncomputable theory

universes u v

variables {E : Type u} [normed_group E] [normed_space ℂ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E]

namespace complex

lemma holo_test {R : ℝ} {z w : ℂ} (hw : w ∈ ball z R)
  {f : ℂ → E} (hd : differentiable_on ℂ f (closed_ball z R)) :

  f w  = (1/(2 • π • I)) • ∫ (θ : ℝ) in 0..2 * π,
    ((R * exp (θ * I) * I) / (z + R * exp (θ * I) - w) : ℂ) • f (z + R * exp (θ * I)) :=

begin
have := integral_circle_div_sub_of_differentiable_on hw hd,
simp only [this, one_div, nat.cast_bit0, real_smul, nsmul_eq_mul, nat.cast_one],
simp_rw ← smul_assoc,
simp,
simp_rw ← mul_assoc,
have hn : (2 * ↑π * I) ≠ 0, by {simp, simp [real.pi_ne_zero, complex.I_ne_zero],},
have tt := inv_mul_cancel hn,
simp_rw ← mul_assoc at tt,
rw tt,
simp,
end



def int_diff0 (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z w : ℂ): (ℝ → E) :=
λ θ, (1/(2 • π • I)) • ((R * exp (θ * I) * I) / (z + R * exp (θ * I) - w) : ℂ) • f (z + R * exp (θ * I))

lemma int_diff0_cont (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z w : ℂ) (hf : continuous f) (hw : w ∈ ball z R):
  continuous (int_diff0 R hR f z w) :=
begin
  rw int_diff0,
  simp,
  apply continuous.smul,
  exact continuous_const,
  apply continuous.smul,
  apply continuous.div,
  sorry,
sorry,
sorry,
sorry,
end



def int_diff0' (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z w : ℂ): (ℝ → E) :=
λ θ, (1/(2 • π • I)) • ((R * exp (θ * I) * I) / (z + R * exp (θ * I) - w)^2 : ℂ) • f (z + R * exp (θ * I))

def int_diff (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z : ℂ)
   : (ℂ → E) := λ w,  ∫ (θ : ℝ) in 0..2 * π, (int_diff0 R hR f z w θ)

def int_diff' (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z : ℂ)
   : (ℂ → E) := λ w,  ∫ (θ : ℝ) in 0..2 * π, (int_diff0' R hR f z w θ)

lemma int_diff_has_fdrevi (R : ℝ)  (hR: 0 < R) (z : ℂ) (f : ℂ → ℂ)  (hf: continuous f) :
  differentiable_on ℂ (int_diff R hR f z) (ball z R) :=
begin
rw int_diff,
simp_rw int_diff0,
rw differentiable_on,
simp_rw differentiable_within_at,
intros x hx,
set F: ℂ → ℝ → ℂ  := λ w, (λ θ, (int_diff0 R hR f z w θ)),
set F': ℂ → ℝ → ℂ := λ w, (λ θ, (int_diff0' R hR f z w θ)),
have hF_meas : ∀ᶠ y in 𝓝 x, ae_measurable (F y) (volume.restrict (Ι 0 (2 * π))) ,
by {simp_rw F,
    have : ∀ (y : ℂ), ae_measurable (int_diff0 R hR f z y) (volume.restrict (Ι 0 (2 * π))),
    by {intro y,
    have := continuous.ae_measurable (int_diff0_cont R hR f z y hf _),
    apply ae_measurable.restrict,
    apply this, sorry,},
    simp [this],
    },
have hF_int : interval_integrable (F x) volume 0  (2 * π),
by {simp_rw F,
  have := continuous.interval_integrable (int_diff0_cont R hR f z x hf hx) 0 (2*π),
  apply this,
  apply_instance,},
have  hF'_meas : ae_measurable (F' x) (volume.restrict (Ι 0 (2 * π))) , by {sorry},
set bound : ℝ → ℝ := λ r, ∥F' R r∥,
have h_bound : ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x R, ∥F' y t∥ ≤  bound t, by {sorry},
have  bound_integrable : interval_integrable bound volume 0 (2 * π) , by {sorry},
have h_diff : ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x R, has_deriv_at (λ y, F y t) (F' y t) y,
by {sorry},
have := interval_integral.has_deriv_at_integral_of_dominated_loc_of_deriv_le hR hF_meas hF_int hF'_meas
  h_bound bound_integrable h_diff,
simp_rw F at this,
simp_rw int_diff0 at this,
simp_rw has_deriv_at at this,
simp_rw has_deriv_at_filter at this,
simp_rw has_fderiv_within_at,
simp at *,
have h3:= this.2,
let der := (interval_integral (F' x) 0 (2 * π) volume),
let DER := continuous_linear_map.smul_right (1 : ℂ →L[ℂ] ℂ) der,
use DER,
simp_rw [DER, der],
have this2:= (has_fderiv_at_filter.mono h3),
apply this2,
rw nhds_within,
simp [inf_le_left],
end

lemma int_diff0_sub  (R : ℝ) (hR: 0 < R)  (f g : ℂ → ℂ) (z w : ℂ) : ∀ θ : ℝ,
   complex.abs (((int_diff0 R hR f z w ) θ)-((int_diff0 R hR g z w) θ)) =
   complex.abs (int_diff0 R hR (f -g) z w θ) :=
begin
  intro θ,
simp_rw int_diff0,
simp only [one_div, nat.cast_bit0, real_smul, nsmul_eq_mul, nat.cast_one, pi.sub_apply],
simp,
simp_rw ← mul_assoc,
ring_nf,
simp_rw [abs_mul],
simp,
end

lemma int_diff0_sub_bound  (R : ℝ) (hR: 0 < R)  (f : ℂ → ℂ) (z w : ℂ) (r : ℝ)
    (h:  ∀ (x : ℂ), (complex.abs (f x) ≤ abs r)) : ∀ θ : ℝ,
    complex.abs (int_diff0 R hR f z w θ) ≤ complex.abs (int_diff0 R hR (λ x, r) z w θ) :=
begin
intro θ,
simp_rw int_diff0,
simp,
simp_rw ← mul_assoc,
sorry,
end



lemma int_diff0_int (R : ℝ) (hR: 0 < R) (F : ℂ → ℂ) (F_cts :  continuous (F ))
  (z : ℂ) (w : ball z R): integrable (int_diff0 R hR (F) z w) (volume.restrict (Ioc 0  (2*π))) :=

begin
apply integrable_on.integrable,
rw ←  interval_integrable_iff_integrable_Ioc_of_le,
apply continuous_on.interval_integrable,
have hw:= w.property,
simp at hw,
have := int_diff0_cont R hR F z w F_cts,
simp at this,
have hc:= this hw,
apply continuous.continuous_on,
apply hc,
simp,
linarith [real.pi_pos],
end

lemma abs_aux (x : ℂ) (r : ℝ) (h : ∃ (b : ℂ), complex.abs (x-b)+ complex.abs(b) ≤  r) :
  complex.abs(x) ≤  r :=
begin
obtain ⟨b, hb⟩ := h,
sorry,
end

lemma UNIF_CONV_INT (R : ℝ) (hR: 0 < R) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)  (F_cts : ∀ n, continuous (F n))
   (hlim : tendsto_uniformly F f filter.at_top) (z : ℂ) (w : ball z R) :
tendsto (λn, ∫ (θ : ℝ) in 0..2 * π, (int_diff0 R hR (F n) z w) θ)
  at_top (𝓝 $  ∫ (θ : ℝ) in 0..2 * π, (int_diff0 R hR f z w) θ) :=

begin
have f_cont: continuous f, by {sorry,},

have F_measurable : ∀ n, ae_measurable (int_diff0 R hR (F n) z w) (volume.restrict (Ioc 0  (2*π))),
 by {intro n,
     have:= int_diff0_int R hR (F n) (F_cts n) z w,
     apply this.ae_measurable, },


have h_lim'' : ∀ (a : ℝ), tendsto (λ n, ((int_diff0 R hR (F n) z w)) a)
  at_top (𝓝 (((int_diff0 R hR f z w)) a)),

 by {rw metric.tendsto_uniformly_iff at hlim, simp_rw metric.tendsto_nhds, simp_rw  dist_comm,
  simp_rw int_diff0,
  simp at *,
  intros y ε hε,
  set r : ℂ :=  ((2 * (↑π * I))⁻¹ * (↑R * exp (↑y * I) * I / (z + ↑R * exp (↑y * I) - ↑w))),
  have hr: 0 < ∥ r ∥, by {simp, rw div_eq_inv_mul,
    apply mul_pos, rw inv_eq_one_div, rw one_div_pos,
    apply mul_pos, linarith, simp, apply real.pi_ne_zero,
    apply mul_pos,
    rw inv_pos,
    rw abs_pos,
    have hw:=w.property,
    simp at hw,
    by_contradiction hc,
    simp_rw dist_eq_norm at hw,
    have hc' : (w : ℂ)-z = R * exp (↑y * I), by {sorry,},
     simp_rw hc' at hw,
     simp at hw,
     rw abs_lt at hw,
     simp at hw,
     apply hw,
     simp,
     by_contradiction hrr,
     rw hrr at hR,
     simp at hR,
     apply hR,},
  have hr':  ∥ r ∥ ≠ 0, by {linarith,},
  let e:= (∥ r ∥)⁻¹ * (ε/2),
  have he: 0 < e, by {sorry,},
  have h_lim2:= hlim e he,
  obtain ⟨a, ha⟩ := h_lim2,
  use a,
  intros b hb,
  simp [ha b hb],
  simp_rw dist_eq_norm at *,
  simp_rw ← mul_sub,
  have hg: ∥(2 * (↑π * I))⁻¹ * (↑R * exp (↑y * I) * I / (z + ↑R * exp (↑y * I) - ↑w) *
    (f (z + ↑R * exp (↑y * I)) - F b (z + ↑R * exp (↑y * I))))∥ =
    ∥(2 * (↑π * I))⁻¹ * (↑R * exp (↑y * I) * I / (z + ↑R * exp (↑y * I) - ↑w)) ∥ *
    ∥ (f (z + ↑R * exp (↑y * I)) - F b (z + ↑R * exp (↑y * I)))∥, by {simp, ring,},
    rw hg,
    simp_rw ← r,
    have haa:= ha b hb,
    have hab:= haa (z + ↑R * exp (↑y * I)),
    have haav: ∥ r ∥ * ∥f (z + ↑R * exp (↑y * I)) - F b (z + ↑R * exp (↑y * I))∥ < ∥ r ∥ * e,
    by {apply mul_lt_mul_of_pos_left hab hr,},
    simp_rw e at haav,
    apply lt_trans haav,
    rw div_eq_inv_mul,
    simp_rw ← mul_assoc,
    simp_rw [mul_inv_cancel hr'],
    simp,
    rw  mul_lt_iff_lt_one_left,
    rw inv_eq_one_div,
    linarith,
    apply hε,},

have h_lim' : ∀ᵐ a ∂(volume.restrict (Ioc 0  (2*π))), tendsto (λ n, ((int_diff0 R hR (F n) z w)) a)
  at_top (𝓝 (((int_diff0 R hR f z w)) a)),
  by {simp [h_lim''],},
rw metric.tendsto_uniformly_iff at hlim,
simp at hlim,
have hlimb:= hlim 1 (zero_lt_one),
obtain ⟨ a, ha⟩ :=hlimb,
set bound: ℝ → ℝ :=λ θ, (∑ (i : finset.range (a+1) ),complex.abs ((int_diff0 R hR (F i) z w) θ))  +
complex.abs ((int_diff0 R hR (λ x, 1) z w) θ)  + complex.abs ((int_diff0 R hR f z w) θ),

have h_bound : ∀ n, ∀ᵐ a ∂(volume.restrict (Ioc 0  (2*π))), ∥(int_diff0 R hR (F n) z w) a∥ ≤ bound a,
by {
  intro n,
  rw  ae_restrict_iff' at *,
  rw eventually_iff_exists_mem,
  use ⊤,
  simp,
  intros y hyl hyu,
  by_cases (n ≤ a),
  simp_rw bound,
  sorry,
  simp at h,
  apply abs_aux ((int_diff0 R hR (F n) z w) y) (bound y),
  use int_diff0 R hR f z ↑w y,
  rw int_diff0_sub,
  simp_rw bound,
  simp,
  have := int_diff0_sub_bound R hR ((F n) - f) z w 1,
  have haan:= ha n h.le,
  simp at this,
  simp_rw dist_eq_norm at *,
  simp at haan,
  have haf:  ∀ (x : ℂ), abs (F n x - f x) ≤  1, by {intro x, sorry,},
  have h5:= this haf,
  have h6:= h5 y,

  sorry,
  all_goals {simp only [measurable_set_Ioc]},},


have bound_integrable : integrable bound (volume.restrict (Ioc 0  (2*π))), by {sorry,},
have := tendsto_integral_of_dominated_convergence bound F_measurable bound_integrable h_bound h_lim',
have pi: 0 ≤ 2*π , by {sorry},
simp_rw  integral_of_le pi,
apply this,
end

lemma unif_of_diff_is_diff (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) (R : ℝ)  (hR: 0 < R)
  (hdiff : ∀ (n : ℕ), differentiable_on ℂ (F n) (closed_ball z R))
  (hlim : tendsto_uniformly F f filter.at_top) :
  differentiable_on ℂ f (ball z R) :=
begin
have F_measurable : ∀ n, integrable (F n) volume, by {sorry,},
have F_cts : ∀ n, continuous (F n) , by {sorry,},
rw differentiable_on,
intros x hx,
have key:= UNIF_CONV_INT R hR F f F_cts hlim z ⟨x, hx⟩,
--have key := int_diff_of_uniform' F f z x R hR hlim,
rw differentiable_within_at,
have h0:= int_diff R hR f z,
--have h1:= holo_test hx (hdiff _),
have hf: continuous f, by {sorry,},
have HF:= int_diff_has_fdrevi R hR x f hf,
rw differentiable_on at HF,
have HF2:= HF x,
simp [hx, hR] at HF2,
rw differentiable_within_at at HF2,
obtain ⟨D, hD⟩:= HF2,
use D,
simp_rw has_fderiv_within_at_iff_tendsto at *,
rw metric.tendsto_nhds at *,
rw tendsto_uniformly_iff at hlim,
simp_rw dist_eq_norm at *,
intros ε hε,
have hlim2:= hlim ε hε,
simp at *,
obtain ⟨a, ha⟩ := hlim2,
have HH: ∀ (y : ℂ), f y - f x - (D y - D x) =
(f y - F a y) - ((f x)- (F a x)) + ((F a y)- (F a x))  - (D y - D x), by {sorry,},
simp_rw HH,
rw int_diff at hD,
simp at hD,
sorry,
end

end complex
