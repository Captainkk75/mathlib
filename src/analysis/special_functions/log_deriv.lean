/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import analysis.special_functions.log
import analysis.special_functions.exp_deriv

/-!
# Derivative and series expansion of real logarithm

In this file we prove that `real.log` is infinitely smooth at all nonzero `x : ℝ`. We also prove
that the series `∑' n : ℕ, x ^ (n + 1) / (n + 1)` converges to `(-real.log (1 - x))` for all
`x : ℝ`, `|x| < 1`.

## Tags

logarighm, derivative
-/

open filter finset set
open_locale topological_space big_operators

namespace real

variables {x : ℝ}

lemma has_strict_deriv_at_log_of_pos (hx : 0 < x) : has_strict_deriv_at log x⁻¹ x :=
have has_strict_deriv_at log (exp $ log x)⁻¹ x,
from (has_strict_deriv_at_exp $ log x).of_local_left_inverse (continuous_at_log hx.ne')
  (ne_of_gt $ exp_pos _) $ eventually.mono (lt_mem_nhds hx) @exp_log,
by rwa [exp_log hx] at this

lemma has_strict_deriv_at_log (hx : x ≠ 0) : has_strict_deriv_at log x⁻¹ x :=
begin
  cases hx.lt_or_lt with hx hx,
  { convert (has_strict_deriv_at_log_of_pos (neg_pos.mpr hx)).comp x (has_strict_deriv_at_neg x),
    { ext y, exact (log_neg_eq_log y).symm },
    { field_simp [hx.ne] } },
  { exact has_strict_deriv_at_log_of_pos hx }
end

lemma has_deriv_at_log (hx : x ≠ 0) : has_deriv_at log x⁻¹ x :=
(has_strict_deriv_at_log hx).has_deriv_at

lemma differentiable_at_log (hx : x ≠ 0) : differentiable_at ℝ log x :=
(has_deriv_at_log hx).differentiable_at

lemma differentiable_on_log : differentiable_on ℝ log {0}ᶜ :=
λ x hx, (differentiable_at_log hx).differentiable_within_at

@[simp] lemma differentiable_at_log_iff : differentiable_at ℝ log x ↔ x ≠ 0 :=
⟨λ h, continuous_at_log_iff.1 h.continuous_at, differentiable_at_log⟩

lemma deriv_log (x : ℝ) : deriv log x = x⁻¹ :=
if hx : x = 0 then
  by rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_log_iff.1 (not_not.2 hx)), hx,
    inv_zero]
else (has_deriv_at_log hx).deriv

@[simp] lemma deriv_log' : deriv log = has_inv.inv := funext deriv_log

lemma times_cont_diff_on_log {n : with_top ℕ} : times_cont_diff_on ℝ n log {0}ᶜ :=
begin
  suffices : times_cont_diff_on ℝ ⊤ log {0}ᶜ, from this.of_le le_top,
  refine (times_cont_diff_on_top_iff_deriv_of_open is_open_compl_singleton).2 _,
  simp [differentiable_on_log, times_cont_diff_on_inv]
end

lemma times_cont_diff_at_log {n : with_top ℕ} : times_cont_diff_at ℝ n log x ↔ x ≠ 0 :=
⟨λ h, continuous_at_log_iff.1 h.continuous_at,
  λ hx, (times_cont_diff_on_log x hx).times_cont_diff_at $
    is_open.mem_nhds is_open_compl_singleton hx⟩

end real

section log_differentiable
open real

section deriv

variables {f : ℝ → ℝ} {x f' : ℝ} {s : set ℝ}

lemma has_deriv_within_at.log (hf : has_deriv_within_at f f' s x) (hx : f x ≠ 0) :
  has_deriv_within_at (λ y, log (f y)) (f' / (f x)) s x :=
begin
  rw div_eq_inv_mul,
  exact (has_deriv_at_log hx).comp_has_deriv_within_at x hf
end

lemma has_deriv_at.log (hf : has_deriv_at f f' x) (hx : f x ≠ 0) :
  has_deriv_at (λ y, log (f y)) (f' / f x) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hf.log hx
end

lemma has_strict_deriv_at.log (hf : has_strict_deriv_at f f' x) (hx : f x ≠ 0) :
  has_strict_deriv_at (λ y, log (f y)) (f' / f x) x :=
begin
  rw div_eq_inv_mul,
  exact (has_strict_deriv_at_log hx).comp x hf
end

lemma deriv_within.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, log (f x)) s x = (deriv_within f s x) / (f x) :=
(hf.has_deriv_within_at.log hx).deriv_within hxs

@[simp] lemma deriv.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  deriv (λx, log (f x)) x = (deriv f x) / (f x) :=
(hf.has_deriv_at.log hx).deriv

end deriv

section fderiv

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ}
  {s : set E}

lemma has_fderiv_within_at.log (hf : has_fderiv_within_at f f' s x) (hx : f x ≠ 0) :
  has_fderiv_within_at (λ x, log (f x)) ((f x)⁻¹ • f') s x :=
(has_deriv_at_log hx).comp_has_fderiv_within_at x hf

lemma has_fderiv_at.log (hf : has_fderiv_at f f' x) (hx : f x ≠ 0) :
  has_fderiv_at (λ x, log (f x)) ((f x)⁻¹ • f') x :=
(has_deriv_at_log hx).comp_has_fderiv_at x hf

lemma has_strict_fderiv_at.log (hf : has_strict_fderiv_at f f' x) (hx : f x ≠ 0) :
  has_strict_fderiv_at (λ x, log (f x)) ((f x)⁻¹ • f') x :=
(has_strict_deriv_at_log hx).comp_has_strict_fderiv_at x hf

lemma differentiable_within_at.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) :
  differentiable_within_at ℝ (λx, log (f x)) s x :=
(hf.has_fderiv_within_at.log hx).differentiable_within_at

@[simp] lemma differentiable_at.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  differentiable_at ℝ (λx, log (f x)) x :=
(hf.has_fderiv_at.log hx).differentiable_at

lemma times_cont_diff_at.log {n} (hf : times_cont_diff_at ℝ n f x) (hx : f x ≠ 0) :
  times_cont_diff_at ℝ n (λ x, log (f x)) x :=
(times_cont_diff_at_log.2 hx).comp x hf

lemma times_cont_diff_within_at.log {n} (hf : times_cont_diff_within_at ℝ n f s x) (hx : f x ≠ 0) :
  times_cont_diff_within_at ℝ n (λ x, log (f x)) s x :=
(times_cont_diff_at_log.2 hx).comp_times_cont_diff_within_at x hf

lemma times_cont_diff_on.log {n} (hf : times_cont_diff_on ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
  times_cont_diff_on ℝ n (λ x, log (f x)) s :=
λ x hx, (hf x hx).log (hs x hx)

lemma times_cont_diff.log {n} (hf : times_cont_diff ℝ n f) (h : ∀ x, f x ≠ 0) :
  times_cont_diff ℝ n (λ x, log (f x)) :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ x, hf.times_cont_diff_at.log (h x)

lemma differentiable_on.log (hf : differentiable_on ℝ f s) (hx : ∀ x ∈ s, f x ≠ 0) :
  differentiable_on ℝ (λx, log (f x)) s :=
λx h, (hf x h).log (hx x h)

@[simp] lemma differentiable.log (hf : differentiable ℝ f) (hx : ∀ x, f x ≠ 0) :
  differentiable ℝ (λx, log (f x)) :=
λx, (hf x).log (hx x)

lemma fderiv_within.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, log (f x)) s x = (f x)⁻¹ • fderiv_within ℝ f s x :=
(hf.has_fderiv_within_at.log hx).fderiv_within hxs

@[simp] lemma fderiv.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  fderiv ℝ (λx, log (f x)) x = (f x)⁻¹ • fderiv ℝ f x :=
(hf.has_fderiv_at.log hx).fderiv

end fderiv

end log_differentiable

namespace real

/-- The function `x * log (1 + t / x)` tends to `t` at `+∞`. -/
lemma tendsto_mul_log_one_plus_div_at_top (t : ℝ) :
  tendsto (λ x, x * log (1 + t / x)) at_top (𝓝 t) :=
begin
  have h₁ : tendsto (λ h, h⁻¹ * log (1 + t * h)) (𝓝[≠] 0) (𝓝 t),
  { simpa [has_deriv_at_iff_tendsto_slope] using
      ((has_deriv_at_const _ 1).add ((has_deriv_at_id (0 : ℝ)).const_mul t)).log (by simp) },
  have h₂ : tendsto (λ x : ℝ, x⁻¹) at_top (𝓝[≠] 0) :=
    tendsto_inv_at_top_zero'.mono_right (nhds_within_mono _ (λ x hx, (set.mem_Ioi.mp hx).ne')),
  convert h₁.comp h₂,
  ext,
  field_simp [mul_comm],
end

open_locale big_operators

/-- A crude lemma estimating the difference between `log (1-x)` and its Taylor series at `0`,
where the main point of the bound is that it tends to `0`. The goal is to deduce the series
expansion of the logarithm, in `has_sum_pow_div_log_of_abs_lt_1`.
-/
lemma abs_log_sub_add_sum_range_le {x : ℝ} (h : |x| < 1) (n : ℕ) :
  |((∑ i in range n, x^(i+1)/(i+1)) + log (1-x))| ≤ (|x|)^(n+1) / (1 - |x|) :=
begin
  /- For the proof, we show that the derivative of the function to be estimated is small,
  and then apply the mean value inequality. -/
  let F : ℝ → ℝ := λ x, ∑ i in range n, x^(i+1)/(i+1) + log (1-x),
  -- First step: compute the derivative of `F`
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, deriv F y = - (y^n) / (1 - y),
  { assume y hy,
    have : (∑ i in range n, (↑i + 1) * y ^ i / (↑i + 1)) = (∑ i in range n, y ^ i),
    { congr' with i,
      have : (i : ℝ) + 1 ≠ 0 := ne_of_gt (nat.cast_add_one_pos i),
      field_simp [this, mul_comm] },
    field_simp [F, this, ← geom_sum_def, geom_sum_eq (ne_of_lt hy.2),
                sub_ne_zero_of_ne (ne_of_gt hy.2), sub_ne_zero_of_ne (ne_of_lt hy.2)],
    ring },
  -- second step: show that the derivative of `F` is small
  have B : ∀ y ∈ Icc (-|x|) (|x|), |deriv F y| ≤ |x|^n / (1 - |x|),
  { assume y hy,
    have : y ∈ Ioo (-(1 : ℝ)) 1 := ⟨lt_of_lt_of_le (neg_lt_neg h) hy.1, lt_of_le_of_lt hy.2 h⟩,
    calc |deriv F y| = | -(y^n) / (1 - y)| : by rw [A y this]
    ... ≤ |x|^n / (1 - |x|) :
      begin
        have : |y| ≤ |x| := abs_le.2 hy,
        have : 0 < 1 - |x|, by linarith,
        have : 1 - |x| ≤ |1 - y| := le_trans (by linarith [hy.2]) (le_abs_self _),
        simp only [← pow_abs, abs_div, abs_neg],
        apply_rules [div_le_div, pow_nonneg, abs_nonneg, pow_le_pow_of_le_left]
      end },
  -- third step: apply the mean value inequality
  have C : ∥F x - F 0∥ ≤ (|x|^n / (1 - |x|)) * ∥x - 0∥,
  { have : ∀ y ∈ Icc (- |x|) (|x|), differentiable_at ℝ F y,
    { assume y hy,
      have : 1 - y ≠ 0 := sub_ne_zero_of_ne (ne_of_gt (lt_of_le_of_lt hy.2 h)),
      simp [F, this] },
    apply convex.norm_image_sub_le_of_norm_deriv_le this B (convex_Icc _ _) _ _,
    { simpa using abs_nonneg x },
    { simp [le_abs_self x, neg_le.mp (neg_le_abs_self x)] } },
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, norm_eq_abs, div_mul_eq_mul_div, pow_succ'] using C
end

/-- Power series expansion of the logarithm around `1`. -/
theorem has_sum_pow_div_log_of_abs_lt_1 {x : ℝ} (h : |x| < 1) :
  has_sum (λ (n : ℕ), x ^ (n + 1) / (n + 1)) (-log (1 - x)) :=
begin
  rw summable.has_sum_iff_tendsto_nat,
  show tendsto (λ (n : ℕ), ∑ (i : ℕ) in range n, x ^ (i + 1) / (i + 1)) at_top (𝓝 (-log (1 - x))),
  { rw [tendsto_iff_norm_tendsto_zero],
    simp only [norm_eq_abs, sub_neg_eq_add],
    refine squeeze_zero (λ n, abs_nonneg _) (abs_log_sub_add_sum_range_le h) _,
    suffices : tendsto (λ (t : ℕ), |x| ^ (t + 1) / (1 - |x|)) at_top
      (𝓝 (|x| * 0 / (1 - |x|))), by simpa,
    simp only [pow_succ],
    refine (tendsto_const_nhds.mul _).div_const,
    exact tendsto_pow_at_top_nhds_0_of_lt_1 (abs_nonneg _) h },
  show summable (λ (n : ℕ), x ^ (n + 1) / (n + 1)),
  { refine summable_of_norm_bounded _ (summable_geometric_of_lt_1 (abs_nonneg _) h) (λ i, _),
    calc ∥x ^ (i + 1) / (i + 1)∥
    = |x| ^ (i+1) / (i+1) :
      begin
        have : (0 : ℝ) ≤ i + 1 := le_of_lt (nat.cast_add_one_pos i),
        rw [norm_eq_abs, abs_div, ← pow_abs, abs_of_nonneg this],
      end
    ... ≤ |x| ^ (i+1) / (0 + 1) :
      begin
        apply_rules [div_le_div_of_le_left, pow_nonneg, abs_nonneg, add_le_add_right,
          i.cast_nonneg],
        norm_num,
      end
    ... ≤ |x| ^ i :
      by simpa [pow_succ'] using mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) i) (le_of_lt h) }
end

lemma sq_eq_sq_iff_abs_eq_abs {R : Type*} [linear_ordered_ring R] (x y : R) :
  x^2 = y^2 ↔ |x| = |y| :=
⟨λ h, (abs_le_abs_of_sq_le_sq h.le).antisymm (abs_le_abs_of_sq_le_sq h.ge),
 λ h, by rw [←sq_abs, h, sq_abs]⟩

@[simp] lemma sq_eq_one_iff {R : Type*} [linear_ordered_ring R] (x : R) :
  x^2 = 1 ↔ x = 1 ∨ x = -1 :=
by rw [←abs_eq_abs, ←sq_eq_sq_iff_abs_eq_abs, one_pow]

lemma sq_ne_one_iff {R : Type*} [linear_ordered_ring R] (x : R) : x^2 ≠ 1 ↔ x ≠ 1 ∧ x ≠ -1 :=
(not_iff_not.2 (sq_eq_one_iff _)).trans not_or_distrib

@[simp] lemma sq_lt_one_iff {R : Type*} [linear_ordered_ring R] (x : R) : x^2 < 1 ↔ |x| < 1 :=
⟨λ h, abs_lt_of_sq_lt_sq (by simp [h]) zero_le_one, λ h, by simpa using sq_lt_sq h⟩

lemma newbound {x : ℝ} (h : |x| < 1) (n : ℕ) :
  |(2*(∑ i in range n, x^(2*i+1)/(2*i+1)) - log ((1+x)/(1-x)))| ≤ 2 * (|x|)^(2*n+1) / (1 - x^2) :=
begin
  /- For the proof, we show that the derivative of the function to be estimated is small,
  and then apply the mean value inequality. -/
  let F : ℝ → ℝ := λ x, 2*(∑ i in range n, x^(2*i+1)/(2*i+1)) - log ((1+x)/(1-x)),
  -- First step: compute the derivative of `F`
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, deriv F y = - 2 * ((y^2)^n) / (1 - y^2),
  { intros y hy,
    have : (∑ i in range n, (2*↑i+1) * y ^ (2*i) / (2*i+1)) = (∑ i in range n, (y^2) ^ i),
    { congr' with i,
      have : 2 * (i : ℝ) + 1 ≠ 0 := by exact_mod_cast (nat.succ_ne_zero (2 * i)),
      field_simp [this, mul_comm, ←pow_mul] },
    have hy' : 0 < 1 + y, simpa [add_comm] using sub_pos_of_lt hy.1,
    have hy'' : y^2 ≠ 1 := by simp [hy.1.ne', hy.2.ne],
    field_simp [F, this, hy'.ne', hy'.ne, hy.2.ne, hy.2.ne', ←geom_sum_def, hy'', geom_sum_eq,
      sub_ne_zero_of_ne, hy''.symm],
    ring },
  -- second step: show that the derivative of `F` is small
  have B : ∀ y ∈ Icc (-|x|) (|x|), |deriv F y| ≤ 2 * |x|^(2*n) / (1 - x^2),
  { intros y hy,
    have : y ∈ Ioo (-(1 : ℝ)) 1 := ⟨(neg_lt_neg h).trans_le hy.1, hy.2.trans_lt h⟩,
    rw [A y this, abs_div, abs_mul, ←pow_abs, ←pow_abs, pow_mul, abs_neg, abs_two, pow_bit0_abs,
      pow_bit0_abs, abs_of_pos (show 0 < 1 - y^2, by simpa [abs_lt] using this)],
    simp only [abs_div, ←pow_abs, abs_mul, pow_mul, pow_bit0_abs y, abs_neg, abs_two],
    have : 0 < 1 - x^2, by simpa using h,
    have yx : y^2 ≤ x^2,
    { apply sq_le_sq,
      rwa abs_le },
    refine div_le_div (mul_nonneg zero_le_two (pow_nonneg (sq_nonneg _) _)) _ this
      (sub_le_sub_left yx _),
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (sq_nonneg _) yx _) zero_le_two },
  -- third step: apply the mean value inequality
  have C : ∥F x - F 0∥ ≤ (2 * |x|^(2*n) / (1 - x^2)) * ∥x - 0∥,
  { have : ∀ y ∈ Icc (- |x|) (|x|), differentiable_at ℝ F y,
    { intros y hy,
      have hy' : 0 < 1 + y := neg_lt_iff_pos_add'.1 ((neg_lt_neg h).trans_le hy.1),
      simp [F, sub_ne_zero_of_ne (hy.2.trans_lt h).ne', hy'.ne'] },
    apply convex.norm_image_sub_le_of_norm_deriv_le this B (convex_Icc _ _) _ _,
    { simpa using abs_nonneg x },
    { simp [le_abs_self x, neg_le.mp (neg_le_abs_self x)] } },
  simpa [F, norm_eq_abs, pow_succ', div_mul_eq_mul_div, mul_assoc] using C,
end

lemma log_two_near_10 : |log 2 - 836158 / 1206321| ≤ 1/10^10 :=
begin
  suffices : |log 2 - 836158 / 1206321| ≤ 1/17179869184 + (1/10^10 - 1/2^34),
  { norm_num1 at *,
    assumption },
  have t : |(2⁻¹ : ℝ)| = 2⁻¹,
  { rw abs_of_pos, norm_num },
  have z := real.abs_log_sub_add_sum_range_le (show |(2⁻¹ : ℝ)| < 1, by { rw t, norm_num }) 34,
  rw t at z,
  norm_num1 at z,
  rw [one_div (2:ℝ), log_inv, ←sub_eq_add_neg, _root_.abs_sub_comm] at z,
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _),
  simp_rw [sum_range_succ],
  norm_num,
  rw abs_of_pos;
  norm_num
end

-- {0, 1, 2/3, 7/10, 9/13, 61/88, 192/277, 253/365, 445/642, 1143/1649, 1588/2291, 2731/3940,
--  4319/6231, 7050/10171, 25469/36744, 261740/377611, 287209/414355, 548949/791966,
--  836158/1206321, 2221265/3204608, 3057423/4410929, 5278688/7615537, 8336111/12026466,
--  13614799/19642003, 49180508/70952475, 111975815/161546953, 385107953/555593334,
--  497083768/717140287, 6847196937/9878417065, 48427462327/69866059742}

set_option profiler true

lemma log_two_near_20 : |log 2 - 48427462327/69866059742| ≤ 9/10^21 :=
begin
  suffices : |log 2 - 48427462327/69866059742| ≤ 1/145891985508683145612 + (9/10^21 - 1/(4 * 3^41)),
  { norm_num1 at *,
    assumption },
  have t : |(3⁻¹ : ℝ)| = 3⁻¹ := abs_of_pos (by norm_num1),
  have z := newbound (show |(3⁻¹ : ℝ)| < 1, by { rw t, norm_num1 }) 21,
  rw [t, _root_.abs_sub_comm] at z,
  norm_num1 at z,
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _),
  simp_rw [sum_range_succ, sum_range_zero],
  norm_num1,
  sorry,
  -- rw [abs_neg, abs_of_pos],
  -- by { norm_num1 },
  -- by { norm_num1 },
end

#exit

lemma log_two_gt_d20 : 0.69314718055994530940 < log 2 :=
lt_of_lt_of_le (by norm_num1) (sub_le.1 (abs_sub_le_iff.1 log_two_near_20).2)

lemma log_two_lt_d20 : log 2 < 0.69314718055994530943 :=
lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_two_near_20).1) (by norm_num)

lemma log_three_div_two_near_20 : |log (3/2) - 10098979643/24907148460| ≤ 1/10^21 :=
begin
  suffices :
    |log (3/2) - 10098979643/24907148460| ≤ 1/2235174179077148437500 + (1/10^21 - 1/(2^2*3*5^29)),
  { norm_num1 at *,
    assumption },
  have t : |(5⁻¹ : ℝ)| = 5⁻¹ := abs_of_pos (by norm_num1),
  have z := newbound (show |(5⁻¹ : ℝ)| < 1, by { rw t, norm_num1 }) 15,
  rw [t, _root_.abs_sub_comm] at z,
  norm_num1 at z,
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _),
  simp_rw [sum_range_succ, sum_range_zero],
  norm_num1,
  rw [abs_of_pos],
  { norm_num1 },
  { norm_num1 },
end.

example : (130029316460388448573787 / 646081657495872133645625196314533858898489550 : ℝ) ≤ 78256967394537077627 / 36472996377170786403000000000000000000000 :=
begin
  rw div_le_div_iff,
  { norm_num1 },
  simp only [zero_lt_bit0, bit1_pos],
  -- { norm_num1 },
  -- norm_num1,
  -- simp only [zero_lt_bit0, zero_lt_bit1, bit1_pos],
  -- library_search,
end

#exit

lemma log_log_two_approx : |log (log 2) - sorry| ≤ 1/10^20 :=
begin
  let l2 : ℝ := 48427462327/69866059742,
  have := newbound,
  -- have : log (log 2 / l2)
  -- have := log_two_near_20,
end

-- lemma log_three_near_20 : |log 3 - sorry| ≤ 1/10^20 :=
-- begin
--   have : log (3/2) + log 2 = log 3,
--   { rw [log_div, sub_add_cancel]; norm_num1 },
--   rw ←this,

-- end

-- lemma exp_one_near_20 : |exp 1 - 363916618873/133877442384| ≤ 1/10^20 :=
-- begin
--   apply exp_approx_start,
--   iterate 21 { refine exp_1_approx_succ_eq (by norm_num1; refl) (by norm_cast; refl) _ },
--   norm_num1,
--   refine exp_approx_end' _ (by norm_num1; refl) _ (by norm_cast; refl) (by simp) _,
--   rw [_root_.abs_one, abs_of_pos]; norm_num1,
-- end

end real
