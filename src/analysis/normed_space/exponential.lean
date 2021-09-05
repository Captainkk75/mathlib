/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import algebra.char_p.algebra
import analysis.calculus.deriv
import analysis.specific_limits
import data.complex.exponential
import analysis.complex.basic
import topology.metric_space.cau_seq_filter

/-!
# Exponential in a Banach algebra

In this file, we define `exp 𝕂 𝔸`, the exponential map in a normed algebra `𝔸` over a nondiscrete
normed field `𝕂`. Although the definition doesn't require `𝔸` to be complete, we need to assume it
for most results.

We then prove basic results, as described below.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `has_strict_fderiv_at_exp_zero_of_radius_pos` : `exp 𝕂 𝔸` has strict Fréchet-derivative
  `1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero
  (see also `has_strict_deriv_at_exp_zero_of_radius_pos` for the case `𝔸 = 𝕂`)
- `exp_add_of_commute_of_lt_radius` : if `𝕂` has characteristic zero, then given two commuting
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
- `exp_add_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative, then given two
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
- `has_strict_fderiv_at_exp_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given a point `x` in the disk of convergence, `exp 𝕂 𝔸` as strict Fréchet-derivative
  `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at x (see also `has_strict_deriv_at_exp_of_lt_radius` for the case
  `𝔸 = 𝕂`)

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `exp_series_radius_eq_top` : the `formal_multilinear_series` defining `exp 𝕂 𝔸` has infinite
  radius of convergence
- `has_strict_fderiv_at_exp_zero` : `exp 𝕂 𝔸` has strict Fréchet-derivative `1 : 𝔸 →L[𝕂] 𝔸` at zero
  (see also `has_strict_deriv_at_exp_zero` for the case `𝔸 = 𝕂`)
- `exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
- `exp_add` : if `𝔸` is commutative, then we have `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
  for any `x` and `y`
- `has_strict_fderiv_at_exp` : if `𝔸` is commutative, then given any point `x`, `exp 𝕂 𝔸` as strict
  Fréchet-derivative `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at x (see also `has_strict_deriv_at_exp` for the
  case `𝔸 = 𝕂`)

### Other useful compatibility results

- `exp_eq_exp_of_field_extension` : given `𝕂' / 𝕂` a normed field extension (that is, an instance
  of `normed_algebra 𝕂 𝕂'`) and a normed algebra `𝔸` over both `𝕂` and `𝕂'` then
  `exp 𝕂 𝔸 = exp 𝕂' 𝔸`
- `complex.exp_eq_exp_ℂ_ℂ` : `complex.exp = exp ℂ ℂ`
- `real.exp_eq_exp_ℝ_ℝ` : `real.exp = exp ℝ ℝ`

-/

open filter is_R_or_C continuous_multilinear_map normed_field asymptotics
open_locale nat topological_space big_operators ennreal

section move_me

variables {S M : Type*} [semigroup S] [monoid M] [mul_action M S] [is_scalar_tower M S S]
   [smul_comm_class M S S]

lemma semiconj_by.smul_left (a : M) {s x y : S} (h : semiconj_by s x y) :
  semiconj_by (a • s) x y :=
by {unfold semiconj_by at *, rw [smul_mul_assoc, h, mul_smul_comm]}

lemma semiconj_by.smul_right (a : M) {s x y : S} (h : semiconj_by s x y) :
  semiconj_by s (a • x) (a • y) :=
by {unfold semiconj_by at *, rw [mul_smul_comm, h, smul_mul_assoc]}

lemma commute.smul_left (a : M) {b c : S} (h : commute b c) : commute (a • b) c :=
h.smul_left a

lemma commute.smul_right (a : M) {b c : S} (h : commute b c) : commute b (a • c) :=
h.smul_right a

end move_me

section any_field_any_algebra

variables (𝕂 𝔸 : Type*) [nondiscrete_normed_field 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]

/-- In a Banach algebra `𝔸` over a normed field `𝕂`, `exp_series 𝕂 𝔸` is the
`formal_multilinear_series` whose `n`-th term is the map `(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`.
Its sum is the exponential map `exp 𝕂 𝔸 : 𝔸 → 𝔸`. -/
def exp_series : formal_multilinear_series 𝕂 𝔸 𝔸 :=
  λ n, (1/n! : 𝕂) • continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸

/-- In a Banach algebra `𝔸` over a normed field `𝕂`, `exp 𝕂 𝔸 : 𝔸 → 𝔸` is the exponential map
determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `formal_multilinear_series` `exp_series 𝕂 𝔸`. -/
noncomputable def exp (x : 𝔸) : 𝔸 := (exp_series 𝕂 𝔸).sum x

variables {𝕂 𝔸}

lemma exp_series_apply_eq (x : 𝔸) (n : ℕ) : exp_series 𝕂 𝔸 n (λ _, x) = (1 / n! : 𝕂) • x^n :=
by simp [exp_series]

lemma exp_series_apply_eq' (x : 𝔸) :
  (λ n, exp_series 𝕂 𝔸 n (λ _, x)) = (λ n, (1 / n! : 𝕂) • x^n) :=
funext (exp_series_apply_eq x)

lemma exp_series_apply_eq_field (x : 𝕂) (n : ℕ) : exp_series 𝕂 𝕂 n (λ _, x) = x^n / n! :=
begin
  rw [div_eq_inv_mul, ←smul_eq_mul, inv_eq_one_div],
  exact exp_series_apply_eq x n,
end

lemma exp_series_apply_eq_field' (x : 𝕂) : (λ n, exp_series 𝕂 𝕂 n (λ _, x)) = (λ n, x^n / n!) :=
funext (exp_series_apply_eq_field x)

lemma exp_series_sum_eq (x : 𝔸) : (exp_series 𝕂 𝔸).sum x = ∑' (n : ℕ), (1 / n! : 𝕂) • x^n :=
tsum_congr (λ n, exp_series_apply_eq x n)

lemma exp_series_sum_eq_field (x : 𝕂) : (exp_series 𝕂 𝕂).sum x = ∑' (n : ℕ), x^n / n! :=
tsum_congr (λ n, exp_series_apply_eq_field x n)

lemma exp_eq_tsum : exp 𝕂 𝔸 = (λ x : 𝔸, ∑' (n : ℕ), (1 / n! : 𝕂) • x^n) :=
funext exp_series_sum_eq

lemma exp_eq_tsum_field : exp 𝕂 𝕂 = (λ x : 𝕂, ∑' (n : ℕ), x^n / n!) :=
funext exp_series_sum_eq_field

lemma exp_zero : exp 𝕂 𝔸 0 = 1 :=
begin
  suffices : (λ x : 𝔸, ∑' (n : ℕ), (1 / n! : 𝕂) • x^n) 0 = ∑' (n : ℕ), if n = 0 then 1 else 0,
  { have key : ∀ n ∉ ({0} : finset ℕ), (if n = 0 then (1 : 𝔸) else 0) = 0,
      from λ n hn, if_neg (finset.not_mem_singleton.mp hn),
    rw [exp_eq_tsum, this, tsum_eq_sum key, finset.sum_singleton],
    simp },
  refine tsum_congr (λ n, _),
  split_ifs with h h;
  simp [h]
end

lemma norm_exp_series_summable_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  summable (λ n, ∥exp_series 𝕂 𝔸 n (λ _, x)∥) :=
(exp_series 𝕂 𝔸).summable_norm_apply hx

lemma norm_exp_series_summable_of_mem_ball' (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  summable (λ n, ∥(1 / n! : 𝕂) • x^n∥) :=
begin
  change summable (norm ∘ _),
  rw ← exp_series_apply_eq',
  exact norm_exp_series_summable_of_mem_ball x hx
end

lemma norm_exp_series_field_summable_of_mem_ball (x : 𝕂)
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) :
  summable (λ n, ∥x^n / n!∥) :=
begin
  change summable (norm ∘ _),
  rw ← exp_series_apply_eq_field',
  exact norm_exp_series_summable_of_mem_ball x hx
end

section complete_algebra

variables [complete_space 𝔸]

lemma exp_series_summable_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  summable (λ n, exp_series 𝕂 𝔸 n (λ _, x)) :=
summable_of_summable_norm (norm_exp_series_summable_of_mem_ball x hx)

lemma exp_series_summable_of_mem_ball' (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  summable (λ n, (1 / n! : 𝕂) • x^n) :=
summable_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx)

lemma exp_series_field_summable_of_mem_ball [complete_space 𝕂] (x : 𝕂)
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) : summable (λ n, x^n / n!) :=
summable_of_summable_norm (norm_exp_series_field_summable_of_mem_ball x hx)

lemma exp_series_has_sum_exp_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_sum (λ n, exp_series 𝕂 𝔸 n (λ _, x)) (exp 𝕂 𝔸 x) :=
formal_multilinear_series.has_sum (exp_series 𝕂 𝔸) hx

lemma exp_series_has_sum_exp_of_mem_ball' (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_sum (λ n, (1 / n! : 𝕂) • x^n) (exp 𝕂 𝔸 x):=
begin
  rw ← exp_series_apply_eq',
  exact exp_series_has_sum_exp_of_mem_ball x hx
end

lemma exp_series_field_has_sum_exp_of_mem_ball [complete_space 𝕂] (x : 𝕂)
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) : has_sum (λ n, x^n / n!) (exp 𝕂 𝕂 x) :=
begin
  rw ← exp_series_apply_eq_field',
  exact exp_series_has_sum_exp_of_mem_ball x hx
end

lemma has_fpower_series_on_ball_exp_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_fpower_series_on_ball (exp 𝕂 𝔸) (exp_series 𝕂 𝔸) 0 (exp_series 𝕂 𝔸).radius :=
(exp_series 𝕂 𝔸).has_fpower_series_on_ball h

lemma has_fpower_series_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_fpower_series_at (exp 𝕂 𝔸) (exp_series 𝕂 𝔸) 0 :=
(has_fpower_series_on_ball_exp_of_radius_pos h).has_fpower_series_at

lemma continuous_on_exp :
  continuous_on (exp 𝕂 𝔸) (emetric.ball 0 (exp_series 𝕂 𝔸).radius) :=
formal_multilinear_series.continuous_on

lemma analytic_at_exp_of_mem_ball (x : 𝔸) (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  analytic_at 𝕂 (exp 𝕂 𝔸) x:=
begin
  by_cases h : (exp_series 𝕂 𝔸).radius = 0,
  { rw h at hx, exact (ennreal.not_lt_zero hx).elim },
  { have h := pos_iff_ne_zero.mpr h,
    exact (has_fpower_series_on_ball_exp_of_radius_pos h).analytic_at_of_mem hx }
end

/-- The exponential in a Banach-algebra `𝔸` over a normed field `𝕂` has strict Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_strict_fderiv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_strict_fderiv_at (exp 𝕂 𝔸) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
begin
  convert (has_fpower_series_at_exp_zero_of_radius_pos h).has_strict_fderiv_at,
  ext x,
  change x = exp_series 𝕂 𝔸 1 (λ _, x),
  simp [exp_series_apply_eq]
end

/-- The exponential in a Banach-algebra `𝔸` over a normed field `𝕂` has Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_fderiv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_fderiv_at (exp 𝕂 𝔸) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
(has_strict_fderiv_at_exp_zero_of_radius_pos h).has_fderiv_at

/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then `exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
lemma exp_add_of_commute_of_mem_ball [char_zero 𝕂]
  {x y : 𝔸} (hxy : commute x y) (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius)
  (hy : y ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y) :=
begin
  rw [exp_eq_tsum, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        (norm_exp_series_summable_of_mem_ball' x hx) (norm_exp_series_summable_of_mem_ball' y hy)],
  dsimp only,
  conv_lhs {congr, funext, rw [hxy.add_pow' _, finset.smul_sum]},
  refine tsum_congr (λ n, finset.sum_congr rfl $ λ kl hkl, _),
  rw [nsmul_eq_smul_cast 𝕂, smul_smul, smul_mul_smul, ← (finset.nat.mem_antidiagonal.mp hkl),
      nat.cast_add_choose, (finset.nat.mem_antidiagonal.mp hkl)],
  congr' 1,
  have : (n! : 𝕂) ≠ 0 := nat.cast_ne_zero.mpr n.factorial_ne_zero,
  field_simp [this]
end

lemma has_fderiv_at_exp_smul_const_of_mem_ball [char_zero 𝕂] {𝔸' : Type*} [normed_comm_ring 𝔸']
  [normed_algebra 𝕂 𝔸'] [algebra 𝔸' 𝔸] [has_continuous_smul 𝔸' 𝔸] [is_scalar_tower 𝕂 𝔸' 𝔸]
  (x : 𝔸) (t : 𝔸') (htx : t • x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_fderiv_at (λ (u : 𝔸'), exp 𝕂 𝔸 (u • x))
    (exp 𝕂 𝔸 (t • x) • ((1 : 𝔸' →L[𝕂] 𝔸').smul_right x)) t :=
begin
  have hpos : 0 < (exp_series 𝕂 𝔸).radius := (zero_le _).trans_lt htx,
  rw has_fderiv_at_iff_is_o_nhds_zero,
  suffices :
    (λ h, exp 𝕂 𝔸 (t • x) * (exp 𝕂 𝔸 ((0 + h) • x) - exp 𝕂 𝔸 ((0 : 𝔸') • x)
      - ((1 : 𝔸' →L[𝕂] 𝔸').smul_right x) h))
    =ᶠ[𝓝 0] (λ h, exp 𝕂 𝔸 ((t + h) • x) - exp 𝕂 𝔸 (t • x)
      - (exp 𝕂 𝔸 (t • x) • ((1 : 𝔸' →L[𝕂] 𝔸').smul_right x)) h),
  { refine (is_o.const_mul_left _ _).congr' this (eventually_eq.refl _ _),
    rw ← @has_fderiv_at_iff_is_o_nhds_zero _ _ _ _ _ _ _ _
      (λ u, exp 𝕂 𝔸 (u • x)) ((1 : 𝔸' →L[𝕂] 𝔸').smul_right x) 0,
    have : has_fderiv_at (exp 𝕂 𝔸) (1 : 𝔸 →L[𝕂] 𝔸) (((1 : 𝔸' →L[𝕂] 𝔸').smul_right x) 0),
    { rw [continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply, zero_smul],
      exact has_fderiv_at_exp_zero_of_radius_pos hpos },
    exact this.comp 0 ((1 : 𝔸' →L[𝕂] 𝔸').smul_right x).has_fderiv_at },
  have : tendsto (λ h : 𝔸', h • x) (𝓝 0) (𝓝 0),
  { rw ← zero_smul 𝔸' x,
    exact tendsto_id.smul_const x },
  have : ∀ᶠ h in 𝓝 (0 : 𝔸'), h • x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius :=
    this.eventually (emetric.ball_mem_nhds _ hpos),
  filter_upwards [this],
  intros h hh,
  have : commute (t • x) (h • x) := ((commute.refl x).smul_left t).smul_right h,
  rw [add_smul t h, exp_add_of_commute_of_mem_ball this htx hh, zero_add, zero_smul, exp_zero,
      continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply,
      continuous_linear_map.smul_apply, continuous_linear_map.smul_right_apply,
      continuous_linear_map.one_apply, smul_eq_mul, mul_sub_left_distrib, mul_sub_left_distrib,
      mul_one],
end

lemma has_strict_fderiv_at_exp_smul_const_of_mem_ball [char_zero 𝕂] {𝔸' : Type*}
  [normed_comm_ring 𝔸'] [normed_algebra 𝕂 𝔸'] [algebra 𝔸' 𝔸] [has_continuous_smul 𝔸' 𝔸]
  [is_scalar_tower 𝕂 𝔸' 𝔸] (x : 𝔸) (t : 𝔸')
  (htx : t • x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_strict_fderiv_at (λ (u : 𝔸'), exp 𝕂 𝔸 (u • x))
    (exp 𝕂 𝔸 (t • x) • ((1 : 𝔸' →L[𝕂] 𝔸').smul_right x)) t :=
let ⟨p, hp⟩ := analytic_at_exp_of_mem_ball (t • x) htx in
have deriv₁ : has_strict_fderiv_at (λ (u : 𝔸'), exp 𝕂 𝔸 (u • x)) _ t,
  from hp.has_strict_fderiv_at.comp t
    ((continuous_linear_map.id 𝕂 𝔸').smul_right x).has_strict_fderiv_at,
have deriv₂ : has_fderiv_at (λ (u : 𝔸'), exp 𝕂 𝔸 (u • x)) _ t,
  from has_fderiv_at_exp_smul_const_of_mem_ball x t htx,
(deriv₁.has_fderiv_at.unique deriv₂) ▸ deriv₁

lemma has_strict_deriv_at_exp_smul_const_of_mem_ball [char_zero 𝕂] (x : 𝔸) (t : 𝕂)
  (htx : t • x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_strict_deriv_at (λ (u : 𝕂), exp 𝕂 𝔸 (u • x)) (exp 𝕂 𝔸 (t • x) • x) t :=
by simpa using (has_strict_fderiv_at_exp_smul_const_of_mem_ball x t htx).has_strict_deriv_at

lemma has_deriv_at_exp_smul_const_of_mem_ball [char_zero 𝕂] (x : 𝔸) (t : 𝕂)
  (htx : t • x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_deriv_at (λ (u : 𝕂), exp 𝕂 𝔸 (u • x)) (exp 𝕂 𝔸 (t • x) • x) t :=
(has_strict_deriv_at_exp_smul_const_of_mem_ball x t htx).has_deriv_at

lemma exp_mul_exp_neg_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 $ -x) = 1 :=
have hnx : -x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius,
  by rwa ← neg_mem_eball_0_iff at hx,
calc  (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 $ -x)
    = exp 𝕂 𝔸 (x + (-x)) : (exp_add_of_commute_of_mem_ball (commute.refl x).neg_right hx hnx).symm
... = exp 𝕂 𝔸 0 : by rw add_right_neg
... = 1 : exp_zero

lemma exp_neg_mul_exp_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  (exp 𝕂 𝔸 $ -x) * (exp 𝕂 𝔸 x) = 1 :=
begin
  have hnx : -x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius,
  { rwa ← neg_mem_eball_0_iff at hx },
  convert exp_mul_exp_neg_of_mem_ball hnx,
  rw neg_neg
end

noncomputable def exp_emetric_ball_to_units [char_zero 𝕂] (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) : units 𝔸 :=
⟨exp 𝕂 𝔸 x, exp 𝕂 𝔸 (-x), exp_mul_exp_neg_of_mem_ball hx, exp_neg_mul_exp_of_mem_ball hx⟩

lemma is_unit_exp_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  is_unit (exp 𝕂 𝔸 x) :=
⟨exp_emetric_ball_to_units x hx, rfl⟩

lemma exp_conj_of_mem_ball [char_zero 𝕂] (x : 𝔸) (y : units 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  exp 𝕂 𝔸 (y * x * (y⁻¹ : units 𝔸)) = y * (exp 𝕂 𝔸 x) * (y⁻¹ : units 𝔸) :=
begin
  rw [exp_eq_tsum, ← summable.tsum_mul_left (_ : 𝔸) (exp_series_summable_of_mem_ball' x hx),
      ← summable.tsum_mul_right (_ : 𝔸) ((exp_series_summable_of_mem_ball' x hx).mul_left _)],
  refine tsum_congr (λ n, _),
  rw [y.conj_pow, ← smul_mul_assoc, ← mul_smul_comm]
end

end complete_algebra

end any_field_any_algebra

section any_field_comm_algebra

variables {𝕂 𝔸 : Type*} [nondiscrete_normed_field 𝕂] [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [complete_space 𝔸]

/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)` for all `x`, `y` in the disk of convergence. -/
lemma exp_add_of_mem_ball [char_zero 𝕂] {x y : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius)
  (hy : y ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y) :=
exp_add_of_commute_of_mem_ball (commute.all x y) hx hy

/-- The exponential map in a commutative Banach-algebra `𝔸` over a normed field `𝕂` of
characteristic zero has Fréchet-derivative `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x` in the
disk of convergence. -/
lemma has_fderiv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_fderiv_at (exp 𝕂 𝔸) (exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
begin
  -- Note : we could deduce this form `has_fderiv_at_exp_smul_const_of_mem_ball`, but doing the
  -- proof from scratch turns out to be easier, both for us and the elaborator
  have hpos : 0 < (exp_series 𝕂 𝔸).radius := (zero_le _).trans_lt hx,
  rw has_fderiv_at_iff_is_o_nhds_zero,
  suffices : (λ h, exp 𝕂 𝔸 x * (exp 𝕂 𝔸 (0 + h) - exp 𝕂 𝔸 0 - continuous_linear_map.id 𝕂 𝔸 h))
    =ᶠ[𝓝 0] (λ h, exp 𝕂 𝔸 (x + h) - exp 𝕂 𝔸 x - exp 𝕂 𝔸 x • continuous_linear_map.id 𝕂 𝔸 h),
  { refine (is_o.const_mul_left _ _).congr' this (eventually_eq.refl _ _),
    rw ← has_fderiv_at_iff_is_o_nhds_zero,
    exact has_fderiv_at_exp_zero_of_radius_pos hpos },
  have : ∀ᶠ h in 𝓝 (0 : 𝔸), h ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius :=
    emetric.ball_mem_nhds _ hpos,
  filter_upwards [this],
  intros h hh,
  rw [exp_add_of_mem_ball hx hh, exp_zero, zero_add, continuous_linear_map.id_apply, smul_eq_mul],
  ring
end

/-- The exponential map in a commutative Banach-algebra `𝔸` over a normed field `𝕂` of
characteristic zero has strict Fréchet-derivative `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x` in
the disk of convergence. -/
lemma has_strict_fderiv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_strict_fderiv_at (exp 𝕂 𝔸) (exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
let ⟨p, hp⟩ := analytic_at_exp_of_mem_ball x hx in
hp.has_fderiv_at.unique (has_fderiv_at_exp_of_mem_ball hx) ▸ hp.has_strict_fderiv_at

end any_field_comm_algebra

section deriv

variables {𝕂 : Type*} [nondiscrete_normed_field 𝕂] [complete_space 𝕂]

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`exp 𝕂 𝕂 x` at any point `x` in the disk of convergence. -/
lemma has_strict_deriv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝕂}
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) :
  has_strict_deriv_at (exp 𝕂 𝕂) (exp 𝕂 𝕂 x) x :=
by simpa using (has_strict_fderiv_at_exp_of_mem_ball hx).has_strict_deriv_at

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`exp 𝕂 𝕂 x` at any point `x` in the disk of convergence. -/
lemma has_deriv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝕂}
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) :
  has_deriv_at (exp 𝕂 𝕂) (exp 𝕂 𝕂 x) x :=
(has_strict_deriv_at_exp_of_mem_ball hx).has_deriv_at

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_strict_deriv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝕂).radius) :
  has_strict_deriv_at (exp 𝕂 𝕂) 1 0 :=
(has_strict_fderiv_at_exp_zero_of_radius_pos h).has_strict_deriv_at

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_deriv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝕂).radius) :
  has_deriv_at (exp 𝕂 𝕂) 1 0 :=
(has_strict_deriv_at_exp_zero_of_radius_pos h).has_deriv_at

end deriv

section is_R_or_C

section any_algebra

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]

-- This is private because one can use the more general `exp_series_summable_field` intead.
private lemma real.summable_pow_div_factorial (x : ℝ) : summable (λ n : ℕ, x^n / n!) :=
begin
  by_cases h : x = 0,
  { refine summable_of_norm_bounded_eventually 0 summable_zero _,
    filter_upwards [eventually_cofinite_ne 0],
    intros n hn,
    rw [h, zero_pow' n hn, zero_div, norm_zero],
    exact le_refl _ },
  { refine summable_of_ratio_test_tendsto_lt_one zero_lt_one (eventually_of_forall $
      λ n, div_ne_zero (pow_ne_zero n h) (nat.cast_ne_zero.mpr n.factorial_ne_zero)) _,
    suffices : ∀ n : ℕ, ∥x^(n+1) / (n+1)!∥ / ∥x^n / n!∥ = ∥x∥ / ∥((n+1 : ℕ) : ℝ)∥,
    { conv {congr, funext, rw [this, real.norm_coe_nat] },
      exact (tendsto_const_div_at_top_nhds_0_nat _).comp (tendsto_add_at_top_nat 1) },
    intro n,
    calc ∥x^(n+1) / (n+1)!∥ / ∥x^n / n!∥
        = (∥x∥^n * ∥x∥) * (∥(n! : ℝ)∥⁻¹ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * ((∥x∥^n)⁻¹ * ∥(n! : ℝ)∥) :
          by rw [ normed_field.norm_div, normed_field.norm_div,
                  normed_field.norm_pow, normed_field.norm_pow, pow_add, pow_one,
                  div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv', inv_inv',
                  nat.factorial_succ, nat.cast_mul, normed_field.norm_mul, mul_inv_rev' ]
    ... = (∥x∥ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * (∥x∥^n * (∥x∥^n)⁻¹) * (∥(n! : ℝ)∥ * ∥(n! : ℝ)∥⁻¹) :
          by linarith --faster than ac_refl !
    ... = (∥x∥ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * 1 * 1 :
          by  rw [mul_inv_cancel (pow_ne_zero _ $ λ h', h $ norm_eq_zero.mp h'), mul_inv_cancel
                    (λ h', n.factorial_ne_zero $ nat.cast_eq_zero.mp $ norm_eq_zero.mp h')];
              apply_instance
    ... = ∥x∥ / ∥((n+1 : ℕ) : ℝ)∥ : by rw [mul_one, mul_one, ← div_eq_mul_inv] }
end

variables (𝕂 𝔸)

/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
lemma exp_series_radius_eq_top : (exp_series 𝕂 𝔸).radius = ∞ :=
begin
  refine (exp_series 𝕂 𝔸).radius_eq_top_of_summable_norm (λ r, _),
  refine summable_of_norm_bounded_eventually _ (real.summable_pow_div_factorial r) _,
  filter_upwards [eventually_cofinite_ne 0],
  intros n hn,
  rw [norm_mul, norm_norm (exp_series 𝕂 𝔸 n), exp_series, norm_smul, norm_div, norm_one, norm_pow,
      nnreal.norm_eq, norm_eq_abs, abs_cast_nat, mul_comm, ←mul_assoc, ←mul_div_assoc, mul_one],
  have : ∥continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸∥ ≤ 1 :=
    norm_mk_pi_algebra_fin_le_of_pos (nat.pos_of_ne_zero hn),
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n!.cast_nonneg) this
end

lemma exp_series_radius_pos : 0 < (exp_series 𝕂 𝔸).radius :=
begin
  rw exp_series_radius_eq_top,
  exact with_top.zero_lt_top
end

variables {𝕂 𝔸}

section complete_algebra

lemma norm_exp_series_summable (x : 𝔸) : summable (λ n, ∥exp_series 𝕂 𝔸 n (λ _, x)∥) :=
norm_exp_series_summable_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

lemma norm_exp_series_summable' (x : 𝔸) : summable (λ n, ∥(1 / n! : 𝕂) • x^n∥) :=
norm_exp_series_summable_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

lemma norm_exp_series_field_summable (x : 𝕂) : summable (λ n, ∥x^n / n!∥) :=
norm_exp_series_field_summable_of_mem_ball x
  ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

variables [complete_space 𝔸]

lemma exp_series_summable (x : 𝔸) : summable (λ n, exp_series 𝕂 𝔸 n (λ _, x)) :=
summable_of_summable_norm (norm_exp_series_summable x)

lemma exp_series_summable' (x : 𝔸) : summable (λ n, (1 / n! : 𝕂) • x^n) :=
summable_of_summable_norm (norm_exp_series_summable' x)

lemma exp_series_field_summable (x : 𝕂) : summable (λ n, x^n / n!) :=
summable_of_summable_norm (norm_exp_series_field_summable x)

lemma exp_series_has_sum_exp (x : 𝔸) : has_sum (λ n, exp_series 𝕂 𝔸 n (λ _, x)) (exp 𝕂 𝔸 x) :=
exp_series_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

lemma exp_series_has_sum_exp' (x : 𝔸) : has_sum (λ n, (1 / n! : 𝕂) • x^n) (exp 𝕂 𝔸 x):=
exp_series_has_sum_exp_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

lemma exp_series_field_has_sum_exp (x : 𝕂) : has_sum (λ n, x^n / n!) (exp 𝕂 𝕂 x):=
exp_series_field_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

lemma exp_has_fpower_series_on_ball :
  has_fpower_series_on_ball (exp 𝕂 𝔸) (exp_series 𝕂 𝔸) 0 ∞ :=
exp_series_radius_eq_top 𝕂 𝔸 ▸
  has_fpower_series_on_ball_exp_of_radius_pos (exp_series_radius_pos _ _)

lemma exp_has_fpower_series_at_zero :
  has_fpower_series_at (exp 𝕂 𝔸) (exp_series 𝕂 𝔸) 0 :=
exp_has_fpower_series_on_ball.has_fpower_series_at

lemma exp_continuous :
  continuous (exp 𝕂 𝔸) :=
begin
  rw [continuous_iff_continuous_on_univ, ← metric.eball_top_eq_univ (0 : 𝔸),
      ← exp_series_radius_eq_top 𝕂 𝔸],
  exact continuous_on_exp
end

lemma exp_analytic (x : 𝔸) :
  analytic_at 𝕂 (exp 𝕂 𝔸) x :=
analytic_at_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/-- The exponential in a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
lemma has_strict_fderiv_at_exp_zero :
  has_strict_fderiv_at (exp 𝕂 𝔸) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
has_strict_fderiv_at_exp_zero_of_radius_pos (exp_series_radius_pos 𝕂 𝔸)

/-- The exponential in a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
lemma has_fderiv_at_exp_zero :
  has_fderiv_at (exp 𝕂 𝔸) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
has_strict_fderiv_at_exp_zero.has_fderiv_at

end complete_algebra

local attribute [instance] char_zero_R_or_C

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
lemma exp_add_of_commute [complete_space 𝔸]
  {x y : 𝔸} (hxy : commute x y) :
  exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y) :=
exp_add_of_commute_of_mem_ball hxy ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
  ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end any_algebra

section comm_algebra

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

local attribute [instance] char_zero_R_or_C

/-- In a comutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
lemma exp_add {x y : 𝔸} : exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y) :=
exp_add_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
  ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/-- The exponential map in a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict
Fréchet-derivative `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
lemma has_strict_fderiv_at_exp {x : 𝔸} :
  has_strict_fderiv_at (exp 𝕂 𝔸) (exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
has_strict_fderiv_at_exp_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/-- The exponential map in a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has
Fréchet-derivative `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
lemma has_fderiv_at_exp {x : 𝔸} :
  has_fderiv_at (exp 𝕂 𝔸) (exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
has_strict_fderiv_at_exp.has_fderiv_at

end comm_algebra

section deriv

variables {𝕂 : Type*} [is_R_or_C 𝕂]

local attribute [instance] char_zero_R_or_C

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `exp 𝕂 𝕂 x` at any point
`x`. -/
lemma has_strict_deriv_at_exp {x : 𝕂} : has_strict_deriv_at (exp 𝕂 𝕂) (exp 𝕂 𝕂 x) x :=
has_strict_deriv_at_exp_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `exp 𝕂 𝕂 x` at any point `x`. -/
lemma has_deriv_at_exp {x : 𝕂} : has_deriv_at (exp 𝕂 𝕂) (exp 𝕂 𝕂 x) x :=
has_strict_deriv_at_exp.has_deriv_at

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `1` at zero. -/
lemma has_strict_deriv_at_exp_zero : has_strict_deriv_at (exp 𝕂 𝕂) 1 0 :=
has_strict_deriv_at_exp_zero_of_radius_pos (exp_series_radius_pos 𝕂 𝕂)

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `1` at zero. -/
lemma has_deriv_at_exp_zero :
  has_deriv_at (exp 𝕂 𝕂) 1 0 :=
has_strict_deriv_at_exp_zero.has_deriv_at

end deriv

end is_R_or_C

section scalar_tower

variables (𝕂 𝕂' 𝔸 : Type*) [nondiscrete_normed_field 𝕂] [nondiscrete_normed_field 𝕂']
  [normed_ring 𝔸] [normed_algebra 𝕂 𝔸] [normed_algebra 𝕂 𝕂'] [normed_algebra 𝕂' 𝔸]
  [is_scalar_tower 𝕂 𝕂' 𝔸] (p : ℕ) [char_p 𝕂 p]

include p

lemma exp_series_eq_exp_series_of_field_extension (n : ℕ) (x : 𝔸) :
  (exp_series 𝕂 𝔸 n (λ _, x)) = (exp_series 𝕂' 𝔸 n (λ _, x)) :=
begin
  haveI : char_p 𝕂' p := char_p_of_injective_algebra_map (algebra_map 𝕂 𝕂').injective p,
  rw [exp_series, exp_series,
      smul_apply, mk_pi_algebra_fin_apply, list.of_fn_const, list.prod_repeat,
      smul_apply, mk_pi_algebra_fin_apply, list.of_fn_const, list.prod_repeat,
      ←inv_eq_one_div, ←inv_eq_one_div, ← smul_one_smul 𝕂' (_ : 𝕂) (_ : 𝔸)],
  congr,
  symmetry,
  have key : (n! : 𝕂) = 0 ↔ (n! : 𝕂') = 0,
  { rw [char_p.cast_eq_zero_iff 𝕂' p, char_p.cast_eq_zero_iff 𝕂 p] },
  by_cases h : (n! : 𝕂) = 0,
  { have h' : (n! : 𝕂') = 0 := key.mp h,
    field_simp [h, h'] },
  { have h' : (n! : 𝕂') ≠ 0 := λ hyp, h (key.mpr hyp),
    suffices : (n! : 𝕂) • (n!⁻¹ : 𝕂') = (n! : 𝕂) • ((n!⁻¹ : 𝕂) • 1),
    { apply_fun (λ (x : 𝕂'), (n!⁻¹ : 𝕂) • x) at this,
      rwa [inv_smul_smul' h, inv_smul_smul' h] at this },
    rw [← smul_assoc, ← nsmul_eq_smul_cast, nsmul_eq_smul_cast 𝕂' _ (_ : 𝕂')],
    field_simp [h, h'] }
end

/-- Given `𝕂' / 𝕂` a normed field extension (that is, an instance of `normed_algebra 𝕂 𝕂'`) and a
normed algebra `𝔸` over both `𝕂` and `𝕂'` then `exp 𝕂 𝔸 = exp 𝕂' 𝔸`. -/
lemma exp_eq_exp_of_field_extension : exp 𝕂 𝔸 = exp 𝕂' 𝔸 :=
begin
  ext,
  rw [exp, exp],
  refine tsum_congr (λ n, _),
  rw exp_series_eq_exp_series_of_field_extension 𝕂 𝕂' 𝔸 p n x
end

end scalar_tower

section complex

lemma complex.exp_eq_exp_ℂ_ℂ : complex.exp = exp ℂ ℂ :=
begin
  refine funext (λ x, _),
  rw [complex.exp, exp_eq_tsum_field],
  exact tendsto_nhds_unique x.exp'.tendsto_limit
    (exp_series_field_summable x).has_sum.tendsto_sum_nat
end

lemma exp_ℝ_ℂ_eq_exp_ℂ_ℂ : exp ℝ ℂ = exp ℂ ℂ :=
exp_eq_exp_of_field_extension ℝ ℂ ℂ 0

end complex

section real

lemma real.exp_eq_exp_ℝ_ℝ : real.exp = exp ℝ ℝ :=
begin
  refine funext (λ x, _),
  rw [real.exp, complex.exp_eq_exp_ℂ_ℂ, ← exp_ℝ_ℂ_eq_exp_ℂ_ℂ, exp_eq_tsum, exp_eq_tsum_field,
      ← re_to_complex, ← re_clm_apply, re_clm.map_tsum (exp_series_summable' (x : ℂ))],
  refine tsum_congr (λ n, _),
  rw [re_clm.map_smul, ← complex.of_real_pow, re_clm_apply, re_to_complex, complex.of_real_re,
      smul_eq_mul, one_div, mul_comm, div_eq_mul_inv]
end

end real

section wip

section move_me

variables {𝕂 E F G : Type*} [nondiscrete_normed_field 𝕂] [normed_group E] [normed_group F]
  [normed_group G] [normed_space 𝕂 E] [normed_space 𝕂 F] [normed_space 𝕂 G]

lemma has_fderiv_at.apply {f : E → F →L[𝕂] G} {f' : E →L[𝕂] F →L[𝕂] G}
  {x : E → F} {x' : E →L[𝕂] F} (p : E) (hff' : has_fderiv_at f f' p)
  (hxx' : has_fderiv_at x x' p) :
  has_fderiv_at (λ t, (f t) (x t)) ((f p).comp x' + f'.flip (x p)) p :=
(is_bounded_bilinear_map_apply.has_fderiv_at (f p, x p)).comp p (hff'.prod hxx')

lemma has_deriv_at.apply {f : 𝕂 → F →L[𝕂] G} {f' : F →L[𝕂] G} {x : 𝕂 → F} {x' : F} (p : 𝕂)
  (hff' : has_deriv_at f f' p) (hxx' : has_deriv_at x x' p) :
  has_deriv_at (λ t, (f t) (x t)) (f p x' + f' (x p)) p :=
by convert (has_fderiv_at.apply p hff'.has_fderiv_at hxx'.has_fderiv_at).has_deriv_at; simp

end move_me

section move_me2

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]

#check has_deriv_at.smul_const

end move_me2

variables {𝕂 E : Type*} [is_R_or_C 𝕂] [normed_group E] [normed_space 𝕂 E]

local attribute [instance] char_zero_R_or_C

#check continuous_linear_map.to_normed_ring
#check has_deriv_at.scomp


lemma foo [nontrivial E] [complete_space E] (y : 𝕂 → E) (L : E →L[𝕂] E) :
  (∀ t, has_deriv_at y (L $ y t) t) ↔ (y = λ t, (exp 𝕂 _ $ t • L) (y 0)) :=
begin
  split; intro h,
  { let u := λ t, exp 𝕂 _ ((-t) • L) (y t),
    suffices : ∀ t, u t = y 0,
    { ext t,
      rw ← this t,
      dsimp only [u],
      rw [neg_smul, ← continuous_linear_map.mul_apply, exp_mul_exp_neg_of_mem_ball,
          continuous_linear_map.one_apply],
      sorry },
    have : ∀ t, has_deriv_at u 0 t,
    { intro t,
      dsimp only [u],
      have := (has_deriv_at_exp_smul_const_of_mem_ball L (-t) sorry).scomp t (has_deriv_at_neg' t),
      convert has_deriv_at.apply t this (h t),
      rw [smul_eq_mul, continuous_linear_map.smul_apply, continuous_linear_map.mul_apply,
          neg_one_smul, add_neg_self] },
    sorry },
  { rw h,
    intro t, }
end


end wip
