/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
import topology.algebra.order.monotone_continuity
import topology.instances.nnreal
import tactic.norm_cast

/-!
# Square root of a real number

In this file we define

* `nnreal.sqrt` to be the square root of a nonnegative real number.
* `real.sqrt` to be the square root of a real number, defined to be zero on negative numbers.

Then we prove some basic properties of these functions.

## Implementation notes

We define `nnreal.sqrt` as the noncomputable inverse to the function `x ↦ x * x`. We use general
theory of inverses of strictly monotone functions to prove that `nnreal.sqrt x` exists. As a side
effect, `nnreal.sqrt` is a bundled `order_iso`, so for `nnreal` numbers we get continuity as well as
theorems like `sqrt x ≤ y ↔ x * x ≤ y` for free.

Then we define `real.sqrt x` to be `nnreal.sqrt (real.to_nnreal x)`. We also define a Cauchy
sequence `real.sqrt_aux (f : cau_seq ℚ abs)` which converges to `sqrt (mk f)` but do not prove (yet)
that this sequence actually converges to `sqrt (mk f)`.

## Tags

square root
-/

open set filter
open_locale filter nnreal topological_space

namespace nnreal

variables {x y : ℝ≥0}

/-- Square root of a nonnegative real number. -/
@[pp_nodot] noncomputable def sqrt : ℝ≥0 ≃o ℝ≥0 :=
order_iso.symm $ strict_mono.order_iso_of_surjective (λ x, x * x)
  (λ x y h, mul_self_lt_mul_self x.2 h) $
  (continuous_id.mul continuous_id).surjective tendsto_mul_self_at_top $
    by simp [order_bot.at_bot_eq]

lemma sqrt_le_sqrt_iff : sqrt x ≤ sqrt y ↔ x ≤ y :=
sqrt.le_iff_le

lemma sqrt_lt_sqrt_iff : sqrt x < sqrt y ↔ x < y :=
sqrt.lt_iff_lt

lemma sqrt_eq_iff_sq_eq : sqrt x = y ↔ y * y = x :=
sqrt.to_equiv.apply_eq_iff_eq_symm_apply.trans eq_comm

lemma sqrt_le_iff : sqrt x ≤ y ↔ x ≤ y * y :=
sqrt.to_galois_connection _ _

lemma le_sqrt_iff : x ≤ sqrt y ↔ x * x ≤ y :=
(sqrt.symm.to_galois_connection _ _).symm

@[simp] lemma sqrt_eq_zero : sqrt x = 0 ↔ x = 0 :=
sqrt_eq_iff_sq_eq.trans $ by rw [eq_comm, zero_mul]

@[simp] lemma sqrt_zero : sqrt 0 = 0 := sqrt_eq_zero.2 rfl

@[simp] lemma sqrt_one : sqrt 1 = 1 := sqrt_eq_iff_sq_eq.2 $ mul_one 1

@[simp] lemma mul_self_sqrt (x : ℝ≥0) : sqrt x * sqrt x = x :=
sqrt.symm_apply_apply x

@[simp] lemma sqrt_mul_self (x : ℝ≥0) : sqrt (x * x) = x := sqrt.apply_symm_apply x

@[simp] lemma sq_sqrt (x : ℝ≥0) : (sqrt x)^2 = x :=
by rw [sq, mul_self_sqrt x]

@[simp] lemma sqrt_sq (x : ℝ≥0) : sqrt (x^2) = x :=
by rw [sq, sqrt_mul_self x]

lemma sqrt_mul (x y : ℝ≥0) : sqrt (x * y) = sqrt x * sqrt y :=
by rw [sqrt_eq_iff_sq_eq, mul_mul_mul_comm, mul_self_sqrt, mul_self_sqrt]

/-- `nnreal.sqrt` as a `monoid_with_zero_hom`. -/
noncomputable def sqrt_hom : ℝ≥0 →*₀ ℝ≥0 := ⟨sqrt, sqrt_zero, sqrt_one, sqrt_mul⟩

lemma sqrt_inv (x : ℝ≥0) : sqrt (x⁻¹) = (sqrt x)⁻¹ := sqrt_hom.map_inv x

lemma sqrt_div (x y : ℝ≥0) : sqrt (x / y) = sqrt x / sqrt y := sqrt_hom.map_div x y

lemma continuous_sqrt : continuous sqrt := sqrt.continuous

end nnreal

namespace real

/-- An auxiliary sequence of rational numbers that converges to `real.sqrt (mk f)`.
This is Heron's method for computing square roots.
Currently this sequence is not used in `mathlib`.  -/
def sqrt_aux (f : cau_seq ℚ abs) : ℕ → ℚ
| 0       := rat.mk_nat (f 0).num.to_nat.sqrt (f 0).denom.sqrt
| (n + 1) := let s := sqrt_aux n in max 0 $ (s + f (n+1) / s) / 2

theorem sqrt_aux_nonneg (f : cau_seq ℚ abs) : ∀ i : ℕ, 0 ≤ sqrt_aux f i
| 0       := by rw [sqrt_aux, rat.mk_nat_eq, rat.mk_eq_div];
  apply div_nonneg; exact int.cast_nonneg.2 (int.of_nat_nonneg _)
| (n + 1) := le_max_left _ _

/-- A simplified version of Cauchy-Schwarz on a two-element set, which we prove separately to
reduce the import graph. -/
theorem rat.cauchy_schwarz (a b : ℚ) : 4 * a * b ≤ (a + b) ^ 2 :=
begin
  suffices pos: 0 ≤ (a + b) ^ 2 - 4 * a * b, exact sub_nonneg.mp pos,
  calc 0 ≤ (a - b) ^ 2 : sq_nonneg (a - b)
    ... = (a + b) ^ 2 - 4 * a * b : by ring,
end

lemma div_mul_eq {a c : ℚ} (c_nonzero : c ≠ 0) : a / c * c = a :=
calc a / c * c = a * c / c : (mul_div_right_comm a c c).symm
  ... = a * (c / c) : (mul_div a c c).symm
  ... = a * 1 : by rw (div_self c_nonzero)
  ... = a : mul_one a

lemma thing3 {a : ℚ} (a_nonzero : a ≠ 0) : a ^ 2 / a = a :=
calc a ^ 2 / a = (a * a) / a : by ring
  ... = a * (a / a) : mul_div_assoc a a a
  ... = a * 1 : by rw (div_self a_nonzero)
  ... = a : mul_one a

theorem ttt (a b : ℚ) (h : 0 ≤ a) (j : a + b ≤ 0) : b ≤ 0 :=
calc b ≤ a + b : le_add_of_nonneg_left h
  ... ≤ 0 : j

theorem fooooo {a b : ℚ} (h1 : 0 < b) (h2 : a ≤ 0) : a * b ≤ 0 :=
begin
  by_cases a = 0,
  { subst h, simp, },
  { have a_neg : a < 0 := (ne.le_iff_lt h).mp h2,
    exact le_of_lt (mul_neg_of_neg_of_pos a_neg h1), },
end

theorem uuu {a b : ℚ} (h : 0 < b) (j : a / b ≤ 0) : a ≤ 0 :=
begin
  calc a = a / b * b : (div_mul_eq (ne_of_gt h)).symm
    ... ≤ 0 : fooooo h j
end

theorem sqrt_aux_overestimate (f : cau_seq ℚ abs) {i : ℕ} (i_pos : 0 < i) :
  f i ≤ (sqrt_aux f i) ^ 2 ∨ sqrt_aux f i = 0 :=
begin
  cases i,
  { linarith, },
  { unfold sqrt_aux,
    simp only [max_eq_left_iff],
    cases lt_or_ge 0 ((sqrt_aux f i + f (i + 1) / sqrt_aux f i) / 2) with r s,
    { left,
      rw max_eq_right_of_lt r,
      simp, norm_num, cancel_denoms,
      by_cases nonzero : sqrt_aux f i = 0,
      { rw nonzero at r, simp at r, cc, },
      { refine (mul_le_mul_right ((sq_pos_iff (sqrt_aux f i)).2 nonzero)).mp _,
        calc 4 * f (i + 1) * sqrt_aux f i ^ 2
              ≤ (f (i + 1) + sqrt_aux f i ^ 2) ^ 2 : rat.cauchy_schwarz _ _
          ... = (sqrt_aux f i ^ 2 + f (i + 1)) ^ 2 : by ring
          ... = (sqrt_aux f i ^ 2 / sqrt_aux f i * sqrt_aux f i + f (i + 1)) ^ 2 : by rw div_mul_eq nonzero
          ... = (sqrt_aux f i ^ 2 / sqrt_aux f i * sqrt_aux f i + f (i + 1) / sqrt_aux f i * sqrt_aux f i) ^ 2 : by rw @div_mul_eq (f (i + 1)) _ nonzero
          ... = (sqrt_aux f i ^ 2 / sqrt_aux f i + f (i + 1) / sqrt_aux f i) ^ 2 * sqrt_aux f i ^ 2 : by ring
          ... = (sqrt_aux f i + f (i + 1) / sqrt_aux f i) ^ 2 * sqrt_aux f i ^ 2 : by rw thing3 nonzero, }, },
    { rw max_eq_left s,
      simp only [zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero, not_false_iff],
      simp only [ge_iff_le] at s,
      cases lt_or_ge 0 (sqrt_aux f i),
      { rw div_le_iff at s,
        { simp at s,
          have u : f (i + 1) / sqrt_aux f i ≤ 0 := ttt (sqrt_aux f i) (f (i + 1) / sqrt_aux f i) _ s,
          { left, exact uuu h u, },
          { exact sqrt_aux_nonneg f i, }, },
        { norm_num, }, },
      { right, exact s, }, }, },
end

lemma blaaaah {a b c : ℚ} (b_pos : 0 < b) (h : a ≤ b * c) : a / b ≤ c :=
begin
  sorry,
end

/-- The sqrt_aux corresponding to decreasing Cauchy sequences is decreasing. -/
theorem sqrt_aux_decreasing (f : cau_seq ℚ abs) (f_decreasing : ∀ i, f (i + 1) ≤ f i)
  {i : ℕ} (i_pos : 0 < i) (all_pos : ∀ j, 0 < sqrt_aux f j) : sqrt_aux f (i + 1) ≤ sqrt_aux f i :=
begin
  unfold sqrt_aux,
  simp,
  cases @sqrt_aux_overestimate f i i_pos,
  { split,
    { exact (le_of_lt (all_pos i)), },
    { cancel_denoms,
      rw two_mul,
      simp,
      refine blaaaah (all_pos i) _,
      calc f (i + 1) ≤ f i : f_decreasing i
        ... ≤ sqrt_aux f i ^ 2 : h
        ... = sqrt_aux f i * sqrt_aux f i : sq _ }, },
  { specialize all_pos i, linarith, },
end

theorem nat_gcd_eq_zero_iff (a b : ℕ) : a.gcd b = 0 ↔ a = 0 ∧ b = 0 :=
begin
  split,
  { intros gcd_eq_zero,
    induction a,
    { simp at gcd_eq_zero,
      exact ⟨rfl, gcd_eq_zero⟩, },
    { exfalso,
      rw nat.gcd_succ at gcd_eq_zero,
      simp at gcd_eq_zero,
      exact gcd_eq_zero, }, },
  { rintros ⟨a_eq_zero, b_eq_zero⟩,
    rw [a_eq_zero, b_eq_zero],
    exact nat.gcd_zero_left _, },
end

/-- If f is positive, then sqrt_aux f is positive. -/
theorem sqrt_aux_pos (f : cau_seq ℚ abs) (all_pos : ∀ j, 0 < f j) (i : ℕ) : 0 < sqrt_aux f i :=
begin
  induction i with i hyp,
  { unfold sqrt_aux,
    specialize all_pos 0,
    rcases f 0,
    intros pos2,
    rw rat.lt_def,
    simp,
    rw rat.lt_def at pos2,
    simp at pos2,
    have sqrt_denom_pos : 0 < nat.sqrt denom := nat.sqrt_pos.mpr pos,
    unfold rat.mk_nat, simp [ne_of_gt sqrt_denom_pos],
    cases num,
    { simp, simp at pos2,
      have sqrt_num_pos : 0 < nat.sqrt num := nat.sqrt_pos.mpr pos2,
      unfold rat.mk_pnat,
      simp,
      norm_cast,
      apply nat.div_pos,
      { exact (nat.sqrt denom).gcd_le_left sqrt_num_pos, },
      { rcases @eq_zero_or_pos _ _ ((nat.sqrt num).gcd (nat.sqrt denom)),
        { rw nat_gcd_eq_zero_iff at h,
          rcases h with ⟨num_zero, denom_zero⟩,
          rw [denom_zero] at sqrt_denom_pos,
          linarith, },
        { assumption, }, }, },
    { simp at pos2, exfalso, exact pos2, }, },
  { unfold sqrt_aux,
    simp,
    specialize all_pos (i + 1),
    cancel_denoms,
    calc 0 < sqrt_aux f i : hyp
      ... < _ : lt_add_of_pos_right (sqrt_aux f i) (div_pos all_pos hyp), },
end

/- TODO(Mario): finish the proof
theorem sqrt_aux_converges (f : cau_seq ℚ abs) : ∃ h x, 0 ≤ x ∧ x * x = max 0 (mk f) ∧
  mk ⟨sqrt_aux f, h⟩ = x :=
begin
  rcases sqrt_exists (le_max_left 0 (mk f)) with ⟨x, x0, hx⟩,
  suffices : ∃ h, mk ⟨sqrt_aux f, h⟩ = x,
  { exact this.imp (λ h e, ⟨x, x0, hx, e⟩) },
  apply of_near,

  suffices : ∃ δ > 0, ∀ i, abs (↑(sqrt_aux f i) - x) < δ / 2 ^ i,
  { rcases this with ⟨δ, δ0, hδ⟩,
    intros }
end -/

/-- The square root of a real number. This returns 0 for negative inputs. -/
@[pp_nodot] noncomputable def sqrt (x : ℝ) : ℝ :=
nnreal.sqrt (real.to_nnreal x)
/-quotient.lift_on x
  (λ f, mk ⟨sqrt_aux f, (sqrt_aux_converges f).fst⟩)
  (λ f g e, begin
    rcases sqrt_aux_converges f with ⟨hf, x, x0, xf, xs⟩,
    rcases sqrt_aux_converges g with ⟨hg, y, y0, yg, ys⟩,
    refine xs.trans (eq.trans _ ys.symm),
    rw [← @mul_self_inj_of_nonneg ℝ _ x y x0 y0, xf, yg],
    congr' 1, exact quotient.sound e
  end)-/

variables {x y : ℝ}

@[simp, norm_cast] lemma coe_sqrt {x : ℝ≥0} : (nnreal.sqrt x : ℝ) = real.sqrt x :=
by rw [real.sqrt, real.to_nnreal_coe]

@[continuity]
lemma continuous_sqrt : continuous sqrt :=
nnreal.continuous_coe.comp $ nnreal.sqrt.continuous.comp continuous_real_to_nnreal

theorem sqrt_eq_zero_of_nonpos (h : x ≤ 0) : sqrt x = 0 :=
by simp [sqrt, real.to_nnreal_eq_zero.2 h]

theorem sqrt_nonneg (x : ℝ) : 0 ≤ sqrt x := nnreal.coe_nonneg _

@[simp] theorem mul_self_sqrt (h : 0 ≤ x) : sqrt x * sqrt x = x :=
by rw [sqrt, ← nnreal.coe_mul, nnreal.mul_self_sqrt, real.coe_to_nnreal _ h]

@[simp] theorem sqrt_mul_self (h : 0 ≤ x) : sqrt (x * x) = x :=
(mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))

theorem sqrt_eq_cases : sqrt x = y ↔ y * y = x ∧ 0 ≤ y ∨ x < 0 ∧ y = 0 :=
begin
  split,
  { rintro rfl,
    cases le_or_lt 0 x with hle hlt,
    { exact or.inl ⟨mul_self_sqrt hle, sqrt_nonneg x⟩ },
    { exact or.inr ⟨hlt, sqrt_eq_zero_of_nonpos hlt.le⟩ } },
  { rintro (⟨rfl, hy⟩|⟨hx, rfl⟩),
    exacts [sqrt_mul_self hy, sqrt_eq_zero_of_nonpos hx.le] }
end

theorem sqrt_eq_iff_mul_self_eq (hx : 0 ≤ x) (hy : 0 ≤ y) :
  sqrt x = y ↔ y * y = x :=
⟨λ h, by rw [← h, mul_self_sqrt hx], λ h, by rw [← h, sqrt_mul_self hy]⟩

theorem sqrt_eq_iff_mul_self_eq_of_pos (h : 0 < y) :
  sqrt x = y ↔ y * y = x :=
by simp [sqrt_eq_cases, h.ne', h.le]

@[simp] lemma sqrt_eq_one : sqrt x = 1 ↔ x = 1 :=
calc sqrt x = 1 ↔ 1 * 1 = x :
  sqrt_eq_iff_mul_self_eq_of_pos zero_lt_one
... ↔ x = 1 : by rw [eq_comm, mul_one]

@[simp] theorem sq_sqrt (h : 0 ≤ x) : (sqrt x)^2 = x :=
by rw [sq, mul_self_sqrt h]

@[simp] theorem sqrt_sq (h : 0 ≤ x) : sqrt (x ^ 2) = x :=
by rw [sq, sqrt_mul_self h]

theorem sqrt_eq_iff_sq_eq (hx : 0 ≤ x) (hy : 0 ≤ y) :
  sqrt x = y ↔ y ^ 2 = x :=
by rw [sq, sqrt_eq_iff_mul_self_eq hx hy]

theorem sqrt_mul_self_eq_abs (x : ℝ) : sqrt (x * x) = |x| :=
by rw [← abs_mul_abs_self x, sqrt_mul_self (abs_nonneg _)]

theorem sqrt_sq_eq_abs (x : ℝ) : sqrt (x ^ 2) = |x| :=
by rw [sq, sqrt_mul_self_eq_abs]

@[simp] theorem sqrt_zero : sqrt 0 = 0 := by simp [sqrt]

@[simp] theorem sqrt_one : sqrt 1 = 1 := by simp [sqrt]

@[simp] theorem sqrt_le_sqrt_iff (hy : 0 ≤ y) : sqrt x ≤ sqrt y ↔ x ≤ y :=
by rw [sqrt, sqrt, nnreal.coe_le_coe, nnreal.sqrt_le_sqrt_iff, real.to_nnreal_le_to_nnreal_iff hy]

@[simp] theorem sqrt_lt_sqrt_iff (hx : 0 ≤ x) : sqrt x < sqrt y ↔ x < y :=
lt_iff_lt_of_le_iff_le (sqrt_le_sqrt_iff hx)

theorem sqrt_lt_sqrt_iff_of_pos (hy : 0 < y) : sqrt x < sqrt y ↔ x < y :=
by rw [sqrt, sqrt, nnreal.coe_lt_coe, nnreal.sqrt_lt_sqrt_iff, to_nnreal_lt_to_nnreal_iff hy]

theorem sqrt_le_sqrt (h : x ≤ y) : sqrt x ≤ sqrt y :=
by { rw [sqrt, sqrt, nnreal.coe_le_coe, nnreal.sqrt_le_sqrt_iff], exact to_nnreal_le_to_nnreal h }

theorem sqrt_lt_sqrt (hx : 0 ≤ x) (h : x < y) : sqrt x < sqrt y :=
(sqrt_lt_sqrt_iff hx).2 h

theorem sqrt_le_left (hy : 0 ≤ y) : sqrt x ≤ y ↔ x ≤ y ^ 2 :=
by rw [sqrt, ← real.le_to_nnreal_iff_coe_le hy, nnreal.sqrt_le_iff, ← real.to_nnreal_mul hy,
  real.to_nnreal_le_to_nnreal_iff (mul_self_nonneg y), sq]

theorem sqrt_le_iff : sqrt x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2 :=
begin
  rw [← and_iff_right_of_imp (λ h, (sqrt_nonneg x).trans h), and.congr_right_iff],
  exact sqrt_le_left
end

/- note: if you want to conclude `x ≤ sqrt y`, then use `le_sqrt_of_sq_le`.
   if you have `x > 0`, consider using `le_sqrt'` -/
theorem le_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
by rw [mul_self_le_mul_self_iff hx (sqrt_nonneg _), sq, mul_self_sqrt hy]

theorem le_sqrt' (hx : 0 < x) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
by { rw [sqrt, ← nnreal.coe_mk x hx.le, nnreal.coe_le_coe, nnreal.le_sqrt_iff,
  real.le_to_nnreal_iff_coe_le', sq, nnreal.coe_mul], exact mul_pos hx hx }

theorem abs_le_sqrt (h : x^2 ≤ y) : |x| ≤ sqrt y :=
by rw ← sqrt_sq_eq_abs; exact sqrt_le_sqrt h

theorem sq_le (h : 0 ≤ y) : x^2 ≤ y ↔ -sqrt y ≤ x ∧ x ≤ sqrt y :=
begin
  split,
  { simpa only [abs_le] using abs_le_sqrt },
  { rw [← abs_le, ← sq_abs],
    exact (le_sqrt (abs_nonneg x) h).mp },
end

theorem neg_sqrt_le_of_sq_le (h : x^2 ≤ y) : -sqrt y ≤ x :=
((sq_le ((sq_nonneg x).trans h)).mp h).1

theorem le_sqrt_of_sq_le (h : x^2 ≤ y) : x ≤ sqrt y :=
((sq_le ((sq_nonneg x).trans h)).mp h).2

@[simp] theorem sqrt_inj (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = sqrt y ↔ x = y :=
by simp [le_antisymm_iff, hx, hy]

@[simp] theorem sqrt_eq_zero (h : 0 ≤ x) : sqrt x = 0 ↔ x = 0 :=
by simpa using sqrt_inj h le_rfl

theorem sqrt_eq_zero' : sqrt x = 0 ↔ x ≤ 0 :=
by rw [sqrt, nnreal.coe_eq_zero, nnreal.sqrt_eq_zero, real.to_nnreal_eq_zero]

theorem sqrt_ne_zero (h : 0 ≤ x) : sqrt x ≠ 0 ↔ x ≠ 0 :=
by rw [not_iff_not, sqrt_eq_zero h]

theorem sqrt_ne_zero' : sqrt x ≠ 0 ↔ 0 < x :=
by rw [← not_le, not_iff_not, sqrt_eq_zero']

@[simp] theorem sqrt_pos : 0 < sqrt x ↔ 0 < x :=
lt_iff_lt_of_le_iff_le (iff.trans
  (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')

@[simp] theorem sqrt_mul (hx : 0 ≤ x) (y : ℝ) : sqrt (x * y) = sqrt x * sqrt y :=
by simp_rw [sqrt, ← nnreal.coe_mul, nnreal.coe_eq, real.to_nnreal_mul hx, nnreal.sqrt_mul]

@[simp] theorem sqrt_mul' (x) {y : ℝ} (hy : 0 ≤ y) : sqrt (x * y) = sqrt x * sqrt y :=
by rw [mul_comm, sqrt_mul hy, mul_comm]

@[simp] theorem sqrt_inv (x : ℝ) : sqrt x⁻¹ = (sqrt x)⁻¹ :=
by rw [sqrt, real.to_nnreal_inv, nnreal.sqrt_inv, nnreal.coe_inv, sqrt]

@[simp] theorem sqrt_div (hx : 0 ≤ x) (y : ℝ) : sqrt (x / y) = sqrt x / sqrt y :=
by rw [division_def, sqrt_mul hx, sqrt_inv, division_def]

@[simp] theorem div_sqrt : x / sqrt x = sqrt x :=
begin
  cases le_or_lt x 0,
  { rw [sqrt_eq_zero'.mpr h, div_zero] },
  { rw [div_eq_iff (sqrt_ne_zero'.mpr h), mul_self_sqrt h.le] },
end

theorem sqrt_div_self' : sqrt x / x = 1 / sqrt x :=
by rw [←div_sqrt, one_div_div, div_sqrt]

theorem sqrt_div_self : sqrt x / x = (sqrt x)⁻¹ :=
by rw [sqrt_div_self', one_div]

theorem lt_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x < sqrt y ↔ x ^ 2 < y :=
by rw [mul_self_lt_mul_self_iff hx (sqrt_nonneg y), sq, mul_self_sqrt hy]

theorem sq_lt : x^2 < y ↔ -sqrt y < x ∧ x < sqrt y :=
begin
  split,
  { simpa only [← sqrt_lt_sqrt_iff (sq_nonneg x), sqrt_sq_eq_abs] using abs_lt.mp },
  { rw [← abs_lt, ← sq_abs],
    exact λ h, (lt_sqrt (abs_nonneg x) (sqrt_pos.mp (lt_of_le_of_lt (abs_nonneg x) h)).le).mp h },
end

theorem neg_sqrt_lt_of_sq_lt (h : x^2 < y) : -sqrt y < x := (sq_lt.mp h).1

theorem lt_sqrt_of_sq_lt (h : x^2 < y) : x < sqrt y := (sq_lt.mp h).2

/-- The natural square root is at most the real square root -/
lemma nat_sqrt_le_real_sqrt {a : ℕ} : ↑(nat.sqrt a) ≤ real.sqrt ↑a :=
begin
  rw real.le_sqrt (nat.cast_nonneg _) (nat.cast_nonneg _),
  norm_cast,
  exact nat.sqrt_le' a,
end

/-- The real square root is at most the natural square root plus one -/
lemma real_sqrt_le_nat_sqrt_succ {a : ℕ} : real.sqrt ↑a ≤ nat.sqrt a + 1 :=
begin
  rw real.sqrt_le_iff,
  split,
  { norm_cast, simp, },
  { norm_cast, exact le_of_lt (nat.lt_succ_sqrt' a), },
end

instance : star_ordered_ring ℝ :=
{ nonneg_iff := λ r, by
  { refine ⟨λ hr, ⟨sqrt r, show r = sqrt r * sqrt r, by rw [←sqrt_mul hr, sqrt_mul_self hr]⟩, _⟩,
    rintros ⟨s, rfl⟩,
    exact mul_self_nonneg s },
  ..real.ordered_add_comm_group }

end real

open real

variables {α : Type*}

lemma filter.tendsto.sqrt {f : α → ℝ} {l : filter α} {x : ℝ} (h : tendsto f l (𝓝 x)) :
  tendsto (λ x, sqrt (f x)) l (𝓝 (sqrt x)) :=
(continuous_sqrt.tendsto _).comp h

variables [topological_space α] {f : α → ℝ} {s : set α} {x : α}

lemma continuous_within_at.sqrt (h : continuous_within_at f s x) :
  continuous_within_at (λ x, sqrt (f x)) s x :=
h.sqrt

lemma continuous_at.sqrt (h : continuous_at f x) : continuous_at (λ x, sqrt (f x)) x := h.sqrt

lemma continuous_on.sqrt (h : continuous_on f s) : continuous_on (λ x, sqrt (f x)) s :=
λ x hx, (h x hx).sqrt

@[continuity]
lemma continuous.sqrt (h : continuous f) : continuous (λ x, sqrt (f x)) := continuous_sqrt.comp h
