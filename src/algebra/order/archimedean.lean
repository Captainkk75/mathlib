/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.field_power
import data.int.least_greatest
import data.rat.floor

/-!
# Archimedean groups and fields.

This file defines the archimedean property for ordered groups and proves several results connected
to this notion. Being archimedean means that for all elements `x` and `y>0` there exists a natural
number `n` such that `x ≤ n • y`.

## Main definitions

* `archimedean` is a typeclass for an ordered additive commutative monoid to have the archimedean
  property.
* `archimedean.floor_ring` defines a floor function on an archimedean linearly ordered ring making
  it into a `floor_ring`.

## Main statements

* `ℕ`, `ℤ`, and `ℚ` are archimedean.
-/

open int set

variables {α : Type*}

/-- An ordered additive commutative monoid is called `archimedean` if for any two elements `x`, `y`
such that `0 < y` there exists a natural number `n` such that `x ≤ n • y`. -/
class archimedean (α) [ordered_add_comm_monoid α] : Prop :=
(arch : ∀ (x : α) {y}, 0 < y → ∃ n : ℕ, x ≤ n • y)

instance order_dual.archimedean [ordered_add_comm_group α] [archimedean α] : archimedean αᵒᵈ :=
⟨λ x y hy, let ⟨n, hn⟩ := archimedean.arch (-x : α) (neg_pos.2 hy) in
  ⟨n, by rwa [neg_nsmul, neg_le_neg_iff] at hn⟩⟩

section linear_ordered_add_comm_group
variables [linear_ordered_add_comm_group α] [archimedean α]

/-- An archimedean decidable linearly ordered `add_comm_group` has a version of the floor: for
`a > 0`, any `g` in the group lies between some two consecutive multiples of `a`. -/
lemma exists_unique_zsmul_near_of_pos {a : α} (ha : 0 < a) (g : α) :
  ∃! k : ℤ, k • a ≤ g ∧ g < (k + 1) • a :=
begin
  let s : set ℤ := {n : ℤ | n • a ≤ g},
  obtain ⟨k, hk : -g ≤ k • a⟩ := archimedean.arch (-g) ha,
  have h_ne : s.nonempty := ⟨-k, by simpa using neg_le_neg hk⟩,
  obtain ⟨k, hk⟩ := archimedean.arch g ha,
  have h_bdd : ∀ n ∈ s, n ≤ (k : ℤ),
  { assume n hn,
    apply (zsmul_le_zsmul_iff ha).mp,
    rw ← coe_nat_zsmul at hk,
    exact le_trans hn hk },
  obtain ⟨m, hm, hm'⟩ := int.exists_greatest_of_bdd ⟨k, h_bdd⟩ h_ne,
  have hm'' : g < (m + 1) • a,
  { contrapose! hm', exact ⟨m + 1, hm', lt_add_one _⟩, },
  refine ⟨m, ⟨hm, hm''⟩, λ n hn, (hm' n hn.1).antisymm $ int.le_of_lt_add_one _⟩,
  rw ← zsmul_lt_zsmul_iff ha,
  exact lt_of_le_of_lt hm hn.2
end

lemma exists_unique_zsmul_near_of_pos' {a : α} (ha : 0 < a) (g : α) :
  ∃! k : ℤ, 0 ≤ g - k • a ∧ g - k • a < a :=
by simpa only [sub_nonneg, add_zsmul, one_zsmul, sub_lt_iff_lt_add']
  using exists_unique_zsmul_near_of_pos ha g

lemma exists_unique_add_zsmul_mem_Ico {a : α} (ha : 0 < a) (b c : α) :
  ∃! m : ℤ, b + m • a ∈ set.Ico c (c + a) :=
(equiv.neg ℤ).bijective.exists_unique_iff.2 $
  by simpa only [equiv.neg_apply, mem_Ico, neg_zsmul, ← sub_eq_add_neg, le_sub_iff_add_le, zero_add,
    add_comm c, sub_lt_iff_lt_add', add_assoc] using exists_unique_zsmul_near_of_pos' ha (b - c)

lemma exists_unique_add_zsmul_mem_Ioc {a : α} (ha : 0 < a) (b c : α) :
  ∃! m : ℤ, b + m • a ∈ set.Ioc c (c + a) :=
(equiv.add_right (1 : ℤ)).bijective.exists_unique_iff.2 $
  by simpa only [add_zsmul, sub_lt_iff_lt_add', le_sub_iff_add_le', ← add_assoc, and.comm, mem_Ioc,
    equiv.coe_add_right, one_zsmul, add_le_add_iff_right]
    using exists_unique_zsmul_near_of_pos ha (c - b)

end linear_ordered_add_comm_group

theorem exists_nat_gt [ordered_semiring α] [nontrivial α] [archimedean α]
  (x : α) : ∃ n : ℕ, x < n :=
let ⟨n, h⟩ := archimedean.arch x zero_lt_one in
⟨n+1, lt_of_le_of_lt (by rwa ← nsmul_one)
  (nat.cast_lt.2 (nat.lt_succ_self _))⟩

theorem exists_nat_ge [ordered_semiring α] [archimedean α] (x : α) :
  ∃ n : ℕ, x ≤ n :=
begin
  nontriviality α,
  exact (exists_nat_gt x).imp (λ n, le_of_lt)
end

lemma add_one_pow_unbounded_of_pos [ordered_semiring α] [nontrivial α] [archimedean α]
  (x : α) {y : α} (hy : 0 < y) :
  ∃ n : ℕ, x < (y + 1) ^ n :=
have 0 ≤ 1 + y, from add_nonneg zero_le_one hy.le,
let ⟨n, h⟩ := archimedean.arch x hy in
⟨n, calc x ≤ n • y : h
       ... = n * y : nsmul_eq_mul _ _
       ... < 1 + n * y : lt_one_add _
       ... ≤ (1 + y) ^ n : one_add_mul_le_pow' (mul_nonneg hy.le hy.le) (mul_nonneg this this)
                             (add_nonneg zero_le_two hy.le) _
       ... = (y + 1) ^ n : by rw [add_comm]⟩

section ordered_ring
variables [ordered_ring α] [nontrivial α] [archimedean α]

lemma pow_unbounded_of_one_lt (x : α) {y : α} (hy1 : 1 < y) :
  ∃ n : ℕ, x < y ^ n :=
sub_add_cancel y 1 ▸ add_one_pow_unbounded_of_pos _ (sub_pos.2 hy1)

theorem exists_int_gt (x : α) : ∃ n : ℤ, x < n :=
let ⟨n, h⟩ := exists_nat_gt x in ⟨n, by rwa int.cast_coe_nat⟩

theorem exists_int_lt (x : α) : ∃ n : ℤ, (n : α) < x :=
let ⟨n, h⟩ := exists_int_gt (-x) in ⟨-n, by rw int.cast_neg; exact neg_lt.1 h⟩

theorem exists_floor (x : α) :
  ∃ (fl : ℤ), ∀ (z : ℤ), z ≤ fl ↔ (z : α) ≤ x :=
begin
  haveI := classical.prop_decidable,
  have : ∃ (ub : ℤ), (ub:α) ≤ x ∧ ∀ (z : ℤ), (z:α) ≤ x → z ≤ ub :=
  int.exists_greatest_of_bdd
    (let ⟨n, hn⟩ := exists_int_gt x in ⟨n, λ z h',
      int.cast_le.1 $ le_trans h' $ le_of_lt hn⟩)
    (let ⟨n, hn⟩ := exists_int_lt x in ⟨n, le_of_lt hn⟩),
  refine this.imp (λ fl h z, _),
  cases h with h₁ h₂,
  exact ⟨λ h, le_trans (int.cast_le.2 h) h₁, h₂ z⟩,
end

end ordered_ring

section linear_ordered_ring
variables [linear_ordered_ring α] [archimedean α]

/-- Every x greater than or equal to 1 is between two successive
natural-number powers of every y greater than one. -/
lemma exists_nat_pow_near {x : α} {y : α} (hx : 1 ≤ x) (hy : 1 < y) :
  ∃ n : ℕ, y ^ n ≤ x ∧ x < y ^ (n + 1) :=
have h : ∃ n : ℕ, x < y ^ n, from pow_unbounded_of_one_lt _ hy,
by classical; exact let n := nat.find h in
  have hn  : x < y ^ n, from nat.find_spec h,
  have hnp : 0 < n,     from pos_iff_ne_zero.2 (λ hn0,
    by rw [hn0, pow_zero] at hn; exact (not_le_of_gt hn hx)),
  have hnsp : nat.pred n + 1 = n,     from nat.succ_pred_eq_of_pos hnp,
  have hltn : nat.pred n < n,         from nat.pred_lt (ne_of_gt hnp),
  ⟨nat.pred n, le_of_not_lt (nat.find_min h hltn), by rwa hnsp⟩

end linear_ordered_ring

section linear_ordered_field
variables [linear_ordered_field α] [archimedean α] {x y ε : α}

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_mem_Ioc_zpow`,
but with ≤ and < the other way around. -/
lemma exists_mem_Ico_zpow (hx : 0 < x) (hy : 1 < y) : ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) :=
by classical; exact
let ⟨N, hN⟩ := pow_unbounded_of_one_lt x⁻¹ hy in
  have he: ∃ m : ℤ, y ^ m ≤ x, from
    ⟨-N, le_of_lt (by { rw [zpow_neg y (↑N), zpow_coe_nat],
    exact (inv_lt hx (lt_trans (inv_pos.2 hx) hN)).1 hN })⟩,
let ⟨M, hM⟩ := pow_unbounded_of_one_lt x hy in
  have hb: ∃ b : ℤ, ∀ m, y ^ m ≤ x → m ≤ b, from
    ⟨M, λ m hm, le_of_not_lt (λ hlt, not_lt_of_ge
  (zpow_le_of_le hy.le hlt.le)
    (lt_of_le_of_lt hm (by rwa ← zpow_coe_nat at hM)))⟩,
let ⟨n, hn₁, hn₂⟩ := int.exists_greatest_of_bdd hb he in
  ⟨n, hn₁, lt_of_not_ge (λ hge, not_le_of_gt (int.lt_succ _) (hn₂ _ hge))⟩

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_mem_Ico_zpow`,
but with ≤ and < the other way around. -/
lemma exists_mem_Ioc_zpow (hx : 0 < x) (hy : 1 < y) : ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) :=
let ⟨m, hle, hlt⟩ := exists_mem_Ico_zpow (inv_pos.2 hx) hy in
have hyp : 0 < y, from lt_trans zero_lt_one hy,
⟨-(m+1),
by rwa [zpow_neg, inv_lt (zpow_pos_of_pos hyp _) hx],
by rwa [neg_add, neg_add_cancel_right, zpow_neg,
        le_inv hx (zpow_pos_of_pos hyp _)]⟩

/-- For any `y < 1` and any positive `x`, there exists `n : ℕ` with `y ^ n < x`. -/
lemma exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 1) : ∃ n : ℕ, y ^ n < x :=
begin
  by_cases y_pos : y ≤ 0,
  { use 1, simp only [pow_one], linarith, },
  rw [not_le] at y_pos,
  rcases pow_unbounded_of_one_lt (x⁻¹) (one_lt_inv y_pos hy) with ⟨q, hq⟩,
  exact ⟨q, by rwa [inv_pow, inv_lt_inv hx (pow_pos y_pos _)] at hq⟩
end

/-- Given `x` and `y` between `0` and `1`, `x` is between two successive powers of `y`.
This is the same as `exists_nat_pow_near`, but for elements between `0` and `1` -/
lemma exists_nat_pow_near_of_lt_one (xpos : 0 < x) (hx : x ≤ 1) (ypos : 0 < y) (hy : y < 1) :
  ∃ n : ℕ, y ^ (n + 1) < x ∧ x ≤ y ^ n :=
begin
  rcases exists_nat_pow_near (one_le_inv_iff.2 ⟨xpos, hx⟩) (one_lt_inv_iff.2 ⟨ypos, hy⟩)
    with ⟨n, hn, h'n⟩,
  refine ⟨n, _, _⟩,
  { rwa [inv_pow, inv_lt_inv xpos (pow_pos ypos _)] at h'n },
  { rwa [inv_pow, inv_le_inv (pow_pos ypos _) xpos] at hn }
end

lemma exists_rat_gt (x : α) : ∃ q : ℚ, x < q :=
let ⟨n, h⟩ := exists_nat_gt x in ⟨n, by rwa rat.cast_coe_nat⟩

theorem exists_rat_lt (x : α) : ∃ q : ℚ, (q : α) < x :=
let ⟨n, h⟩ := exists_int_lt x in ⟨n, by rwa rat.cast_coe_int⟩

theorem exists_rat_btwn {x y : α} (h : x < y) : ∃ q : ℚ, x < q ∧ (q:α) < y :=
begin
  cases exists_nat_gt (y - x)⁻¹ with n nh,
  cases exists_floor (x * n) with z zh,
  refine ⟨(z + 1 : ℤ) / n, _⟩,
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh,
  have n0 := nat.cast_pos.1 n0',
  rw [rat.cast_div_of_ne_zero, rat.cast_coe_nat, rat.cast_coe_int, div_lt_iff n0'],
  refine ⟨(lt_div_iff n0').2 $
    (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), _⟩,
  rw [int.cast_add, int.cast_one],
  refine lt_of_le_of_lt (add_le_add_right ((zh _).1 le_rfl) _) _,
  rwa [← lt_sub_iff_add_lt', ← sub_mul,
       ← div_lt_iff' (sub_pos.2 h), one_div],
  { rw [rat.coe_int_denom, nat.cast_one], exact one_ne_zero },
  { intro H, rw [rat.coe_nat_num, int.cast_coe_nat, nat.cast_eq_zero] at H, subst H, cases n0 },
  { rw [rat.coe_nat_denom, nat.cast_one], exact one_ne_zero }
end

lemma le_of_forall_rat_lt_imp_le (h : ∀ q : ℚ, (q : α) < x → (q : α) ≤ y) : x ≤ y :=
le_of_not_lt $ λ hyx, let ⟨q, hy, hx⟩ := exists_rat_btwn hyx in hy.not_le $ h _ hx

lemma le_of_forall_lt_rat_imp_le (h : ∀ q : ℚ, y < q → x ≤ q) : x ≤ y :=
le_of_not_lt $ λ hyx, let ⟨q, hy, hx⟩ := exists_rat_btwn hyx in hx.not_le $ h _ hy

lemma eq_of_forall_rat_lt_iff_lt (h : ∀ q : ℚ, (q : α) < x ↔ (q : α) < y) : x = y :=
(le_of_forall_rat_lt_imp_le $ λ q hq, ((h q).1 hq).le).antisymm $ le_of_forall_rat_lt_imp_le $
  λ q hq, ((h q).2 hq).le

lemma eq_of_forall_lt_rat_iff_lt (h : ∀ q : ℚ, x < q ↔ y < q) : x = y :=
(le_of_forall_lt_rat_imp_le $ λ q hq, ((h q).2 hq).le).antisymm $ le_of_forall_lt_rat_imp_le $
  λ q hq, ((h q).1 hq).le

theorem exists_nat_one_div_lt {ε : α} (hε : 0 < ε) : ∃ n : ℕ, 1 / (n + 1: α) < ε :=
begin
  cases exists_nat_gt (1/ε) with n hn,
  use n,
  rw [div_lt_iff, ← div_lt_iff' hε],
  { apply hn.trans,
    simp [zero_lt_one] },
  { exact n.cast_add_one_pos }
end

theorem exists_pos_rat_lt {x : α} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q : α) < x :=
by simpa only [rat.cast_pos] using exists_rat_btwn x0

lemma exists_rat_near (x : α) (ε0 : 0 < ε) : ∃ q : ℚ, |x - q| < ε :=
let ⟨q, h₁, h₂⟩ := exists_rat_btwn $ ((sub_lt_self_iff x).2 ε0).trans ((lt_add_iff_pos_left x).2 ε0)
  in ⟨q, abs_sub_lt_iff.2 ⟨sub_lt.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩

end linear_ordered_field

section linear_ordered_field
variables [linear_ordered_field α]

lemma archimedean_iff_nat_lt : archimedean α ↔ ∀ x : α, ∃ n : ℕ, x < n :=
⟨@exists_nat_gt α _ _, λ H, ⟨λ x y y0,
  (H (x / y)).imp $ λ n h, le_of_lt $
  by rwa [div_lt_iff y0, ← nsmul_eq_mul] at h⟩⟩

lemma archimedean_iff_nat_le : archimedean α ↔ ∀ x : α, ∃ n : ℕ, x ≤ n :=
archimedean_iff_nat_lt.trans
⟨λ H x, (H x).imp $ λ _, le_of_lt,
 λ H x, let ⟨n, h⟩ := H x in ⟨n+1,
   lt_of_le_of_lt h (nat.cast_lt.2 (lt_add_one _))⟩⟩

lemma archimedean_iff_int_lt : archimedean α ↔ ∀ x : α, ∃ n : ℤ, x < n :=
⟨@exists_int_gt α _ _,
begin
  rw archimedean_iff_nat_lt,
  intros h x,
  obtain ⟨n, h⟩ := h x,
  refine ⟨n.to_nat, h.trans_le _⟩,
  exact_mod_cast int.le_to_nat _,
end⟩

lemma archimedean_iff_int_le : archimedean α ↔ ∀ x : α, ∃ n : ℤ, x ≤ n :=
archimedean_iff_int_lt.trans
⟨λ H x, (H x).imp $ λ _, le_of_lt,
 λ H x, let ⟨n, h⟩ := H x in ⟨n+1,
   lt_of_le_of_lt h (int.cast_lt.2 (lt_add_one _))⟩⟩

lemma archimedean_iff_rat_lt : archimedean α ↔ ∀ x : α, ∃ q : ℚ, x < q :=
⟨@exists_rat_gt α _,
  λ H, archimedean_iff_nat_lt.2 $ λ x,
  let ⟨q, h⟩ := H x in
  ⟨⌈q⌉₊, lt_of_lt_of_le h $
    by simpa only [rat.cast_coe_nat] using (@rat.cast_le α _ _ _).2 (nat.le_ceil _)⟩⟩

lemma archimedean_iff_rat_le : archimedean α ↔ ∀ x : α, ∃ q : ℚ, x ≤ q :=
archimedean_iff_rat_lt.trans
⟨λ H x, (H x).imp $ λ _, le_of_lt,
 λ H x, let ⟨n, h⟩ := H x in ⟨n+1,
   lt_of_le_of_lt h (rat.cast_lt.2 (lt_add_one _))⟩⟩

end linear_ordered_field

instance : archimedean ℕ :=
⟨λ n m m0, ⟨n, by simpa only [mul_one, nat.nsmul_eq_mul] using nat.mul_le_mul_left n m0⟩⟩

instance : archimedean ℤ :=
⟨λ n m m0, ⟨n.to_nat, le_trans (int.le_to_nat _) $
by simpa only [nsmul_eq_mul, zero_add, mul_one]
  using mul_le_mul_of_nonneg_left (int.add_one_le_iff.2 m0) (int.coe_zero_le n.to_nat)⟩⟩

instance : archimedean ℚ :=
archimedean_iff_rat_le.2 $ λ q, ⟨q, by rw rat.cast_id⟩

/-- A linear ordered archimedean ring is a floor ring. This is not an `instance` because in some
cases we have a computable `floor` function. -/
noncomputable def archimedean.floor_ring (α) [linear_ordered_ring α] [archimedean α] :
  floor_ring α :=
floor_ring.of_floor α (λ a, classical.some (exists_floor a))
  (λ z a, (classical.some_spec (exists_floor a) z).symm)

/-- A linear ordered field that is a floor ring is archimedean. -/
lemma floor_ring.archimedean (α) [linear_ordered_field α] [floor_ring α] : archimedean α :=
begin
  rw archimedean_iff_int_le,
  exact λ x, ⟨⌈x⌉, int.le_ceil x⟩
end
