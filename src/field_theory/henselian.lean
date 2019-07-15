/-
Copyright (c) 2019 Casper Putz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sander Dahmen, Casper Putz
-/

import algebra data.real.basic data.polynomial data.finset ring_theory.integral_closure

universe u

namespace valuation

/-- A *valued ring* is an integral domain `α` together with a valuation `val : α → ℝ`,
which is positive definite, multiplicative, and satisfies the (weak) triangle inequality. -/
class valued_ring (α : Type u) [integral_domain α] :=
(val : α → ℝ)
(non_neg : ∀ a, val a ≥ 0)
(definite : ∀ a, val a = 0 ↔ a = 0)
(val_mul : ∀ a b, val (a * b) = val a * val b)
(val_add : ∀ a b, val (a + b) ≤ val a + val b)

/-- A *nonarchimedian valued ring* is a valued ring satisfying the strong (i.e nonarchimedian)
triangle inequality. -/
class nonarch_valued_ring (α : Type u) [integral_domain α] extends valued_ring α :=
(nonarch : ∀ a b, val (a + b) ≤ max (val a) (val b))

section valued_ring

open valued_ring

variables {α : Type u} [integral_domain α] [valued_ring α]

/-- Shows that the valuation of a nonzero element is nonzero. -/
lemma val_ne_zero {x : α} (h : x ≠ 0) : val x ≠ 0 := (mt (definite x).mp) h

/-- Shows that the valuation of a nonzero element is > 0. -/
lemma val_pos {x : α} (h : x ≠ 0) : val x > 0 := lt_of_le_of_ne (non_neg x) (ne.symm $ val_ne_zero h)

/-- Shows that the valuation of 0 equals 0. -/
lemma val_zero : val (0 : α) = 0 := by rw [definite]

/-- Shows that the valuation of 1 equals 1. -/
lemma val_one : val (1 : α) = 1 :=
have h : val (1 : α) * val (1 : α) = val (1 : α), by rw[←val_mul, mul_one],
(domain.mul_left_inj (val_ne_zero (one_ne_zero : (1 : α) ≠ 0))).mp (by rw [h, mul_one])

/-- Shows that the valuation of -1 equals -1. -/
lemma val_neg_one : val (-1 : α) = 1 :=
have val (-1 : α) * val (-1 : α) = 1, by rw[←val_mul, neg_one_mul, neg_neg, val_one],
or.resolve_right
  ((mul_self_eq_one_iff _).mp this)
  (ne_of_gt (lt_of_lt_of_le zero_gt_neg_one (non_neg (-1 : α))))

/-- Shows that the valuation of -x equals x. -/
lemma val_neg (x : α) : val (-x) = val x := by rw[←mul_neg_one, val_mul, val_neg_one, mul_one]

/-- Shows that the valuation of x^n equals the n-th power of the valuation of x. -/
lemma val_pow (x : α) (n : ℕ) : val (x^n) = (val x)^n :=
begin
  induction n,
  { rw [pow_zero, pow_zero, val_one] },
  { rw [pow_succ, pow_succ, val_mul, n_ih] }
end

end valued_ring

section nonarch_valued_ring

open valued_ring nonarch_valued_ring

variables {α : Type u} [integral_domain α] [nonarch_valued_ring α]

lemma val_sum (s : multiset α) (b : ℝ) (hb : b ≥ 0) : (∀ x ∈ s, val x ≤ b) → val (multiset.sum s) ≤ b :=
multiset.induction_on s
  (λ _, by rw[multiset.sum_zero, val_zero]; exact hb)
  (assume x s h hs,
  have hbx : val x ≤ b, from hs x (multiset.mem_cons_self x s),
  have hbs : ∀ y ∈ s, val y ≤ b, from λ y hy, hs y (multiset.mem_cons_of_mem hy),
  calc val (multiset.sum (x :: s)) ≤ val (x + multiset.sum s)           : by rw [multiset.sum_cons]
                               ... ≤ max (val x) (val (multiset.sum s)) : nonarch x _
                               ... ≤ b                                  : max_le hbx (h hbs))

end nonarch_valued_ring

/-- The *valuation ring* of a nonarchimedien valued field is the subring of all
elements of valuation ≤ 1. -/
def valuation_ring (α : Type u) [discrete_field α] [nonarch_valued_ring α] :=
    {x : α // valued_ring.val x ≤ 1}

section valuation_ring

variables {α : Type u} [discrete_field α] [nonarch_valued_ring α]

/-- The addition on a valuation ring. -/
def add : valuation_ring α → valuation_ring α → valuation_ring α
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x+y,
    le_trans (nonarch_valued_ring.nonarch _ _) (max_le_iff.2 ⟨hx,hy⟩)⟩

/-- The multiplication on a valuation ring. -/
def mul : valuation_ring α → valuation_ring α → valuation_ring α
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x*y,
    begin rw valued_ring.val_mul, apply mul_le_one; {assumption <|> apply valued_ring.non_neg} end⟩

/-- The subtraction on a valuation ring. -/
def neg : valuation_ring α → valuation_ring α
| ⟨x, hx⟩ := ⟨-x, by rw[val_neg]; exact hx⟩

/-- The valuation ring is indeed a ring. -/
instance : ring (valuation_ring α) :=
begin
  refine { add := add,
           mul := mul,
           neg := neg,
           zero := ⟨0,
           begin
             rw [(valued_ring.definite (0:α)).2 rfl], exact zero_le_one,
           end
        ⟩,
           one := ⟨1, by rw[val_one]⟩,
           .. };
  {repeat {rintro ⟨_, _⟩}, simp [mul_assoc, left_distrib, right_distrib, add, mul, neg]}
end

lemma zero_def : ∀ x : valuation_ring α, x = 0 ↔ x.val = 0
| ⟨x, _⟩ := ⟨subtype.mk.inj, λ h, by simp at h; simp only [h]; refl⟩

@[simp] lemma add_def : ∀ (x y : valuation_ring α), (x+y).val = x.val + y.val
| ⟨x, hx⟩ ⟨y, hy⟩ := rfl

@[simp] lemma mul_def : ∀ (x y : valuation_ring α), (x*y).val = x.val * y.val
| ⟨x, hx⟩ ⟨y, hy⟩ := rfl

@[simp] lemma mk_zero {h} : (⟨0, h⟩ : valuation_ring α) = (0 : valuation_ring α) := rfl

-- There is a coercion from the valuation ring of α to α; these lemmas below prove that the
-- coercion has some natural properties.
instance : has_coe (valuation_ring α) α := ⟨subtype.val⟩

@[simp] lemma val_eq_coe (z : valuation_ring α) : z.val = ↑z := rfl

@[simp, move_cast] lemma coe_add : ∀ (z1 z2 : valuation_ring α), (↑(z1 + z2) : α) = ↑z1 + ↑z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, move_cast] lemma coe_mul : ∀ (z1 z2 : valuation_ring α), (↑(z1 * z2) : α) = ↑z1 * ↑z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, move_cast] lemma coe_neg : ∀ (z1 : valuation_ring α), (↑(-z1) : α) = -↑z1
| ⟨_, _⟩ := rfl

@[simp, move_cast] lemma coe_sub : ∀ (z1 z2 : valuation_ring α), (↑(z1 - z2) : α) = ↑z1 - ↑z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, squash_cast] lemma coe_one : (↑(1 : valuation_ring α) : α) = 1 := rfl

@[simp, squash_cast] lemma coe_coe : ∀ n : ℕ, (↑(↑n : valuation_ring α) : α) = (↑n : α)
| 0 := rfl
| (k+1) := by simp [coe_coe]

@[simp, squash_cast] lemma coe_zero : (↑(0 : valuation_ring α) : α) = 0 := rfl

@[simp, move_cast] lemma cast_pow (x : valuation_ring α) : ∀ (n : ℕ), (↑(x^n) : α) = (↑x : α)^n
| 0 := by simp
| (k+1) := by simp [monoid.pow, pow]; congr; apply cast_pow

lemma mk_coe : ∀ (k : valuation_ring α), (⟨↑k, k.2⟩ : valuation_ring α) = k
| ⟨_, _⟩ := rfl

/-- Shows that the multiplication on the valuation ring is commutative -/
protected lemma vmul_comm : ∀ x y : valuation_ring α, x * y = y * x
| ⟨q1, h1⟩ ⟨q2, h2⟩ := show (⟨q1*q2, _⟩ : valuation_ring α) = ⟨q2*q1, _⟩,
  by simp[mul_comm]

/-- The valuation ring is a commutative ring -/
instance : comm_ring (valuation_ring α) :=
{ mul_comm := valuation.vmul_comm,
  ..valuation.ring }

/-- The valuation ring is an integral domain-/
instance : integral_domain (valuation_ring α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
    λ a b, begin
      repeat {rw[subtype.ext, val_eq_coe, val_eq_coe]},
      rw[coe_mul];
      exact eq_zero_or_eq_zero_of_mul_eq_zero
    end,
  zero_ne_one := by simp[subtype.ext]; exact zero_ne_one,
  ..valuation.comm_ring }

/-- The valuation ring is itself a valued ring -/
instance : nonarch_valued_ring (valuation_ring α) :=
{ val := λ x, valued_ring.val (x : α),
  non_neg := λ x, valued_ring.non_neg x,
  definite := λ x, by rw[subtype.ext]; simp; exact valued_ring.definite x,
  val_mul := λ x y, by rw[coe_mul]; exact valued_ring.val_mul x y,
  val_add := λ x y, by rw[coe_add]; exact valued_ring.val_add x y,
  nonarch := λ x y, by simp only [val_eq_coe, coe_add]; exact nonarch_valued_ring.nonarch x y }

/-- Shows that the valuation of the inverse is the inverse of the valuation. -/
lemma val_inv (x : α) (h : x ≠ 0) : valued_ring.val x⁻¹ = (valued_ring.val x)⁻¹ :=
begin
  apply eq_of_mul_eq_mul_right (val_ne_zero h),
  rw [inv_mul_cancel (val_ne_zero h), ←valued_ring.val_mul, inv_mul_cancel h, val_one]
end

/-- Shows that for x in a valued field, either x or x⁻¹ is in the valuation ring. -/
lemma mem_or_inv_mem (x : α) (h : x ≠ 0) : valued_ring.val x ≤ 1 ∨ valued_ring.val x⁻¹ ≤ 1 :=
suffices valued_ring.val x ≤ 1 ∨ valued_ring.val x⁻¹ < 1, from
  or.elim this (λ hr, or.inl hr) (λ hl, or.inr (le_of_lt hl)),
begin
  rw [val_inv x h, inv_lt (val_pos h) zero_lt_one, inv_one],
  exact le_or_gt _ _
end

instance coe_is_ring_hom : @is_ring_hom _ _ (show ring (valuation_ring α), by apply_instance) _
	(subtype.val : valuation_ring α → α) :=
{ map_one := by rw[val_eq_coe, coe_one],
	map_mul := λ x y, by simp only [val_eq_coe, coe_mul, val_eq_coe],
	map_add := λ x y, by simp only [val_eq_coe, coe_add, val_eq_coe] }

open polynomial

instance : algebra (valuation_ring α) α :=
	algebra.of_ring_hom (subtype.val) valuation.coe_is_ring_hom

lemma integrally_closed (x : α) (hi : is_integral (valuation_ring α) x) :
	valued_ring.val x ≤ 1 :=
let ⟨p, hm, hp⟩ := hi in
begin
	by_contradiction hnx,
  change p.eval₂ subtype.val x = 0 at hp,
  let X : polynomial (valuation_ring α):= X,
  have h : valued_ring.val (x^p.nat_degree) =
           valued_ring.val ((X^p.nat_degree + -p).eval₂ subtype.val x), from
    congr_arg _ (by rw[eval₂_add, eval₂_neg, hp, neg_zero, add_zero, eval₂_X_pow]),
  rw [val_pow] at h,
  have hn0 : p ≠ 0, from ne_zero_of_monic hm,
  have h1 : valued_ring.val x ^ p.nat_degree ≤ valued_ring.val x ^ (p.nat_degree - 1),
    begin
      rw [h],
      apply val_sum,
      { cases nat.eq_zero_or_pos (nat_degree p - 1) with h0 h1,
        { rw [h0, pow_zero], exact zero_le_one },
        { rw [←zero_pow h1],
          exact pow_le_pow_of_le_left (le_refl _) (valued_ring.non_neg x) _ } },
      { intros y hy,
        rw [multiset.mem_map] at hy,
        cases hy with a ha,
        have hd : a ≤ p.nat_degree - 1,
          begin
            rw [←finset.mem_def] at ha,
            have ha1 : a ∈ (X ^ nat_degree p + -p).support, from ha.1,
            have hna : a ≠ p.nat_degree, from λ hna,
              begin rw [finsupp.mem_support_iff, hna] at ha1,
                change coeff (X ^ nat_degree p + -p) (nat_degree p) ≠ 0 at ha1,
                rw [monic.def] at hm,
                unfold leading_coeff at hm,
                rw [coeff_add, coeff_neg, coeff_X_pow, if_pos, hm, add_neg_self] at ha1,
                exact ha1 rfl,
                refl,
              end,
            have hm1 : a ∈ (X ^ nat_degree p).support ∪ (-p).support, from finset.mem_of_subset finsupp.support_add ha1,
            have hm2 : (X ^ nat_degree p).support = finset.singleton (nat_degree p),
              by rw [←one_mul (X^_), ←C_1, ←single_eq_C_mul_X, finsupp.support_single_ne_zero (one_ne_zero)]; refl,
            have hm3 : (X ^ nat_degree p).support ⊆ (-p).support,
            begin
              rw [finsupp.support_neg, hm2, finset.subset_iff],
              intros x hx,
              rw [finset.mem_singleton] at hx,
              rw [hx, finsupp.mem_support_iff],
              change leading_coeff p ≠ 0,
              rw [monic.def.mp hm],
              exact one_ne_zero
            end,
            have : a ∈ p.support,
            begin
              rw [←finsupp.support_neg],
              exact finset.mem_of_subset (finset.union_subset hm3 (finset.subset.refl _)) hm1
            end,
            have : a ≤ p.nat_degree, from
            begin
              rw [←with_bot.coe_le_coe, ←degree_eq_nat_degree hn0],
              exact finset.le_sup this
            end,
            exact nat.le_pred_of_lt (lt_of_le_of_ne this hna)
          end,
        rw [←ha.2, valued_ring.val_mul],
        exact calc valued_ring.val (((X ^ nat_degree p - p).to_fun a).val) * valued_ring.val (x ^ a)
              ≤ valued_ring.val (x ^ a) :
                  mul_le_of_le_one_left (valued_ring.non_neg _) (((X ^ nat_degree p - p).to_fun a).property)
          ... ≤ valued_ring.val x ^ (p.nat_degree - 1) :
                  by rw [val_pow]; exact pow_le_pow (le_of_not_ge hnx) hd }
    end,
  have h0 : 0 < nat_degree p, from
    suffices ↑0 < degree p, by rwa [degree_eq_nat_degree hn0, with_bot.coe_lt_coe] at this,
    (lt_of_not_ge $ λ hlt, begin
      have := eq_C_of_degree_le_zero hlt,
      rw [this, eval₂_C, ←zero_def] at hp,
      exact hn0 (finsupp.ext (λ n, show coeff p n = 0, from
        nat.cases_on n hp (λ _, coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hlt
          (with_bot.coe_lt_coe.2 (nat.succ_pos _))))))
    end),
  have hx : 0 < valued_ring.val x,
    from val_pos (λ hn, by by_contradiction; rw [hn, val_zero] at hnx; exact hnx zero_le_one),
  rw [←mul_le_mul_right hx, ←pow_succ' _ (_ - 1)] at h1,
  change valued_ring.val x ^ p.nat_degree * valued_ring.val x ≤
         valued_ring.val x ^ (nat.succ (nat.pred p.nat_degree)) at h1,
  rw [nat.succ_pred_eq_of_pos h0] at h1,
  have : valued_ring.val x ^ nat_degree p > 0,
    by rw [←zero_pow h0]; exact pow_lt_pow_of_lt_left hx (le_refl 0) h0,
  rw [mul_le_iff_le_one_right this] at h1,
  contradiction
end

end valuation_ring

end valuation

namespace henselian

open valuation polynomial

/-- A *henselian field* is a valued field `α` such that any irreducible polyomial
over this field . -/
class henselian_field (α : Type u) [discrete_field α] [valued_ring α] :=
(henselian : ∀ p : polynomial α, irreducible p →
  ∀ k ≤ nat_degree p, valued_ring.val (p.coeff k) ≤ max (valued_ring.val (p.coeff 0)) (valued_ring.val (p.leading_coeff)))

variables {α : Type u} [discrete_field α] [nonarch_valued_ring α] [henselian_field α]

lemma integral_coeffs (p : polynomial α) (hp : irreducible p) (hm : monic p)
  (h0 : valued_ring.val (p.coeff 0) ≤ 1) : ∀ n, valued_ring.val (p.coeff n) ≤ 1 :=
λ k, or.elim (le_or_gt ↑k (degree p))
	(λ hk, begin
		rw[degree_eq_nat_degree (ne_zero_of_irreducible hp), with_bot.coe_le_coe] at hk,
		have h : valued_ring.val (p.coeff k) ≤
			max (valued_ring.val (p.coeff 0)) (valued_ring.val (p.leading_coeff)),
			from henselian_field.henselian p hp k hk,
		rwa [monic.def.mp hm, val_one, max_eq_right h0] at h
	end)
	(λ hk, by	rw [coeff_eq_zero_of_degree_lt hk, val_zero]; exact zero_le_one)


end henselian
