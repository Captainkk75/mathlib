/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import algebra.big_operators.finsupp
import data.finsupp.multiset
import data.nat.prime
import number_theory.padics.padic_val
import data.nat.interval

/-!
# Prime factorizations

 `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`.  For example, since 2000 = 2^4 * 5^3,
  * `factorization 2000 2` is 4
  * `factorization 2000 5` is 3
  * `factorization 2000 k` is 0 for all other `k : ℕ`.

## TODO

* As discussed in this Zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/217875/topic/Multiplicity.20in.20the.20naturals
We have lots of disparate ways of talking about the multiplicity of a prime
in a natural number, including `factors.count`, `padic_val_nat`, `multiplicity`,
and the material in `data/pnat/factors`.  Move some of this material to this file,
prove results about the relationships between these definitions,
and (where appropriate) choose a uniform canonical way of expressing these ideas.

* Moreover, the results here should be generalised to an arbitrary unique factorization monoid
with a normalization function, and then deduplicated.  The basics of this have been started in
`ring_theory/unique_factorization_domain`.

* Extend the inductions to any `normalization_monoid` with unique factorization.

-/

open nat finset list finsupp
open_locale big_operators

namespace nat

/-- `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`. -/
def factorization (n : ℕ) : ℕ →₀ ℕ :=
{ support := n.factors.to_finset,
  to_fun := λ p, if p.prime then padic_val_nat p n else 0,
  mem_support_to_fun :=
      begin
        rcases eq_or_ne n 0 with rfl | hn0, { simp },
        simp only [mem_factors hn0, mem_to_finset, ne.def, ite_eq_right_iff, not_forall,
          exists_prop, and.congr_right_iff],
        rintro p hp,
        haveI := fact_iff.mpr hp,
        exact dvd_iff_padic_val_nat_ne_zero hn0,
      end }

lemma factorization_def (n : ℕ) {p : ℕ} (pp : p.prime) : n.factorization p = padic_val_nat p n :=
by simpa [factorization] using absurd pp

/-- We can write both `n.factorization p` and `n.factors.count p` to represent the power
of `p` in the factorization of `n`: we declare the former to be the simp-normal form. -/
@[simp] lemma factors_count_eq {n p : ℕ} : n.factors.count p = n.factorization p :=
begin
  rcases n.eq_zero_or_pos with rfl | hn0, { simp [factorization] },
  by_cases pp : p.prime, swap,
  { rw count_eq_zero_of_not_mem (mt prime_of_mem_factors pp), simp [factorization, pp] },
  simp only [factorization, coe_mk, pp, if_true],
  rw [←part_enat.coe_inj, padic_val_nat_def' pp.ne_one hn0,
    unique_factorization_monoid.multiplicity_eq_count_normalized_factors pp hn0.ne'],
  simp [factors_eq],
end

lemma factorization_eq_factors_multiset (n : ℕ) :
  n.factorization = (n.factors : multiset ℕ).to_finsupp :=
by { ext p, simp }

lemma multiplicity_eq_factorization {n p : ℕ} (pp : p.prime) (hn : n ≠ 0) :
  multiplicity p n = n.factorization p :=
by simp [factorization, pp, (padic_val_nat_def' pp.ne_one hn.bot_lt)]

/-! ### Basic facts about factorization -/

@[simp] lemma factorization_prod_pow_eq_self {n : ℕ} (hn : n ≠ 0) : n.factorization.prod pow = n :=
begin
  rw factorization_eq_factors_multiset n,
  simp only [←prod_to_multiset, factorization, multiset.coe_prod, multiset.to_finsupp_to_multiset],
  exact prod_factors hn,
end

lemma eq_of_factorization_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
  (h : ∀ p : ℕ, a.factorization p = b.factorization p) : a = b :=
eq_of_perm_factors ha hb (by simpa only [list.perm_iff_count, factors_count_eq] using h)

/-- Every nonzero natural number has a unique prime factorization -/
lemma factorization_inj : set.inj_on factorization { x : ℕ | x ≠ 0 } :=
λ a ha b hb h, eq_of_factorization_eq ha hb (λ p, by simp [h])

@[simp] lemma factorization_zero : factorization 0 = 0 :=
by simpa [factorization]

@[simp] lemma factorization_one : factorization 1 = 0 :=
by simpa [factorization]

/-- The support of `n.factorization` is exactly `n.factors.to_finset` -/
@[simp] lemma support_factorization {n : ℕ} : n.factorization.support = n.factors.to_finset :=
by simp [factorization]

lemma factor_iff_mem_factorization {n p : ℕ} : p ∈ n.factorization.support ↔ p ∈ n.factors :=
by simp only [support_factorization, list.mem_to_finset]

lemma prime_of_mem_factorization {n p : ℕ} (hp : p ∈ n.factorization.support) : p.prime :=
prime_of_mem_factors (factor_iff_mem_factorization.mp hp)

lemma pos_of_mem_factorization {n p : ℕ} (hp : p ∈ n.factorization.support) : 0 < p :=
prime.pos (prime_of_mem_factorization hp)

lemma le_of_mem_factorization {n p : ℕ} (h : p ∈ n.factorization.support) : p ≤ n :=
le_of_mem_factors (factor_iff_mem_factorization.mp h)

@[simp]
lemma factorization_eq_zero_of_non_prime (n : ℕ) {p : ℕ} (hp : ¬p.prime) : n.factorization p = 0 :=
not_mem_support_iff.1 (mt prime_of_mem_factorization hp)

lemma factorization_eq_zero_of_lt {n p : ℕ} (h : n < p) : n.factorization p = 0 :=
finsupp.not_mem_support_iff.mp (mt le_of_mem_factorization (not_le_of_lt h))

@[simp] lemma factorization_zero_right (n : ℕ) : n.factorization 0 = 0 :=
factorization_eq_zero_of_non_prime _ not_prime_zero

@[simp] lemma factorization_one_right (n : ℕ) : n.factorization 1 = 0 :=
factorization_eq_zero_of_non_prime _ not_prime_one

lemma dvd_of_factorization_pos {n p : ℕ} (hn : n.factorization p ≠ 0) : p ∣ n :=
dvd_of_mem_factors (factor_iff_mem_factorization.1 (mem_support_iff.2 hn))

lemma prime.factorization_pos_of_dvd {n p : ℕ} (hp : p.prime) (hn : n ≠ 0) (h : p ∣ n) :
  0 < n.factorization p :=
by rwa [←factors_count_eq, count_pos, mem_factors_iff_dvd hn hp]

/-- The only numbers with empty prime factorization are `0` and `1` -/
lemma factorization_eq_zero_iff (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 :=
begin
  rw factorization_eq_factors_multiset n,
  simp [factorization, add_equiv.map_eq_zero_iff, multiset.coe_eq_zero],
end

lemma factorization_eq_zero_iff' (n p : ℕ) :
  n.factorization p = 0 ↔ ¬p.prime ∨ ¬p ∣ n ∨ n = 0 :=
begin
  rw [←not_mem_support_iff, support_factorization, mem_to_finset],
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  { simp [hn, nat.mem_factors, not_and_distrib] },
end

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp] lemma factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b).factorization = a.factorization + b.factorization :=
by { ext p, simp only [add_apply, ←factors_count_eq,
                       perm_iff_count.mp (perm_factors_mul ha hb) p, count_append] }

lemma factorization_mul_support {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b).factorization.support = a.factorization.support ∪ b.factorization.support :=
begin
  ext q,
  simp only [finset.mem_union, factor_iff_mem_factorization],
  exact mem_factors_mul ha hb
end

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
@[simp] lemma factorization_pow (n k : ℕ) :
  factorization (n^k) = k • n.factorization :=
begin
  induction k with k ih, { simp },
  rcases eq_or_ne n 0 with rfl | hn, { simp },
  rw [pow_succ, factorization_mul hn (pow_ne_zero _ hn), ih, succ_eq_one_add, add_smul, one_smul],
end

/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
@[simp] lemma prime.factorization {p : ℕ} (hp : prime p) :
  p.factorization = single p 1 :=
begin
  ext q,
  rw [←factors_count_eq, factors_prime hp, single_apply, count_singleton', if_congr eq_comm];
  refl,
end

/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
@[simp] lemma prime.factorization_self {p : ℕ} (hp : prime p) : p.factorization p = 1 :=
by simp [hp]

/-- For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k` -/
lemma prime.factorization_pow {p k : ℕ} (hp : prime p) :
  factorization (p ^ k) = single p k :=
by simp [hp]

/-- If the factorization of `n` contains just one number `p` then `n` is a power of `p` -/
lemma eq_pow_of_factorization_eq_single {n p k : ℕ} (hn : n ≠ 0)
  (h : n.factorization = finsupp.single p k) : n = p ^ k :=
by { rw [←nat.factorization_prod_pow_eq_self hn, h], simp }

/-- If a product over `n.factorization` doesn't use the multiplicities of the prime factors
then it's equal to the corresponding product over `n.factors.to_finset` -/
lemma prod_factorization_eq_prod_factors {n : ℕ} {β : Type*} [comm_monoid β] (f : ℕ → β) :
  n.factorization.prod (λ p k, f p) = ∏ p in n.factors.to_finset, (f p) :=
by { apply prod_congr support_factorization, simp }

/-- For any `p : ℕ` and any function `g : α → ℕ` that's non-zero on `S : finset α`,
the power of `p` in `S.prod g` equals the sum over `x ∈ S` of the powers of `p` in `g x`.
Generalises `factorization_mul`, which is the special case where `S.card = 2` and `g = id`. -/
lemma factorization_prod {α : Type*} {S : finset α} {g : α → ℕ} (hS : ∀ x ∈ S, g x ≠ 0) :
  (S.prod g).factorization = S.sum (λ x, (g x).factorization) :=
begin
  classical,
  ext p,
  apply finset.induction_on' S, { simp },
  { intros x T hxS hTS hxT IH,
    have hT : T.prod g ≠ 0 := prod_ne_zero_iff.mpr (λ x hx, hS x (hTS hx)),
    simp [prod_insert hxT, sum_insert hxT, ←IH, factorization_mul (hS x hxS) hT] }
end

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/

/-- Any finsupp `f : ℕ →₀ ℕ` whose support is in the primes is equal to the factorization of
the product `∏ (a : ℕ) in f.support, a ^ f a`. -/
lemma prod_pow_factorization_eq_self {f : ℕ →₀ ℕ} (hf : ∀ (p : ℕ), p ∈ f.support → prime p) :
  (f.prod pow).factorization = f :=
begin
  have h : ∀ x : ℕ, x ∈ f.support → x ^ f x ≠ 0 := λ p hp, pow_ne_zero _ (prime.ne_zero (hf p hp)),
  simp only [finsupp.prod, factorization_prod h],
  nth_rewrite_rhs 0 (sum_single f).symm,
  exact sum_congr rfl (λ p hp, prime.factorization_pow (hf p hp)),
end

lemma eq_factorization_iff {n : ℕ} {f : ℕ →₀ ℕ} (hn : n ≠ 0) (hf : ∀ p ∈ f.support, prime p) :
  f = n.factorization ↔ f.prod pow = n :=
⟨λ h, by rw [h, factorization_prod_pow_eq_self hn],
 λ h, by rw [←h, prod_pow_factorization_eq_self hf]⟩

/-- The equiv between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/
def factorization_equiv : ℕ+ ≃ {f : ℕ →₀ ℕ | ∀ p ∈ f.support, prime p} :=
{ to_fun    := λ ⟨n, hn⟩, ⟨n.factorization, λ _, prime_of_mem_factorization⟩,
  inv_fun   := λ ⟨f, hf⟩, ⟨f.prod pow,
    prod_pow_pos_of_zero_not_mem_support (λ H, not_prime_zero (hf 0 H))⟩,
  left_inv  := λ ⟨x, hx⟩, subtype.ext $ factorization_prod_pow_eq_self hx.ne.symm,
  right_inv := λ ⟨f, hf⟩, subtype.ext $ prod_pow_factorization_eq_self hf }

lemma factorization_equiv_apply (n : ℕ+) : (factorization_equiv n).1 = n.1.factorization :=
by { cases n, refl }

lemma factorization_equiv_inv_apply {f : ℕ →₀ ℕ} (hf : ∀ p ∈ f.support, prime p) :
  (factorization_equiv.symm ⟨f, hf⟩).1 = f.prod pow := rfl

/-! ### Factorization and divisibility -/

lemma dvd_of_mem_factorization {n p : ℕ} (h : p ∈ n.factorization.support) : p ∣ n :=
begin
  rcases eq_or_ne n 0 with rfl | hn, { simp },
  simp [←mem_factors_iff_dvd hn (prime_of_mem_factorization h), factor_iff_mem_factorization.mp h],
end

lemma pow_factorization_dvd (n p : ℕ) : p ^ n.factorization p ∣ n :=
begin
  by_cases hp : p.prime, swap, { simp [factorization_eq_zero_of_non_prime n hp] },
  rw ←factors_count_eq,
  apply dvd_of_factors_subperm (pow_ne_zero _ hp.ne_zero),
  rw [hp.factors_pow, list.subperm_ext_iff],
  intros q hq,
  simp [list.eq_of_mem_repeat hq],
end

lemma pow_factorization_le {n : ℕ} (p : ℕ) (hn : n ≠ 0) : p ^ n.factorization p ≤ n :=
le_of_dvd hn.bot_lt (nat.pow_factorization_dvd n p)

/-- A crude upper bound on `n.factorization p` -/
lemma factorization_lt {n : ℕ} (p : ℕ) (hn : n ≠ 0) : n.factorization p < n :=
begin
  by_cases pp : p.prime, swap, { simp [factorization_eq_zero_of_non_prime n pp], exact hn.bot_lt },
  rw ←pow_lt_iff_lt_right pp.two_le,
  apply lt_of_le_of_lt (pow_factorization_le p hn),
  exact lt_of_lt_of_le (lt_two_pow n) (pow_le_pow_of_le_left (by linarith) pp.two_le n),
end

/-- An upper bound on `n.factorization p` -/
lemma factorization_le_of_le_pow {n p b : ℕ} (hb : n ≤ p ^ b) : n.factorization p ≤ b :=
begin
  rcases eq_or_ne n 0 with rfl | hn, { simp },
  by_cases pp : p.prime,
  { exact (pow_le_iff_le_right pp.two_le).1 (le_trans (pow_factorization_le p hn) hb) },
  { simp [factorization_eq_zero_of_non_prime n pp] }
end

lemma div_pow_factorization_ne_zero {n : ℕ} (p : ℕ) (hn : n ≠ 0) :
  n / p ^ n.factorization p ≠ 0 :=
begin
  by_cases pp : nat.prime p,
  { apply mt (nat.div_eq_zero_iff (pow_pos (prime.pos pp) _)).1,
    simp [le_of_dvd hn.bot_lt (nat.pow_factorization_dvd n p)] },
  { simp [nat.factorization_eq_zero_of_non_prime n pp, hn] },
end

lemma factorization_le_iff_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
  d.factorization ≤ n.factorization ↔ d ∣ n :=
begin
  split,
  { intro hdn,
    set K := n.factorization - d.factorization with hK,
    use K.prod pow,
    rw [←factorization_prod_pow_eq_self hn, ←factorization_prod_pow_eq_self hd,
        ←finsupp.prod_add_index' pow_zero pow_add, hK, add_tsub_cancel_of_le hdn] },
  { rintro ⟨c, rfl⟩, rw factorization_mul hd (right_ne_zero_of_mul hn), simp },
end

lemma pow_succ_factorization_not_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.prime) :
  ¬ p ^ (n.factorization p + 1) ∣ n :=
begin
  intro h,
  rw ←factorization_le_iff_dvd (pow_pos hp.pos _).ne' hn at h,
  simpa [hp.factorization] using h p,
end

lemma factorization_le_factorization_mul_left {a b : ℕ} (hb : b ≠ 0) :
  a.factorization ≤ (a * b).factorization :=
begin
  rcases eq_or_ne a 0 with rfl | ha, { simp },
  rw [factorization_le_iff_dvd ha $ mul_ne_zero ha hb],
  exact dvd.intro b rfl
end

lemma factorization_le_factorization_mul_right {a b : ℕ} (ha : a ≠ 0) :
  b.factorization ≤ (a * b).factorization :=
by { rw mul_comm, apply factorization_le_factorization_mul_left ha }

lemma prime.pow_dvd_iff_le_factorization {p k n : ℕ} (pp : prime p) (hn : n ≠ 0) :
  p ^ k ∣ n ↔ k ≤ n.factorization p :=
by rw [←factorization_le_iff_dvd (pow_pos pp.pos k).ne' hn, pp.factorization_pow, single_le_iff]

lemma prime.pow_dvd_iff_dvd_pow_factorization {p k n : ℕ} (pp : prime p) (hn : n ≠ 0) :
  p ^ k ∣ n ↔ p ^ k ∣ p ^ n.factorization p :=
by rw [pow_dvd_pow_iff_le_right pp.one_lt, pp.pow_dvd_iff_le_factorization hn]

lemma prime.dvd_iff_one_le_factorization {p n : ℕ} (pp : prime p) (hn : n ≠ 0) :
  p ∣ n ↔ 1 ≤ n.factorization p :=
iff.trans (by simp) (pp.pow_dvd_iff_le_factorization hn)

lemma exists_factorization_lt_of_lt {a b : ℕ} (ha : a ≠ 0) (hab : a < b) :
  ∃ p : ℕ, a.factorization p < b.factorization p :=
begin
  have hb : b ≠ 0 := (ha.bot_lt.trans hab).ne',
  contrapose! hab,
  rw [←finsupp.le_def, factorization_le_iff_dvd hb ha] at hab,
  exact le_of_dvd ha.bot_lt hab,
end

@[simp] lemma factorization_div {d n : ℕ} (h : d ∣ n) :
  (n / d).factorization = n.factorization - d.factorization :=
begin
  rcases eq_or_ne d 0 with rfl | hd, { simp [zero_dvd_iff.mp h] },
  rcases eq_or_ne n 0 with rfl | hn, { simp },
  apply add_left_injective d.factorization,
  simp only,
  rw [tsub_add_cancel_of_le $ (nat.factorization_le_iff_dvd hd hn).mpr h,
      ←nat.factorization_mul (nat.div_pos (nat.le_of_dvd hn.bot_lt h) hd.bot_lt).ne' hd,
      nat.div_mul_cancel h],
end

lemma not_dvd_div_pow_factorization {n p : ℕ} (hp : prime p) (hn : n ≠ 0) :
  ¬p ∣ n / p ^ n.factorization p :=
begin
  rw [nat.prime.dvd_iff_one_le_factorization hp (div_pow_factorization_ne_zero p hn),
    nat.factorization_div (nat.pow_factorization_dvd n p)],
  simp [hp.factorization],
end

lemma coprime_of_div_pow_factorization {n p : ℕ} (hp : prime p) (hn : n ≠ 0) :
  coprime p (n / p ^ n.factorization p) :=
(or_iff_left (not_dvd_div_pow_factorization hp hn)).mp $ coprime_or_dvd_of_prime hp _

lemma dvd_iff_div_factorization_eq_tsub {d n : ℕ} (hd : d ≠ 0) (hdn : d ≤ n) :
  d ∣ n ↔ (n / d).factorization = n.factorization - d.factorization :=
begin
  refine ⟨factorization_div, _⟩,
  rcases eq_or_lt_of_le hdn with rfl | hd_lt_n, { simp },
  have h1 : n / d ≠ 0 := λ H, nat.lt_asymm hd_lt_n ((nat.div_eq_zero_iff hd.bot_lt).mp H),
  intros h,
  rw dvd_iff_le_div_mul n d,
  by_contra h2,
  cases (exists_factorization_lt_of_lt (mul_ne_zero h1 hd) (not_le.mp h2)) with p hp,
  rwa [factorization_mul h1 hd, add_apply, ←lt_tsub_iff_right, h, tsub_apply,
    lt_self_iff_false] at hp
end

lemma dvd_iff_prime_pow_dvd_dvd (n d : ℕ) :
  d ∣ n ↔ ∀ p k : ℕ, prime p → p ^ k ∣ d → p ^ k ∣ n :=
begin
  rcases eq_or_ne n 0 with rfl | hn, { simp },
  rcases eq_or_ne d 0 with rfl | hd,
  { simp only [zero_dvd_iff, hn, false_iff, not_forall],
    refine ⟨2, n, prime_two, ⟨dvd_zero _, _⟩⟩,
    apply mt (le_of_dvd hn.bot_lt) (not_le.mpr (lt_two_pow n)) },
  refine ⟨λ h p k _ hpkd, dvd_trans hpkd h, _⟩,
  rw [←factorization_le_iff_dvd hd hn, finsupp.le_def],
  intros h p,
  by_cases pp : prime p, swap, { simp [factorization_eq_zero_of_non_prime d pp] },
  rw ←pp.pow_dvd_iff_le_factorization hn,
  exact h p _ pp (pow_factorization_dvd _ _)
end

lemma prod_prime_factors_dvd (n : ℕ) : (∏ (p : ℕ) in n.factors.to_finset, p) ∣ n :=
begin
  by_cases hn : n = 0, { subst hn, simp },
  simpa [prod_factors hn] using multiset.to_finset_prod_dvd_prod (n.factors : multiset ℕ),
end

lemma factorization_gcd {a b : ℕ} (ha_pos : a ≠ 0) (hb_pos : b ≠ 0) :
  (gcd a b).factorization = a.factorization ⊓ b.factorization :=
begin
  let dfac := a.factorization ⊓ b.factorization,
  let d := dfac.prod pow,
  have dfac_prime : ∀ (p : ℕ), p ∈ dfac.support → prime p,
  { intros p hp,
    have : p ∈ a.factors ∧ p ∈ b.factors := by simpa using hp,
    exact prime_of_mem_factors this.1 },
  have h1 : d.factorization = dfac := prod_pow_factorization_eq_self dfac_prime,
  have hd_pos : d ≠ 0 := (factorization_equiv.inv_fun ⟨dfac, dfac_prime⟩).2.ne.symm,
  suffices : d = (gcd a b), { rwa ←this },
  apply gcd_greatest,
  { rw [←factorization_le_iff_dvd hd_pos ha_pos, h1], exact inf_le_left },
  { rw [←factorization_le_iff_dvd hd_pos hb_pos, h1], exact inf_le_right },
  { intros e hea heb,
    rcases decidable.eq_or_ne e 0 with rfl | he_pos,
    { simp only [zero_dvd_iff] at hea, contradiction, },
    have hea' := (factorization_le_iff_dvd he_pos ha_pos).mpr hea,
    have heb' := (factorization_le_iff_dvd he_pos hb_pos).mpr heb,
    simp [←factorization_le_iff_dvd he_pos hd_pos, h1, hea', heb'] },
end

@[to_additive sum_factors_gcd_add_sum_factors_mul]
lemma prod_factors_gcd_mul_prod_factors_mul {β : Type*} [comm_monoid β] (m n : ℕ) (f : ℕ → β) :
  (m.gcd n).factors.to_finset.prod f * (m * n).factors.to_finset.prod f
    = m.factors.to_finset.prod f * n.factors.to_finset.prod f :=
begin
  rcases eq_or_ne n 0 with rfl | hm0, { simp },
  rcases eq_or_ne m 0 with rfl | hn0, { simp },
  rw [←@finset.prod_union_inter _ _ m.factors.to_finset n.factors.to_finset, mul_comm],
  congr,
  { apply factors_mul_to_finset; assumption },
  { simp only [←support_factorization, factorization_gcd hn0 hm0, finsupp.support_inf] },
end

lemma set_of_pow_dvd_eq_Icc_factorization {n p : ℕ} (pp : p.prime) (hn : n ≠ 0) :
  {i : ℕ | i ≠ 0 ∧ p ^ i ∣ n} = set.Icc 1 (n.factorization p) :=
by { ext, simp [lt_succ_iff, one_le_iff_ne_zero, pp.pow_dvd_iff_le_factorization hn] }

/-- The set of positive powers of prime `p` that divide `n` is exactly the set of
positive natural numbers up to `n.factorization p`. -/
lemma Icc_factorization_eq_pow_dvd (n : ℕ) {p : ℕ} (pp : prime p) :
  Icc 1 ((n.factorization) p) = (Ico 1 n).filter (λ (i : ℕ), p ^ i ∣ n) :=
begin
  rcases eq_or_ne n 0 with rfl | hn, { simp },
  ext x,
  simp only [mem_Icc, finset.mem_filter, mem_Ico, and_assoc, and.congr_right_iff,
    pp.pow_dvd_iff_le_factorization hn, iff_and_self],
  exact λ H1 H2, lt_of_le_of_lt H2 (factorization_lt p hn),
end

lemma factorization_eq_card_pow_dvd (n : ℕ) {p : ℕ} (pp : p.prime) :
  n.factorization p = ((Ico 1 n).filter (λ i, p ^ i ∣ n)).card :=
by simp [←Icc_factorization_eq_pow_dvd n pp]

lemma Ico_filter_pow_dvd_eq {n p b : ℕ} (pp : p.prime) (hn : n ≠ 0) (hb : n ≤ p ^ b):
  (Ico 1 n).filter (λ i, p ^ i ∣ n) = (Icc 1 b).filter (λ i, p ^ i ∣ n) :=
begin
  ext x,
  simp only [finset.mem_filter, mem_Ico, mem_Icc, and.congr_left_iff, and.congr_right_iff],
  rintro h1 -,
  simp [lt_of_pow_dvd_right hn pp.two_le h1,
    (pow_le_iff_le_right pp.two_le).1 ((le_of_dvd hn.bot_lt h1).trans hb)],
end

/-! ### Factorization and coprimes -/

/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma factorization_mul_apply_of_coprime {p a b : ℕ} (hab : coprime a b)  :
  (a * b).factorization p = a.factorization p + b.factorization p :=
by simp only [←factors_count_eq, perm_iff_count.mp (perm_factors_mul_of_coprime hab), count_append]

/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma factorization_mul_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).factorization = a.factorization + b.factorization :=
begin
  ext q,
  simp only [finsupp.coe_add, add_apply, ←factors_count_eq, factorization_mul_apply_of_coprime hab],
end

/-- If `p` is a prime factor of `a` then the power of `p` in `a` is the same that in `a * b`,
for any `b` coprime to `a`. -/
lemma factorization_eq_of_coprime_left {p a b : ℕ} (hab : coprime a b) (hpa : p ∈ a.factors) :
  (a * b).factorization p = a.factorization p :=
begin
  rw [factorization_mul_apply_of_coprime hab, ←factors_count_eq, ←factors_count_eq],
  simpa only [count_eq_zero_of_not_mem (coprime_factors_disjoint hab hpa)],
end

/-- If `p` is a prime factor of `b` then the power of `p` in `b` is the same that in `a * b`,
for any `a` coprime to `b`. -/
lemma factorization_eq_of_coprime_right {p a b : ℕ} (hab : coprime a b) (hpb : p ∈ b.factors) :
  (a * b).factorization p = b.factorization p :=
by { rw mul_comm, exact factorization_eq_of_coprime_left (coprime_comm.mp hab) hpb }

/-- The prime factorizations of coprime `a` and `b` are disjoint -/
lemma factorization_disjoint_of_coprime {a b : ℕ} (hab : coprime a b) :
  disjoint a.factorization.support b.factorization.support :=
by simpa only [support_factorization]
  using disjoint_to_finset_iff_disjoint.mpr (coprime_factors_disjoint hab)

/-- For coprime `a` and `b` the prime factorization `a * b` is the union of those of `a` and `b` -/
lemma factorization_mul_support_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).factorization.support = a.factorization.support ∪ b.factorization.support :=
begin
  rw factorization_mul_of_coprime hab,
  exact support_add_eq (factorization_disjoint_of_coprime hab),
end

/-! ### Induction principles involving factorizations -/

/-- Given `P 0, P 1` and a way to extend `P a` to `P (p ^ n * a)` for prime `p` not dividing `a`,
we can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def rec_on_prime_pow {P : ℕ → Sort*} (h0 : P 0) (h1 : P 1)
  (h : ∀ a p n : ℕ, p.prime → ¬ p ∣ a → 0 < n → P a → P (p ^ n * a)) : ∀ (a : ℕ), P a :=
λ a, nat.strong_rec_on a $ λ n,
  match n with
  | 0     := λ _, h0
  | 1     := λ _, h1
  | (k+2) := λ hk, begin
    let p := (k + 2).min_fac,
    have hp : prime p := min_fac_prime (succ_succ_ne_one k),
    -- the awkward `let` stuff here is because `factorization` is noncomputable (finsupp);
    -- we get around this by using the computable `factors.count`, and rewriting when we want
    -- to use the `factorization` API
    let t := (k+2).factors.count p,
    have ht : t = (k+2).factorization p := factors_count_eq,
    have hpt : p ^ t ∣ k + 2 := by { rw ht, exact pow_factorization_dvd _ _ },
    have htp : 0 < t :=
    by { rw ht, exact hp.factorization_pos_of_dvd (nat.succ_ne_zero _) (min_fac_dvd _) },
    convert h ((k + 2) / p ^ t) p t hp _ _ _,
    { rw nat.mul_div_cancel' hpt, },
    { rw [nat.dvd_div_iff hpt, ←pow_succ', ht],
      exact pow_succ_factorization_not_dvd (k + 1).succ_ne_zero hp },
    { exact htp },
    { apply hk _ (nat.div_lt_of_lt_mul _),
      simp [lt_mul_iff_one_lt_left nat.succ_pos', one_lt_pow_iff htp.ne, hp.one_lt] },
    end
  end

/-- Given `P 0`, `P 1`, and `P (p ^ n)` for positive prime powers, and a way to extend `P a` and
`P b` to `P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def rec_on_pos_prime_pos_coprime {P : ℕ → Sort*} (hp : ∀ p n : ℕ, prime p → 0 < n → P (p ^ n))
  (h0 : P 0) (h1 : P 1) (h : ∀ a b, 1 < a → 1 < b → coprime a b → P a → P b → P (a * b)) :
  ∀ a, P a :=
rec_on_prime_pow h0 h1 $
begin
  intros a p n hp' hpa hn hPa,
  by_cases ha1 : a = 1,
  { rw [ha1, mul_one],
    exact hp p n hp' hn },
  refine h (p^n) a ((hp'.one_lt).trans_le (le_self_pow (prime.one_lt hp').le (succ_le_iff.mpr hn)))
    _ _ (hp _ _ hp' hn) hPa,
  { contrapose! hpa,
    simp [lt_one_iff.1 (lt_of_le_of_ne hpa ha1)] },
  simpa [hn, prime.coprime_iff_not_dvd hp'],
end

/-- Given `P 0`, `P (p ^ n)` for all prime powers, and a way to extend `P a` and `P b` to
`P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def rec_on_prime_coprime {P : ℕ → Sort*} (h0 : P 0) (hp : ∀ p n : ℕ, prime p → P (p ^ n))
  (h : ∀ a b, 1 < a → 1 < b → coprime a b → P a → P b → P (a * b)) : ∀ a, P a :=
rec_on_pos_prime_pos_coprime (λ p n h _, hp p n h) h0 (hp 2 0 prime_two) h

/-- Given `P 0`, `P 1`, `P p` for all primes, and a way to extend `P a` and `P b` to
`P (a * b)`, we can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def rec_on_mul {P : ℕ → Sort*} (h0 : P 0) (h1 : P 1)
  (hp : ∀ p, prime p → P p) (h : ∀ a b, P a → P b → P (a * b)) : ∀ a, P a :=
let hp : ∀ p n : ℕ, prime p → P (p ^ n) :=
  λ p n hp', match n with
  | 0     := h1
  | (n+1) := by exact h _ _ (hp p hp') (_match _)
  end in
rec_on_prime_coprime h0 hp $ λ a b _ _ _, h a b

/-- For any multiplicative function `f` with `f 1 = 1` and any `n ≠ 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
lemma multiplicative_factorization {β : Type*} [comm_monoid β] (f : ℕ → β)
  (h_mult : ∀ x y : ℕ, coprime x y → f (x * y) = f x * f y) (hf : f 1 = 1) :
  ∀ {n : ℕ}, n ≠ 0 → f n = n.factorization.prod (λ p k, f (p ^ k)) :=
begin
  apply' nat.rec_on_pos_prime_pos_coprime,
  { intros p k hp hk hpk, simp [prime.factorization_pow hp, finsupp.prod_single_index _, hf] },
  { simp },
  { rintros -, rw [factorization_one, hf], simp },
  { intros a b _ _ hab ha hb hab_pos,
    rw [h_mult a b hab, ha (left_ne_zero_of_mul hab_pos), hb (right_ne_zero_of_mul hab_pos),
        factorization_mul_of_coprime hab, ←prod_add_index_of_disjoint],
    convert (factorization_disjoint_of_coprime hab) },
end

/-- For any multiplicative function `f` with `f 1 = 1` and `f 0 = 1`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
lemma multiplicative_factorization' {β : Type*} [comm_monoid β] (f : ℕ → β)
  (h_mult : ∀ x y : ℕ, coprime x y → f (x * y) = f x * f y) (hf0 : f 0 = 1) (hf1 : f 1 = 1) :
  ∀ {n : ℕ}, f n = n.factorization.prod (λ p k, f (p ^ k)) :=
begin
  apply' nat.rec_on_pos_prime_pos_coprime,
  { intros p k hp hk, simp only [hp.factorization_pow], rw prod_single_index _, simp [hf1] },
  { simp [hf0] },
  { rw [factorization_one, hf1], simp },
  { intros a b _ _ hab ha hb,
    rw [h_mult a b hab, ha, hb, factorization_mul_of_coprime hab, ←prod_add_index_of_disjoint],
    convert (factorization_disjoint_of_coprime hab) },
end

/-- Two positive naturals are equal if their prime padic valuations are equal -/
lemma eq_iff_prime_padic_val_nat_eq (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
  a = b ↔ (∀ p : ℕ, p.prime → padic_val_nat p a = padic_val_nat p b) :=
begin
  split,
  { rintros rfl, simp },
  { intro h,
    refine eq_of_factorization_eq ha hb (λ p, _),
    by_cases pp : p.prime,
    { simp [factorization_def, pp, h p pp] },
    { simp [factorization_eq_zero_of_non_prime, pp] } },
end

lemma prod_pow_prime_padic_val_nat (n : nat) (hn : n ≠ 0) (m : nat) (pr : n < m) :
  ∏ p in finset.filter nat.prime (finset.range m), p ^ (padic_val_nat p n) = n :=
begin
  nth_rewrite_rhs 0 ←factorization_prod_pow_eq_self hn,
  rw eq_comm,
  apply finset.prod_subset_one_on_sdiff,
  { exact λ p hp, finset.mem_filter.mpr
      ⟨finset.mem_range.mpr (gt_of_gt_of_ge pr (le_of_mem_factorization hp)),
       prime_of_mem_factorization hp⟩ },
  { intros p hp,
    cases finset.mem_sdiff.mp hp with hp1 hp2,
    rw ←factorization_def n (finset.mem_filter.mp hp1).2,
    simp [finsupp.not_mem_support_iff.mp hp2] },
  { intros p hp,
    simp [factorization_def n (prime_of_mem_factorization hp)] }
end

/-! ### Lemmas about factorizations of particular functions -/

-- TODO: Port lemmas from `data/nat/multiplicity` to here, re-written in terms of `factorization`

/-- Exactly `n / p` naturals in `[1, n]` are multiples of `p`. -/
lemma card_multiples (n p : ℕ) : card ((finset.range n).filter (λ e, p ∣ e + 1)) = n / p :=
begin
  induction n with n hn, { simp },
  simp [nat.succ_div, add_ite, add_zero, finset.range_succ, filter_insert, apply_ite card,
    card_insert_of_not_mem, hn],
end

/-- Exactly `n / p` naturals in `(0, n]` are multiples of `p`. -/
lemma Ioc_filter_dvd_card_eq_div (n p : ℕ) :
  ((Ioc 0 n).filter (λ x, p ∣ x)).card = n / p :=
begin
  induction n with n IH, { simp },
  -- TODO: Golf away `h1` after Yaël PRs a lemma asserting this
  have h1 : Ioc 0 n.succ = insert n.succ (Ioc 0 n),
  { rcases n.eq_zero_or_pos with rfl | hn, { simp },
    simp_rw [←Ico_succ_succ, Ico_insert_right (succ_le_succ hn.le), Ico_succ_right] },
  simp [nat.succ_div, add_ite, add_zero, h1, filter_insert, apply_ite card,
    card_insert_eq_ite, IH, finset.mem_filter, mem_Ioc, not_le.2 (lt_add_one n)],
end

end nat
