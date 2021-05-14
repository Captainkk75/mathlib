import data.nat.prime
import data.finset.intervals
import data.nat.multiplicity
import data.padics.padic_norm
import tactic
import ring_theory.multiplicity
import algebra.module

open_locale big_operators

/-- The multiplicity of p in the nth central binomial coefficient-/
private def α (n : nat) (p : nat) [hp : fact p.prime] : nat :=
padic_val_nat p (nat.choose (2 * n) n)

/-
def primes_le (n : nat) : finset {m : nat // m ≤ n ∧ nat.prime m} :=
begin
  have r : finset {m : nat // m ≤ n ∧ nat.prime m} = finset {m : nat // m < n + 1 ∧ nat.prime m},
  { congr, ext,
    split,
    { rintros ⟨x_le_n, x_prime⟩,
      exact ⟨nat.lt_succ_iff.mpr x_le_n, x_prime⟩, },
    { rintros ⟨x_lt_sn, x_prime⟩,
      exact ⟨nat.lt_succ_iff.mp x_lt_sn, x_prime ⟩, }, },
  simpa only [r, finset.mem_filter, finset.mem_range] using (finset.filter nat.prime (finset.range (n + 1))).attach,
end

lemma alpha_eq (n : nat) (n_pos : 0 < n) :
  nat.choose (2 * n) n = ∏ p in primes_le n, p.val ^ (α n n_pos p p.property.2) :=
begin
sorry
end
-/

lemma central_binom_nonzero (n : ℕ) : nat.choose (2 * n) n ≠ 0 :=
ne_of_gt (nat.choose_pos (by linarith))

lemma foo (p n : ℕ) : nat.log p (2 * n) < nat.log p (2 * n) + 1 :=
begin
  exact lt_add_one (nat.log p (2 * n))
end

lemma foo3 {p : ℕ} : p ≤ 2 * p :=
begin
  omega,
end

lemma claim_1
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  : p ^ (α n p) ≤ 2 * n
  :=
begin
  unfold α,
  rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n),
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (nat.log p (2 * n) + 1)
                        (hp.out) (by linarith) (foo p n)],
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp [r, ←two_mul],
  have bar : (finset.filter (λ (i : ℕ), p ^ i ≤ 2 * (n % p ^ i)) (finset.Ico 1 (nat.log p (2 * n) + 1))).card ≤ nat.log p (2 * n),
    calc (finset.filter (λ (i : ℕ), p ^ i ≤ 2 * (n % p ^ i)) (finset.Ico 1 (nat.log p (2 * n) + 1))).card ≤ (finset.Ico 1 (nat.log p (2 * n) + 1)).card : by apply finset.card_filter_le
    ... = (nat.log p (2 * n) + 1) - 1 : by simp,
  have baz : p ^ (nat.log p (2 * n)) ≤ 2 * n,
    apply nat.pow_log_le_self,
    apply hp.out.one_lt,
    calc 1 ≤ 3 : dec_trivial
    ...    ≤ n : n_big
    ...    ≤ 2 * n : foo3,
  -- have djf : 1 ≤ p,
  --   calc
  apply trans (pow_le_pow (trans one_le_two hp.out.two_le) bar) baz,
  -- apply trans (@foo2 p _ _ bar) baz,
end

lemma add_two_not_le_one (x : nat) (pr : x.succ.succ ≤ 1) : false :=
  nat.not_succ_le_zero x (nat.lt_succ_iff.mp pr)

lemma claim_2
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  (smallish : (2 * n) < p ^ 2)
  : (α n p) ≤ 1
  :=
begin
  have h1 : p ^ α n p < p ^ 2,
    calc p ^ α n p ≤ 2 * n : claim_1 p n n_big
    ...            < p ^ 2 : smallish,

  let h2 := (pow_lt_pow_iff hp.out.one_lt).1 h1,
  omega,
  -- -- pow_lt_pow_iff
  -- unfold α,
  -- rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n),
  -- simp only [@nat.prime.multiplicity_choose p (2 * n) n _ hp.out (by linarith) (le_refl (2 * n))],
  -- have r : 2 * n - n = n, by
  --   calc 2 * n - n = n + n - n: by rw two_mul n
  --   ... = n: nat.add_sub_cancel n n,
  -- simp only [r, finset.filter_congr_decidable],
  -- have s : ∀ i, p ^ i ≤ n % p ^ i + n % p ^ i → i ≤ 1, by
  --   { intros i pr,
  --     cases le_or_lt i 1, {exact h,},
  --     { exfalso,
  --       have u : 2 * n < 2 * (n % p ^ i), by
  --         calc 2 * n < p ^ 2 : smallish
  --         ... ≤ p ^ i : nat.pow_le_pow_of_le_right (nat.prime.pos is_prime) h
  --         ... ≤ n % p ^ i + n % p ^ i : pr
  --         ... = 2 * (n % p ^ i) : (two_mul _).symm,
  --       have v : n < n % p ^ i, by linarith,
  --       have w : n % p ^ i ≤ n, exact (nat.mod_le _ _),
  --       linarith, }, },
  -- have t : ∀ x ∈ finset.Ico 1 (2 * n), p ^ x ≤ n % p ^ x + n % p ^ x ↔ (x ≤ 1 ∧ p ^ x ≤ n % p ^ x + n % p ^ x), by
  --   {
  --     intros x size,
  --     split,
  --     { intros bound, split, exact s x bound, exact bound, },
  --     { intros size2,
  --       cases x,
  --       { simp at size, trivial, },
  --       { cases x,
  --         { exact size2.right, },
  --         { exfalso, exact nat.not_succ_le_zero _ (nat.lt_succ_iff.mp (size2.left)), }, }, },
  --   },
  -- simp only [finset.filter_congr t],
  -- simp only [finset.filter_and],
  -- simp only [@finset.Ico.filter_Ico_bot 1 (2 * n) (by linarith)],
  -- exact finset.card_singleton_inter,
end

lemma move_mul (m p i : nat) (b : m < i * p) : m / p < i :=
begin
  cases lt_or_le (m / p) i,
  { exact h },
  exfalso,
  have u : i * p ≤ m, by exact le_trans (nat.mul_le_mul_right p h) (nat.div_mul_le_self m p),
  linarith,
end

private lemma collapse_enat (n : enat) (s : 2 = n + 1 + 1) : n = 0 :=
begin
  have u : 0 + 1 = n + 1, by simpa using (enat.add_right_cancel_iff (enat.coe_ne_top 1)).1 s,
  have v : 0 = n, by exact (enat.add_right_cancel_iff (enat.coe_ne_top 1)).1 u,
  exact v.symm
end

lemma twice_nat_small : ∀ (n : nat) (h : 2 * n < 2), n = 0
| 0 := λ _, rfl
| (n + 1) := λ pr, by linarith

lemma pow_big : ∀ (i p : nat) (p_pos : 0 < p) (i_big : 1 < i), p * p ≤ p ^ i
| 0 := λ _ _ pr, by linarith
| 1 := λ _ _ pr, by linarith
| (i + 2) := λ p p_pos i_big, by {
  calc p * p = p ^ 2 : by ring_exp
  ... ≤ p ^ (i + 2) : nat.pow_le_pow_of_le_right p_pos i_big,
}

lemma claim_3
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 < n)
  (small : p ≤ n)
  (big : 2 * n < 3 * p)
  : α n p = 0
  :=
begin
  have expand : nat.choose (2 * n) n * (nat.fact n) * (nat.fact n) = nat.fact (2 * n), by
    calc nat.choose (2 * n) n * (nat.fact n) * (nat.fact n)
        = nat.choose (2 * n) n * (nat.fact n) * (nat.fact (n + n - n)) : by rw nat.add_sub_cancel n n
      ... = nat.choose (2 * n) n * (nat.fact n) * (nat.fact (2 * n - n)) : by rw two_mul n
      ... = nat.fact (2 * n) : nat.choose_mul_fact_mul_fact (by linarith),

  have mult_fact_two_n : multiplicity p (nat.fact (2 * n)) = _, by
    calc multiplicity p (nat.fact (2 * n))
        = multiplicity p (nat.choose (2 * n) n * (nat.fact n) * (nat.fact n)) :
            congr_arg (multiplicity p) expand.symm
      ... = multiplicity p (nat.choose (2 * n) n * nat.fact n) + multiplicity p (nat.fact n) :
            by rw nat.prime.multiplicity_mul is_prime
      ... = multiplicity p (nat.choose (2 * n) n) + multiplicity p (nat.fact n) + multiplicity p (nat.fact n) :
            by rw nat.prime.multiplicity_mul is_prime,

  have two_n_div_p_small : (2 * n) / p < 3, by exact move_mul (2 * n) p 3 big,
  have n_div_p : n / p = 1,
    { cases lt_trichotomy (n / p) 1,
      { exfalso,
        have n_zero : n / p = 0, by exact twice_nat_small (n / p) (by linarith),
        have r : n < p, by exact (nat.div_eq_zero_iff (nat.prime.pos is_prime)).1 n_zero,
        linarith, },
      { cases h,
        { exact h },
        { have s : 2 < 2 * (n / p), by linarith,
          linarith [nat.mul_div_le_mul_div_assoc 2 n p], }, }, },
  have p_pos : 0 < p, by exact nat.prime.pos is_prime,

  have two_n_small : ∀ i > 1, 2 * n < p ^ i, by
    { intros i one_less,
      cases lt_trichotomy 2 p,
      { calc 2 * n < 3 * p: big
        ... ≤ p * p : nat.mul_le_mul_right p h
        ... ≤ p ^ i : pow_big i p p_pos one_less, },
      cases h,
      { exfalso, rw ← h at big, linarith },
      { have u : 2 ≤ p, by exact nat.prime.two_le is_prime, linarith, }, },

  have mult_in_two_n : multiplicity p (nat.fact (2 * n)) = 2,
    { rw @nat.prime.multiplicity_fact p is_prime (2 * n) (2 * n) (by linarith),
      have first_term_two : (2 * n) / p = 2, by linarith [nat.mul_div_le_mul_div_assoc 2 n p],
      rw @finset.sum_eq_sum_Ico_succ_bot _ _ 1 (2 * n) (by linarith) (λ i, 2 * n / p ^ i),
      have t : ∑ k in finset.Ico 2 (2 * n), 2 * n / p ^ k = 0, by
        { apply finset.sum_eq_zero,
          have other_terms_zero : ∀ i > 1, (2 * n) / (p ^ i) = 0, by
            { intros i one_less,
              refine (nat.div_eq_zero_iff (nat.pow_pos p_pos i)).2 _,
              exact two_n_small i one_less, },
          intros i pr,
          exact other_terms_zero i (by linarith [(list.Ico.mem.mp pr).1]), },
      rw t,
      simp only [add_zero, nat.pow_one],
      rw first_term_two,
      exact enat.coe_add 1 1 },
  have mult_in_n : multiplicity p (nat.fact n) = 1,
    { rw @nat.prime.multiplicity_fact p is_prime n n (by linarith),
      have r : 0 < p, by exact nat.prime.pos is_prime,
      rw @finset.sum_eq_sum_Ico_succ_bot _ _ 1 n (by linarith) (λ i, n / p ^ i),
      have other_terms_zero : ∀ i > 1, n / (p ^ i) = 0, by
        { intros i one_less,
          refine (nat.div_eq_zero_iff (nat.pow_pos p_pos i)).2 _,
          calc n ≤ 2 * n : by linarith
            ... < p ^ i : two_n_small i one_less,
        },
      have t : ∑ k in finset.Ico 2 n, n / p ^ k = 0, by
        { apply finset.sum_eq_zero,
          intros i pr,
          exact other_terms_zero i (by linarith [(list.Ico.mem.mp pr).1]), },
      rw t,
      simp only [add_zero, nat.pow_one],
      rw n_div_p,
      simp only [enat.coe_one],
    },
  rw [mult_in_two_n, mult_in_n] at mult_fact_two_n,
  have mult_choose_zero : multiplicity p (nat.choose (2 * n) n) = 0,
    by exact collapse_enat (multiplicity p (nat.choose (2 * n) n)) mult_fact_two_n,
  unfold α,
  rw @padic_val_nat_def p is_prime (nat.choose (2 * n) n) (central_binom_nonzero n),
  simp [mult_choose_zero],
end

/--
"The mean of a bounded list is less than or equal to the bound".
-/
lemma mean_le_biggest {A B : Type*} [decidable_eq A] [ordered_semiring B]
  (f : A → B) {m : B} (s : finset A) (bound : ∀ x ∈ s, f x ≤ m) : ∑ i in s, f i ≤ s.card * m :=
begin
  rw ← @smul_eq_mul B _ s.card m,
  rw ← @finset.sum_const _ _ s _ m,
  apply finset.sum_le_sum bound,
end

lemma choose_le_middle_2 (r n : ℕ) : nat.choose (2 * n) r ≤ nat.choose (2 * n) n :=
begin
  have s : (2 * n) / 2 = n, by exact nat.mul_div_cancel_left n (by linarith),
  simpa [] using (@choose_le_middle r (2 * n)),
end

/-

/-
Then:
4^n ≤ 2nCn * (2 * n + 1) (by choose_halfway_is_big)
= prod (primes <= 2n) p^(α n p) * (2n+1) ---- need to prove this
= prod (primes <= n) p^(α n p) * prod (primes n < p <= 2n) p^α * (2n+1)
= prod (primes <= 2n/3) p^α * prod (primes 2n/3 to n) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes <= 2n/3) p^α * prod (primes 2n/3 to n) 1 * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by claim 3
= prod (primes <= 2n/3) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes <= sqrt(2n)) p^α * prod(primes sqrt(2n) to 2n/3) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ prod (primes <= sqrt(2n)) p^α * prod(primes sqrt(2n) to 2n/3) p * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by claim 2
≤ prod (primes <= sqrt(2n)) p^α * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by primorial bound, proved in different PR
≤ prod (primes <= sqrt(2n)) (2n) * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by claim 1
= (2n)^π (sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ (2n)^(sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by "prime count of x is less than x", need to prove

For sufficiently large n, that last product term is > 1.
Indeed, suppose for contradiction it's equal to 1.
Then 4^n ≤ (2n)^(sqrt 2n) * 4^(2n/3) * (2n+1)
so 4^(n/3) ≤ (2n)^(sqrt 2n) (2n+1)
and this is Clearly False for sufficiently large n.
-/

lemma bertrand_eventually (n : nat) (n_big : 750 ≤ n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
sorry
end

theorem bertrand (n : nat) (n_pos : 0 < n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
cases le_or_lt 750 n,
{exact bertrand_eventually n h},
cases le_or_lt 376 n,
{ use 751, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 274 n,
{ use 547, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 139 n,
{ use 277, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 70 n,
{ use 139, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 37 n,
{ use 73, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 19 n,
{ use 37, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 11 n,
{ use 19, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 6 n,
{ use 11, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 4 n,
{ use 7, norm_num, split, linarith, linarith, },
clear h,
interval_cases n,
{ use 2, norm_num },
{ use 3, norm_num },
{ use 5, norm_num },
end

-/
