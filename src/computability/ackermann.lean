/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import computability.primrec
import tactic.linarith

/-!
# Ackermann function

In this file, we define the two-argument Ackermann function `ack`. Despite having a recursive
definition, we show that this isn't a primitive recursive function.

## Main results

- `exists_lt_ack_of_primrec`: any primitive recursive function is pointwise bounded above by `ack m`
  for some `m`.
- `not_primrec₂_ack`: the two-argument Ackermann function is not primitive recursive.

## Proof approach

We very broadly adapt the proof idea from
https://www.planetmath.org/ackermannfunctionisnotprimitiverecursive. Namely, we prove that for any
primitive recursive `f : ℕ → ℕ`, there exists `m` such that `f n < ack m n` for all `n`. This then
implies that `λ n, ack n n` can't be primitive recursive, and so neither can `ack`. We aren't able
to use the same bounds as in that proof though, since our approach of using pairing functions
differs from their approach of using multivariate functions.

The important bounds we show during the main inductive proof (`exists_lt_ack_of_primrec`) are the
following. Assuming `∀ n, f n < ack a n` and `∀ n, g n < ack b n`, we have:

- `∀ n, nat.mkpair (f n) (g n) < ack (max a b + 3) n`.
- `∀ n, g (f n) < ack (max a b + 2) n`.
- `∀ n, nat.elim (f n.unpair.1) (λ (y IH : ℕ), g (nat.mkpair n.unpair.1 (nat.mkpair y IH)))
  n.unpair.2 < ack (max a b + 9) n`.

The last one is evidently the hardest. Using `nat.unpair_add_le`, we reduce it to the more
manageable

- `∀ m n, elim (f m) (λ (y IH : ℕ), g (nat.mkpair m (nat.mkpair y IH))) n <
  ack (max a b + 9) (m + n)`.

We then prove this by induction on `n`. Our proof crucially depends on `ack_mkpair_lt`, which is
applied twice, giving us a constant of `4 + 4`. The rest of the proof consists of simpler bounds
which bump up our constant to `9`.
-/

open nat

/-- The two-argument Ackermann function, defined so that

- `ack 0 n = n + 1`
- `ack (m + 1) 0 = ack m 1`
- `ack (m + 1) (n + 1) = ack m (ack (m + 1) n)`.

This is of interest as both a fast-growing function, and as an example of a recursive function that
isn't primitive recursive. -/
def ack : ℕ → ℕ → ℕ
| 0       n       := n + 1
| (m + 1) 0       := ack m 1
| (m + 1) (n + 1) := ack m (ack (m + 1) n)

@[simp] theorem ack_zero (n : ℕ) : ack 0 n = n + 1 := by rw ack
@[simp] theorem ack_succ_zero (m : ℕ) : ack (m + 1) 0 = ack m 1 := by rw ack
@[simp] theorem ack_succ_succ (m n : ℕ) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw ack

@[simp] theorem ack_one (n : ℕ) : ack 1 n = n + 2 :=
begin
  induction n with n IH,
  { simp },
  { simp [IH] }
end

@[simp] theorem ack_two (n : ℕ) : ack 2 n = 2 * n + 3 :=
begin
  induction n with n IH,
  { simp },
  { simp [IH, mul_succ] }
end

private theorem ack_three_aux (n : ℕ) : (ack 3 n : ℤ) = 2 ^ (n + 3) - 3 :=
begin
  induction n with n IH,
  { simp, norm_num },
  { simp [IH, pow_succ],
    rw [mul_sub, sub_add],
    norm_num }
end

@[simp] theorem ack_three (n : ℕ) : ack 3 n = 2 ^ (n + 3) - 3 :=
begin
  zify,
  rw cast_sub,
  { exact_mod_cast ack_three_aux n },
  { have H : 3 ≤ 2 ^ 3 := by norm_num,
    exact H.trans (pow_mono one_le_two $ le_add_left le_rfl) }
end

theorem ack_pos : ∀ m n, 0 < ack m n
| 0       n       := by simp
| (m + 1) 0       := by { rw ack_succ_zero, apply ack_pos }
| (m + 1) (n + 1) := by { rw ack_succ_succ, apply ack_pos }

theorem one_lt_ack_succ_left : ∀ m n, 1 < ack (m + 1) n
| 0       n       := by simp
| (m + 1) 0       := by { rw ack_succ_zero, apply one_lt_ack_succ_left }
| (m + 1) (n + 1) := by { rw ack_succ_succ, apply one_lt_ack_succ_left }

theorem one_lt_ack_succ_right : ∀ m n, 1 < ack m (n + 1)
| 0       n := by simp
| (m + 1) n := begin
  rw ack_succ_succ,
  cases exists_eq_succ_of_ne_zero (ack_pos (m + 1) n).ne',
  rw h,
  apply one_lt_ack_succ_right
end

theorem ack_strict_mono_right : ∀ m, strict_mono (ack m)
| 0 n₁ n₂ h := by simpa using h
| (m + 1) 0 (n + 1) h := begin
  rw [ack_succ_zero, ack_succ_succ],
  exact ack_strict_mono_right _ (one_lt_ack_succ_left m n)
end
| (m + 1) (n₁ + 1) (n₂ + 1) h := begin
  rw [ack_succ_succ, ack_succ_succ],
  apply ack_strict_mono_right _ (ack_strict_mono_right _ _),
  rwa add_lt_add_iff_right at h
end

theorem ack_mono_right (m : ℕ) : monotone (ack m) := (ack_strict_mono_right m).monotone

theorem ack_injective_right (m : ℕ) : function.injective (ack m) :=
(ack_strict_mono_right m).injective

@[simp] theorem ack_lt_iff_right {m n₁ n₂ : ℕ} : ack m n₁ < ack m n₂ ↔ n₁ < n₂ :=
(ack_strict_mono_right m).lt_iff_lt

@[simp] theorem ack_le_iff_right {m n₁ n₂ : ℕ} : ack m n₁ ≤ ack m n₂ ↔ n₁ ≤ n₂ :=
(ack_strict_mono_right m).le_iff_le

@[simp] theorem ack_inj_right {m n₁ n₂ : ℕ} : ack m n₁ = ack m n₂ ↔ n₁ = n₂ :=
(ack_injective_right m).eq_iff

theorem max_ack_right (m n₁ n₂ : ℕ) : ack m (max n₁ n₂) = max (ack m n₁) (ack m n₂) :=
(ack_mono_right m).map_max

theorem add_lt_ack : ∀ m n, m + n < ack m n
| 0       n       := by simp
| (m + 1) 0       := by simpa using add_lt_ack m 1
| (m + 1) (n + 1) :=
calc (m + 1) + n + 1
      ≤ m + (m + n + 2) : by linarith
  ... < ack m (m + n + 2) : add_lt_ack _ _
  ... ≤ ack m (ack (m + 1) n) : ack_mono_right m $
          le_of_eq_of_le (by ring_nf) $ succ_le_of_lt $ add_lt_ack (m + 1) n
  ... = ack (m + 1) (n + 1) : (ack_succ_succ m n).symm

theorem add_add_one_le_ack (m n : ℕ) : m + n + 1 ≤ ack m n := succ_le_of_lt (add_lt_ack m n)

theorem lt_ack_left (m n : ℕ) : m < ack m n := (self_le_add_right m n).trans_lt $ add_lt_ack m n
theorem lt_ack_right (m n : ℕ) : n < ack m n := (self_le_add_left n m).trans_lt $ add_lt_ack m n

-- we reorder the arguments to appease the equation compiler
private theorem ack_strict_mono_left' : ∀ {m₁ m₂} n, m₁ < m₂ → ack m₁ n < ack m₂ n
| m 0 n := λ h, (nat.not_lt_zero m h).elim
| 0 (m + 1) 0 := λ h, by simpa using one_lt_ack_succ_right m 0
| 0 (m + 1) (n + 1) := λ h, begin
  rw [ack_zero, ack_succ_succ],
  apply lt_of_le_of_lt (le_trans _ $ add_le_add_left (add_add_one_le_ack _ _) m) (add_lt_ack _ _),
  linarith
end
| (m₁ + 1) (m₂ + 1) 0 := λ h, by simpa using ack_strict_mono_left' 1 ((add_lt_add_iff_right 1).1 h)
| (m₁ + 1) (m₂ + 1) (n + 1) := λ h, begin
  rw [ack_succ_succ, ack_succ_succ],
  exact (ack_strict_mono_left' _ $ (add_lt_add_iff_right 1).1 h).trans
    (ack_strict_mono_right _ $ ack_strict_mono_left' n h)
end

theorem ack_strict_mono_left (n : ℕ) : strict_mono (λ m, ack m n) :=
λ m₁ m₂, ack_strict_mono_left' n

theorem ack_mono_left (n : ℕ) : monotone (λ m, ack m n) := (ack_strict_mono_left n).monotone

theorem ack_injective_left (n : ℕ) : function.injective (λ m, ack m n) :=
(ack_strict_mono_left n).injective

@[simp] theorem ack_lt_iff_left {m₁ m₂ n : ℕ} : ack m₁ n < ack m₂ n ↔ m₁ < m₂ :=
(ack_strict_mono_left n).lt_iff_lt

@[simp] theorem ack_le_iff_left {m₁ m₂ n : ℕ} : ack m₁ n ≤ ack m₂ n ↔ m₁ ≤ m₂ :=
(ack_strict_mono_left n).le_iff_le

@[simp] theorem ack_inj_left {m₁ m₂ n : ℕ} : ack m₁ n = ack m₂ n ↔ m₁ = m₂ :=
(ack_injective_left n).eq_iff

theorem max_ack_left (m₁ m₂ n : ℕ) : ack (max m₁ m₂) n = max (ack m₁ n) (ack m₂ n) :=
(ack_mono_left n).map_max

theorem ack_le_ack {m₁ m₂ n₁ n₂ : ℕ} (hm : m₁ ≤ m₂) (hn : n₁ ≤ n₂) : ack m₁ n₁ ≤ ack m₂ n₂ :=
(ack_mono_left n₁ hm).trans $ ack_mono_right m₂ hn

theorem ack_succ_right_le_ack_succ_left (m n : ℕ) : ack m (n + 1) ≤ ack (m + 1) n :=
begin
  cases n,
  { simp },
  { rw [ack_succ_succ, succ_eq_add_one],
    apply ack_mono_right m (le_trans _ $ add_add_one_le_ack _ n),
    linarith }
end

-- All the inequalities from this point onwards are specific to the main proof.

private theorem sq_le_two_pow_add_one_minus_three (n : ℕ) : n ^ 2 ≤ 2 ^ (n + 1) - 3 :=
begin
  induction n with k hk,
  { norm_num },
  { cases k,
    { norm_num },
    { rw [succ_eq_add_one, add_sq, pow_succ 2, two_mul (2 ^ _), add_tsub_assoc_of_le,
        add_comm (2 ^ _), add_assoc],
      { apply add_le_add hk,
        norm_num,
        apply succ_le_of_lt,
        rw [pow_succ, mul_lt_mul_left (@zero_lt_two ℕ _ _)],
        apply lt_two_pow },
      { rw [pow_succ, pow_succ],
        linarith [one_le_pow k 2 zero_lt_two] } } }
end

theorem ack_add_one_sq_lt_ack_add_three : ∀ m n, (ack m n + 1) ^ 2 ≤ ack (m + 3) n
| 0       n       := by simpa using sq_le_two_pow_add_one_minus_three (n + 2)
| (m + 1) 0       := by { rw [ack_succ_zero, ack_succ_zero], apply ack_add_one_sq_lt_ack_add_three }
| (m + 1) (n + 1) := begin
  rw [ack_succ_succ, ack_succ_succ],
  apply (ack_add_one_sq_lt_ack_add_three _ _).trans (ack_mono_right _ $ ack_mono_left _ _),
  linarith
end

theorem ack_ack_lt_ack_max_add_two (m n k : ℕ) : ack m (ack n k) < ack (max m n + 2) k :=
calc ack m (ack n k)
      ≤ ack (max m n) (ack n k) : ack_mono_left _ (le_max_left _ _)
  ... < ack (max m n) (ack (max m n + 1) k) : ack_strict_mono_right _ $ ack_strict_mono_left k $
          lt_succ_of_le $ le_max_right m n
  ... = ack (max m n + 1) (k + 1) : (ack_succ_succ _ _).symm
  ... ≤ ack (max m n + 2) k : ack_succ_right_le_ack_succ_left _ _

theorem ack_add_one_sq_lt_ack_add_four (m n : ℕ) : ack m ((n + 1) ^ 2) < ack (m + 4) n :=
calc ack m ((n + 1) ^ 2)
      < ack m ((ack m n + 1) ^ 2) : ack_strict_mono_right m $
          pow_lt_pow_of_lt_left (succ_lt_succ $ lt_ack_right m n) zero_lt_two
  ... ≤ ack m (ack (m + 3) n) : ack_mono_right m $ ack_add_one_sq_lt_ack_add_three m n
  ... ≤ ack (m + 2) (ack (m + 3) n) : ack_mono_left _ $ by linarith
  ... = ack (m + 3) (n + 1) : (ack_succ_succ _ n).symm
  ... ≤ ack (m + 4) n : ack_succ_right_le_ack_succ_left _ n

theorem ack_mkpair_lt (m n k : ℕ) : ack m (mkpair n k) < ack (m + 4) (max n k) :=
(ack_strict_mono_right m $ mkpair_lt_max_add_one_sq n k).trans $ ack_add_one_sq_lt_ack_add_four _ _

/-- If `f` is primitive recursive, there exists `m` such that `f n < ack m n` for all `n`. -/
theorem exists_lt_ack_of_nat_primrec {f : ℕ → ℕ} (hf : nat.primrec f) : ∃ m, ∀ n, f n < ack m n :=
begin
  induction hf with f g hf hg IHf IHg f g hf hg IHf IHg f g hf hg IHf IHg,
  -- Zero function:
  { exact ⟨0, ack_pos 0⟩ },
  -- Successor function:
  { refine ⟨1, λ n, _⟩,
    rw succ_eq_one_add,
    apply add_lt_ack },
  -- Left projection:
  { refine ⟨0, λ n, _⟩,
    rw [ack_zero, lt_succ_iff],
    exact unpair_left_le n },
  -- Right projection:
  { refine ⟨0, λ n, _⟩,
    rw [ack_zero, lt_succ_iff],
    exact unpair_right_le n },
  all_goals { cases IHf with a ha, cases IHg with b hb },
  -- Pairing:
  { refine ⟨max a b + 3, λ n, (mkpair_lt_max_add_one_sq _ _).trans_le $
      (nat.pow_le_pow_of_le_left (add_le_add_right _ _) 2).trans $
        ack_add_one_sq_lt_ack_add_three _ _⟩,
    rw max_ack_left,
    exact max_le_max (ha n).le (hb n).le },
  -- Composition:
  { exact ⟨max a b + 2, λ n,
      (ha _).trans $ (ack_strict_mono_right a $ hb n).trans $ ack_ack_lt_ack_max_add_two a b n⟩ },
  -- Primitive recursion operator:
  { -- We prove this simpler inequality first.
    have : ∀ {m n}, elim (f m) (λ y IH, g $ mkpair m $ mkpair y IH) n < ack (max a b + 9) (m + n),
    { intros m n,
      -- We induct on n.
      induction n with n IH,
      -- The base case is easy.
      { apply (ha m).trans (ack_strict_mono_left m $ (le_max_left a b).trans_lt _),
        linarith },
      { -- We get rid of the first `mkpair`.
        rw elim_succ,
        apply (hb _).trans ((ack_mkpair_lt _ _ _).trans_le _),
        -- If m is the maximum, we get a very weak inequality.
        cases lt_or_le _ m with h₁ h₁,
        { rw max_eq_left h₁.le,
          exact ack_le_ack (add_le_add (le_max_right a b) $ by norm_num) (self_le_add_right m _) },
        rw max_eq_right h₁,
        -- We get rid of the second `mkpair`.
        apply (ack_mkpair_lt _ _ _).le.trans,
        -- If n is the maximum, we get a very weak inequality.
        cases lt_or_le _ n with h₂ h₂,
        { rw [max_eq_left h₂.le, add_assoc],
          exact ack_le_ack (add_le_add (le_max_right a b) $ by norm_num)
            ((le_succ n).trans $ self_le_add_left _ _) },
        rw max_eq_right h₂,
        -- We now use the inductive hypothesis, and some simple algebraic manipulation.
        apply (ack_strict_mono_right _ IH).le.trans,
        rw [add_succ m, add_succ _ 8, ack_succ_succ (_ + 8), add_assoc],
        exact ack_mono_left _ (add_le_add (le_max_right a b) le_rfl) } },
    -- The proof is now simple.
    exact ⟨max a b + 9, λ n, this.trans_le $ ack_mono_right _ $ unpair_add_le n⟩ }
end

theorem not_nat_primrec_ack_self : ¬ nat.primrec (λ n, ack n n) :=
λ h, by { cases exists_lt_ack_of_nat_primrec h with m hm, exact (hm m).false }

theorem not_primrec_ack_self : ¬ _root_.primrec (λ n, ack n n) :=
by { rw primrec.nat_iff, exact not_nat_primrec_ack_self }

/-- The Ackermann function is not primitive recursive. -/
theorem not_primrec₂_ack : ¬ primrec₂ ack :=
λ h, not_primrec_ack_self $ h.comp primrec.id primrec.id
