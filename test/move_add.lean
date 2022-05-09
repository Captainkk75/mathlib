import tactic.move_add
import data.polynomial.degree

open polynomial tactic interactive
open_locale polynomial

example {R : Type*} [add_comm_semigroup R] {a b c d e f g: R} (h : a + b + c = d) : b + (a + c) = d :=
begin
--  move_add [d] at *, -- d is an unused variable
  move_add at *,
--  move_add at *,  -- 'move_add at *' changes nothing
--  move_add [a, e, f, g] at h a b c ⊢, -- '[a, b, c]' did not change,
                                        -- '[e, f, g]' are unused variables
--  move_add at ⊢ h,  -- '[h]' did not change
                      -- Goal did not change
  move_add ← a at *,
end

example {a b c d e : ℕ} (h : c = d) : c + b + a = b + a + d :=
begin
  move_add [← a, b],  -- Goal: `a + c + b = a + d + b`
  congr,
  exact h
end

example {a b c d : ℕ} (h : c = d) (k : c + b * c + a * c = a * d + d + b * d) :
  b * c + c + a * c = a * d + d + b * d :=
begin
--  move_add [_ * _] at k ⊢,
  -- the first `_ * c` unifies with `b * c` and moves it to the right
  -- the second `_ * c` unifies with `a * c` and moves it to the left
  move_add [_ * c, ← _ * c], -- Goal: `a * c + c + b * c = a * d + d + b * d`
  congr,
  repeat { assumption }
end

example {a b c d : ℕ} (h : c = d) : c + b * c + a * c = a * d + d + b * d :=
begin
  -- the first `_ * c` unifies with `b * c` and moves it to the right
  -- the second `_ * c` unifies with `a * c` and moves it to the left
  move_add [_ * c, ← _ * c], -- Goal: `a * c + c + b * c = a * d + d + b * d`
  congr,
  repeat { assumption }
end
--/

variables {R : Type*} [semiring R] (f g h : R[X]) {r s t u : R}

example (hp : f = g) :
  7 + f + (C r * X ^ 3 + 42) + X ^ 5 * h = C r * X ^ 3 + h * X ^ 5 + g + 7 + 42 :=
begin
  -- we move `f, g` to the right of their respective sides, so `congr` helps us remove the
  -- repeated term
  move_add [← C r * X ^ 3, (7 : R[X]), (42 : R[X]), f, g],
  congr' 4, -- takes care of using assumption `hp`
  exact X_pow_mul,
end

example (s0 : s ≠ 0) (m n : ℕ) (mn : m < n) (m1 : 1 ≤ m) :
  (C r * X ^ m + (5 + C s * X ^ n) + m * X + 37 * X).nat_degree = n :=
begin
  -- move `C s * X ^ n` to the right, since it is the term with highest degree
  -- we also move `m * X` and `37 * X` to the left, to collect them in a single summand
  move_add [C s * X ^ n, ← ↑m * (X : R[X]), ← 37 * (X : R[X])],
  rw [← add_mul, nat_degree_add_eq_right_of_nat_degree_lt, nat_degree_C_mul_X_pow _ _ s0],
  rw [nat_degree_C_mul_X_pow _ _ s0],
  -- what is left has degree at most `m < n`, so let's inform Lean
  refine lt_of_le_of_lt _ mn,
  -- all summands are now of degree at most `m`, so we break the sum into pieces
  repeat { refine (nat_degree_add_le _ _).trans _,
    refine max_le _ _ };
    try { simp only [nat_degree_one, zero_le], done },
  -- we have now focused on the two "interesting" terms
  { convert (nat_degree_C_mul_X_pow_le (m + 37 : R) _).trans m1;
    simp only [map_add, C_eq_nat_cast, C_bit1, C_bit0, map_one, pow_one] },
  { exact nat_degree_C_mul_X_pow_le _ _ }
end
