/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison, Apurva Nakade
-/
import set_theory.game.pgame
import tactic.abel

/-!
# Combinatorial games.

In this file we define the quotient of pre-games by the equivalence relation
`p ≈ q ↔ p ≤ q ∧ q ≤ p` (its `antisymmetrization`), and construct an instance `add_comm_group game`,
as well as an instance `partial_order game`.

## Multiplication on pre-games

We define the operations of multiplication and inverse on pre-games, and prove a few basic theorems
about them. Multiplication is not well-behaved under equivalence of pre-games i.e. `x ≈ y` does not
imply `x * z ≈ y * z`. Hence, multiplication is not a well-defined operation on games. Nevertheless,
the abelian group structure on games allows us to simplify many proofs for pre-games.
-/

open function pgame

open_locale pgame

universes u

instance pgame.setoid : setoid pgame :=
⟨(≈), equiv_refl, @pgame.equiv.symm, @pgame.equiv.trans⟩

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by the equivalence
  `x ≈ y ↔ x ≤ y ∧ y ≤ x`. -/
abbreviation game := quotient pgame.setoid

theorem pgame.equiv.game_eq {x y : pgame} (h : x ≈ y) : ⟦x⟧ = ⟦y⟧ :=
quot.sound h

theorem pgame.relabelling.game_eq {x y : pgame} (h : x ≡r y) : ⟦x⟧ = ⟦y⟧ :=
h.equiv.game_eq

namespace game

instance : add_comm_group game :=
{ zero := ⟦0⟧,
  neg := quot.lift (λ x, ⟦-x⟧) (λ x y h, ((@neg_equiv_neg_iff x y).2 h).game_eq),
  add := quotient.lift₂ (λ x y : pgame, ⟦x + y⟧)
    (λ x₁ y₁ x₂ y₂ hx hy, (pgame.add_congr hx hy).game_eq),
  add_zero := by { rintro ⟨x⟩, exact (add_zero_relabelling x).game_eq },
  zero_add := by { rintro ⟨x⟩, exact (zero_add_relabelling x).game_eq },
  add_assoc := by { rintros ⟨x⟩ ⟨y⟩ ⟨z⟩, exact (add_assoc_relabelling x y z).game_eq },
  add_left_neg := by { rintro ⟨x⟩, exact (add_left_neg_equiv x).game_eq },
  add_comm := by { rintros ⟨x⟩ ⟨y⟩, exact (add_comm_relabelling x y).game_eq } }

instance : has_one game := ⟨⟦1⟧⟩
instance : inhabited game := ⟨0⟩

instance : partial_order game :=
{ le := quotient.lift₂ (λ x y, x ≤ y) (λ x₁ y₁ x₂ y₂ hx hy, propext (le_congr hx hy)),
  le_refl := by { rintro ⟨x⟩, exact le_refl x },
  le_trans := by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, exact @le_trans _ _ x y z },
  le_antisymm := by { rintro ⟨x⟩ ⟨y⟩ h₁ h₂, exact quot.sound ⟨h₁, h₂⟩ } }

/-- The less or fuzzy relation on games.

If `0 ⧏ x` (less or fuzzy with), then Left can win `x` as the first player. -/
def lf : game → game → Prop :=
quotient.lift₂ lf (λ x₁ y₁ x₂ y₂ hx hy, propext (lf_congr hx hy))

local infix ` ⧏ `:50 := lf

/-- On `game`, simp-normal inequalities should use as few negations as possible. -/
@[simp] theorem not_le : ∀ {x y : game}, ¬ x ≤ y ↔ y ⧏ x :=
by { rintro ⟨x⟩ ⟨y⟩, exact pgame.not_le }

/-- On `game`, simp-normal inequalities should use as few negations as possible. -/
@[simp] theorem not_lf : ∀ {x y : game}, ¬ x ⧏ y ↔ y ≤ x :=
by { rintro ⟨x⟩ ⟨y⟩, exact not_lf }

instance : is_trichotomous game (⧏) :=
⟨by { rintro ⟨x⟩ ⟨y⟩, change _ ∨ ⟦x⟧ = ⟦y⟧ ∨ _, rw quotient.eq, apply lf_or_equiv_or_gf }⟩

/-! It can be useful to use these lemmas to turn `pgame` inequalities into `game` inequalities, as
the `add_comm_group` structure on `game` often simplifies many proofs. -/

theorem _root_.pgame.le_iff_game_le {x y : pgame} : x ≤ y ↔ ⟦x⟧ ≤ ⟦y⟧ := iff.rfl
theorem _root_.pgame.lf_iff_game_lf {x y : pgame} : pgame.lf x y ↔ ⟦x⟧ ⧏ ⟦y⟧ := iff.rfl
theorem _root_.pgame.lt_iff_game_lt {x y : pgame} : x < y ↔ ⟦x⟧ < ⟦y⟧ := iff.rfl
theorem _root_.pgame.equiv_iff_game_eq {x y : pgame} : x ≈ y ↔ ⟦x⟧ = ⟦y⟧ :=
(@quotient.eq _ _ x y).symm

/-- The fuzzy, confused, or incomparable relation on games.

If `x ∥ 0`, then the first player can always win `x`. -/
def fuzzy : game → game → Prop :=
quotient.lift₂ fuzzy (λ x₁ y₁ x₂ y₂ hx hy, propext (fuzzy_congr hx hy))

local infix ` ∥ `:50 := fuzzy

theorem _root_.pgame.fuzzy_iff_game_fuzzy {x y : pgame} : pgame.fuzzy x y ↔ ⟦x⟧ ∥ ⟦y⟧ := iff.rfl

instance covariant_class_add_le : covariant_class game game (+) (≤) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_le_add_left _ _ _ _ b c h a }⟩

instance covariant_class_swap_add_le : covariant_class game game (swap (+)) (≤) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_le_add_right _ _ _ _ b c h a }⟩

instance covariant_class_add_lt : covariant_class game game (+) (<) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_lt_add_left _ _ _ _ b c h a }⟩

instance covariant_class_swap_add_lt : covariant_class game game (swap (+)) (<) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_lt_add_right _ _ _ _ b c h a }⟩

theorem add_lf_add_right : ∀ {b c : game} (h : b ⧏ c) (a), b + a ⧏ c + a :=
by { rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩, apply add_lf_add_right h }

theorem add_lf_add_left : ∀ {b c : game} (h : b ⧏ c) (a), a + b ⧏ a + c :=
by { rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩, apply add_lf_add_left h }

instance ordered_add_comm_group : ordered_add_comm_group game :=
{ add_le_add_left := @add_le_add_left _ _ _ game.covariant_class_add_le,
  ..game.add_comm_group,
  ..game.partial_order }

end game

namespace pgame

@[simp] lemma quot_neg (a : pgame) : ⟦-a⟧ = -⟦a⟧ := rfl

@[simp] lemma quot_add (a b : pgame) : ⟦a + b⟧ = ⟦a⟧ + ⟦b⟧ := rfl

@[simp] lemma quot_sub (a b : pgame) : ⟦a - b⟧ = ⟦a⟧ - ⟦b⟧ := rfl

/-- The lemma `pgame.equiv_of_mk_equiv` written in terms of quotients. -/
theorem quot_eq_of_mk_quot_eq {x y : pgame}
  (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves)
  (hl : ∀ i, ⟦x.move_left i⟧ = ⟦y.move_left (L i)⟧)
  (hr : ∀ j, ⟦x.move_right (R.symm j)⟧ = ⟦y.move_right j⟧) :
  ⟦x⟧ = ⟦y⟧ :=
by { simp_rw quotient.eq at hl hr ⊢, exact equiv_of_mk_equiv L R hl hr }

/-! We prove various inequalities on pre-games taking advantage of the extra structure on games. -/

theorem neg_le {x y : pgame} : -x ≤ y ↔ -y ≤ x :=
@neg_le game _ _ _ _ ⟦x⟧ ⟦y⟧

theorem neg_lt {x y : pgame} : -x < y ↔ -y < x :=
@neg_lt game _ _ _ _ ⟦x⟧ ⟦y⟧

theorem le_neg {x y : pgame} : x ≤ -y ↔ y ≤ -x :=
@le_neg game _ _ _ _ ⟦x⟧ ⟦y⟧

theorem lt_neg {x y : pgame} : x < -y ↔ y < -x :=
@lt_neg game _ _ _ _ ⟦x⟧ ⟦y⟧

theorem neg_lf {x y : pgame} : -x ⧏ y ↔ -y ⧏ x :=
by rw [←pgame.not_le, ←pgame.not_le, not_iff_not, le_neg]

theorem lf_neg {x y : pgame} : x ⧏ -y ↔ y ⧏ -x :=
by rw [←pgame.not_le, ←pgame.not_le, not_iff_not, neg_le]

theorem equiv_neg_iff_equiv_neg {x y : pgame} : x ≈ -y ↔ y ≈ -x :=
by simp only [equiv, le_neg, neg_le, and_comm]

theorem neg_equiv_iff_neg_equiv {x y : pgame} : -x ≈ y ↔ -y ≈ x :=
by simp only [equiv, le_neg, neg_le, and_comm]

theorem fuzzy_neg_iff_fuzzy_neg {x y : pgame} : x ∥ -y ↔ y ∥ -x :=
by simp only [fuzzy, lf_neg, neg_lf, and_comm]

theorem neg_fuzzy_iff_neg_fuzzy {x y : pgame} : -x ∥ y ↔ -y ∥ x :=
by simp only [fuzzy, lf_neg, neg_lf, and_comm]

@[simp] theorem neg_le_zero_iff {x : pgame} : -x ≤ 0 ↔ 0 ≤ x :=
@neg_nonpos game _ _ _ ⟦x⟧

@[simp] theorem zero_le_neg_iff {x : pgame} : 0 ≤ -x ↔ x ≤ 0 :=
@neg_nonneg game _ _ _ ⟦x⟧

@[simp] theorem neg_lt_zero_iff {x : pgame} : -x < 0 ↔ 0 < x :=
@neg_lt_zero game _ _ _ ⟦x⟧

@[simp] theorem zero_lt_neg_iff {x : pgame} : 0 < -x ↔ x < 0 :=
@neg_pos game _ _ _ ⟦x⟧

@[simp] theorem neg_lf_zero_iff {x : pgame} : -x ⧏ 0 ↔ 0 ⧏ x :=
by rw [neg_lf, pgame.neg_zero]

@[simp] theorem zero_lf_neg_iff {x : pgame} : 0 ⧏ -x ↔ x ⧏ 0 :=
by rw [lf_neg, pgame.neg_zero]

@[simp] theorem neg_equiv_zero {x : pgame} : -x ≈ 0 ↔ x ≈ 0 :=
by rw [neg_equiv_iff_neg_equiv, pgame.neg_zero, equiv.comm]

@[simp] theorem neg_fuzzy_zero {x : pgame} : -x ∥ 0 ↔ x ∥ 0 :=
by rw [neg_fuzzy_iff_neg_fuzzy, pgame.neg_zero, fuzzy.comm]

@[simp] theorem zero_equiv_neg {x : pgame} : 0 ≈ -x ↔ 0 ≈ x :=
by rw [equiv_neg_iff_equiv_neg, pgame.neg_zero, equiv.comm]

@[simp] theorem zero_fuzzy_neg {x : pgame} : 0 ∥ -x ↔ 0 ∥ x :=
by rw [fuzzy_neg_iff_fuzzy_neg, pgame.neg_zero, fuzzy.comm]

theorem sub_le_zero_iff {x y : pgame} : x - y ≤ 0 ↔ x ≤ y :=
@sub_nonpos game _ _ _ ⟦x⟧ ⟦y⟧

theorem zero_le_sub_iff {x y : pgame} : 0 ≤ x - y ↔ y ≤ x :=
@sub_nonneg game _ _ _ ⟦x⟧ ⟦y⟧

theorem sub_lt_zero_iff {x y : pgame} : x - y < 0 ↔ x < y :=
@sub_neg game _ _ _ ⟦x⟧ ⟦y⟧

theorem zero_lt_sub_iff {x y : pgame} : 0 < x - y ↔ y < x :=
@sub_pos game _ _ _ ⟦x⟧ ⟦y⟧

theorem sub_lf_zero_iff {x y : pgame} : x - y ⧏ 0 ↔ x ⧏ y :=
by rw [←pgame.not_le, ←pgame.not_le, not_iff_not, zero_le_sub_iff]

theorem zero_lf_sub_iff {x y : pgame} : 0 ⧏ x - y ↔ y ⧏ x :=
by rw [←pgame.not_le, ←pgame.not_le, not_iff_not, sub_le_zero_iff]

/-! ### Pre-game multiplication -/

theorem quot_mul_comm : Π (x y : pgame.{u}), ⟦x * y⟧ = ⟦y * x⟧
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  refine quot_eq_of_mk_quot_eq
    (equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _))
    ((equiv.sum_comm _ _).trans (equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _))) _ _,
  all_goals { rintro (⟨i, j⟩ | ⟨i, j⟩); dsimp; rw [quot_mul_comm, quot_mul_comm (mk xl xr xL xR)] },
  { rw [quot_mul_comm (xL i), add_comm] },
  { rw [quot_mul_comm (xR i), add_comm] },
  { rw [quot_mul_comm (xR j), add_comm] },
  { rw [quot_mul_comm (xL j), add_comm] }
end
using_well_founded { dec_tac := pgame_wf_tac }

/-- `x * y` is equivalent to `y * x`. -/
theorem mul_comm_equiv (x y : pgame) : x * y ≈ y * x :=
quotient.exact $ quot_mul_comm _ _

/-- `x * 0` has exactly the same moves as `0`. -/
def mul_zero_relabelling (x : pgame) : x * 0 ≡r 0 := relabelling.is_empty _

/-- `x * 0` is equivalent to `0`. -/
theorem mul_zero_equiv (x : pgame) : x * 0 ≈ 0 := (mul_zero_relabelling x).equiv

@[simp] theorem quot_mul_zero (x : pgame) : ⟦x * 0⟧ = ⟦0⟧ :=
@quotient.sound _ _ (x * 0) _ x.mul_zero_equiv

/-- `0 * x` has exactly the same moves as `0`. -/
def zero_mul_relabelling (x : pgame) : 0 * x ≡r 0 := relabelling.is_empty _

/-- `0 * x` is equivalent to `0`. -/
theorem zero_mul_equiv (x : pgame) : 0 * x ≈ 0 := (zero_mul_relabelling x).equiv

@[simp] theorem quot_zero_mul (x : pgame) : ⟦0 * x⟧ = ⟦0⟧ :=
@quotient.sound _ _ (0 * x) _ x.zero_mul_equiv

@[simp] theorem quot_neg_mul : Π (x y : pgame), ⟦-x * y⟧ = -⟦x * y⟧
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  refine quot_eq_of_mk_quot_eq _ _ _ _,
  { fsplit; rintro (⟨_, _⟩ | ⟨_, _⟩);
    solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 4 } },
  { fsplit; rintro (⟨_, _⟩ | ⟨_, _⟩);
    solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 4 } },
  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { change ⟦-xR i * y + (-x) * yL j - (-xR i) * yL j⟧ = ⟦-(xR i * y + x * yL j - xR i * yL j)⟧,
      simp only [quot_add, quot_sub, quot_neg_mul],
      simp, abel },
    { change ⟦-xL i * y + (-x) * yR j - (-xL i) * yR j⟧ = ⟦-(xL i * y + x * yR j - xL i * yR j)⟧,
      simp only [quot_add, quot_sub, quot_neg_mul],
      simp, abel } },
  { rintro (⟨i, j⟩ | ⟨i, j⟩),
    { change ⟦-xL i * y + (-x) * yL j - (-xL i) * yL j⟧ = ⟦-(xL i * y + x * yL j - xL i * yL j)⟧,
      simp only [quot_add, quot_sub, quot_neg_mul],
      simp, abel },
    { change ⟦-xR i * y + (-x) * yR j - (-xR i) * yR j⟧ = ⟦-(xR i * y + x * yR j - xR i * yR j)⟧,
      simp only [quot_add, quot_sub, quot_neg_mul],
      simp, abel } },
end
using_well_founded { dec_tac := pgame_wf_tac }

@[simp] theorem quot_mul_neg (x y : pgame) : ⟦x * -y⟧ = -⟦x * y⟧ :=
by rw [quot_mul_comm, quot_neg_mul, quot_mul_comm]

@[simp] theorem quot_left_distrib : Π (x y z : pgame), ⟦x * (y + z)⟧ = ⟦x * y⟧ + ⟦x * z⟧
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  let z := mk zl zr zL zR,
  refine quot_eq_of_mk_quot_eq _ _ _ _,
  { fsplit,
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩); refl },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩); refl } },
  { fsplit,
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩); refl },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩); refl } },
  { rintro (⟨i, j | k⟩ | ⟨i, j | k⟩),
    { change ⟦xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)⟧
             = ⟦xL i * y + x * yL j - xL i * yL j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)⟧
             = ⟦x * y + (xL i * z + x * zL k - xL i * zL k)⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)⟧
             = ⟦xR i * y + x * yR j - xR i * yR j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)⟧
             = ⟦x * y + (xR i * z + x * zR k - xR i * zR k)⟧,
      simp [quot_left_distrib], abel } },
  { rintro (⟨⟨i, j⟩ | ⟨i, j⟩⟩ | ⟨i, k⟩ | ⟨i, k⟩),
    { change ⟦xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)⟧
             = ⟦xL i * y + x * yR j - xL i * yR j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)⟧
             = ⟦xR i * y + x * yL j - xR i * yL j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)⟧
             = ⟦x * y + (xL i * z + x * zR k - xL i * zR k)⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)⟧
             = ⟦x * y + (xR i * z + x * zL k - xR i * zL k)⟧,
      simp [quot_left_distrib], abel } }
end
using_well_founded { dec_tac := pgame_wf_tac }

/-- `x * (y + z)` is equivalent to `x * y + x * z.`-/
theorem left_distrib_equiv (x y z : pgame) : x * (y + z) ≈ x * y + x * z :=
quotient.exact $ quot_left_distrib _ _ _

@[simp] theorem quot_left_distrib_sub (x y z : pgame) : ⟦x * (y - z)⟧ = ⟦x * y⟧ - ⟦x * z⟧ :=
by { change  ⟦x * (y + -z)⟧ = ⟦x * y⟧ + -⟦x * z⟧, rw [quot_left_distrib, quot_mul_neg] }

@[simp] theorem quot_right_distrib (x y z : pgame) : ⟦(x + y) * z⟧ = ⟦x * z⟧ + ⟦y * z⟧ :=
by simp only [quot_mul_comm, quot_left_distrib]

/-- `(x + y) * z` is equivalent to `x * z + y * z.`-/
theorem right_distrib_equiv (x y z : pgame) : (x + y) * z ≈ x * z + y * z :=
quotient.exact $ quot_right_distrib _ _ _

@[simp] theorem quot_right_distrib_sub (x y z : pgame) : ⟦(y - z) * x⟧ = ⟦y * x⟧ - ⟦z * x⟧ :=
by { change ⟦(y + -z) * x⟧ = ⟦y * x⟧ + -⟦z * x⟧, rw [quot_right_distrib, quot_neg_mul] }

@[simp] theorem quot_mul_one : Π (x : pgame), ⟦x * 1⟧ = ⟦x⟧
| (mk xl xr xL xR) :=
begin
  let x := mk xl xr xL xR,
  refine quot_eq_of_mk_quot_eq _ _ _ _,
  { fsplit,
    { rintro (⟨_, ⟨ ⟩⟩ | ⟨_, ⟨ ⟩⟩), assumption },
    { rintro i,  exact sum.inl(i, punit.star) },
    { rintro (⟨_, ⟨ ⟩⟩ | ⟨_, ⟨ ⟩⟩), refl },
    { rintro i, refl } },
  { fsplit,
    { rintro (⟨_, ⟨ ⟩⟩ | ⟨_, ⟨ ⟩⟩), assumption },
    { rintro i,  exact sum.inr(i, punit.star) },
    { rintro (⟨_, ⟨ ⟩⟩ | ⟨_, ⟨ ⟩⟩), refl },
    { rintro i, refl } },
  { rintro (⟨i, ⟨ ⟩⟩ | ⟨i, ⟨ ⟩⟩),
    change ⟦xL i * 1 + x * 0 - xL i * 0⟧ = ⟦xL i⟧,
    simp [quot_mul_one] },
  { rintro i,
    change ⟦xR i * 1 + x * 0 - xR i * 0⟧ = ⟦xR i⟧,
    simp [quot_mul_one] }
end

/-- `x * 1` is equivalent to `x`. -/
theorem mul_one_equiv (x : pgame) : x * 1 ≈ x := quotient.exact $ quot_mul_one _

@[simp] theorem quot_one_mul (x : pgame) : ⟦1 * x⟧ = ⟦x⟧ :=
by rw [quot_mul_comm, quot_mul_one x]

/-- `1 * x` is equivalent to `x`. -/
theorem one_mul_equiv (x : pgame) : 1 * x ≈ x := quotient.exact $ quot_one_mul _

theorem quot_mul_assoc : Π (x y z : pgame), ⟦x * y * z⟧ = ⟦x * (y * z)⟧
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  let z := mk zl zr zL zR,
  refine quot_eq_of_mk_quot_eq _ _ _ _,
  { fsplit,
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_,⟨_, _⟩ | ⟨_, _⟩⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_,_⟩ | ⟨_, _⟩,_⟩); refl },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_,⟨_, _⟩ | ⟨_, _⟩⟩); refl } },
  { fsplit,
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩,_⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩,_⟩); refl },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩); refl } },
  { rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩),
    { change ⟦(xL i * y + x * yL j - xL i * yL j) * z + (x * y) * zL k
               - (xL i * y + x * yL j - xL i * yL j) * zL k⟧
             = ⟦xL i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k)
               - xL i * (yL j * z + y * zL k - yL j * zL k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xR i * y + x * yR j - xR i * yR j) * z + (x * y) * zL k
               - (xR i * y + x * yR j - xR i * yR j) * zL k⟧
             = ⟦xR i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k)
               - xR i * (yR j * z + y * zL k - yR j * zL k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xL i * y + x * yR j - xL i * yR j) * z + (x * y) * zR k
               - (xL i * y + x * yR j - xL i * yR j) * zR k⟧
             = ⟦xL i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k)
               - xL i * (yR j * z + y * zR k - yR j * zR k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xR i * y + x * yL j - xR i * yL j) * z + (x * y) * zR k
               - (xR i * y + x * yL j - xR i * yL j) * zR k⟧
             = ⟦xR i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k)
               - xR i * (yL j * z + y * zR k - yL j * zR k)⟧,
      simp [quot_mul_assoc], abel } },
  { rintro (⟨i, ⟨j, k⟩ | ⟨j, k⟩⟩ | ⟨i, ⟨j, k⟩ | ⟨j, k⟩⟩),
    { change ⟦(xL i * y + x * yL j - xL i * yL j) * z + (x * y) * zR k
               - (xL i * y + x * yL j - xL i * yL j) * zR k⟧
             = ⟦xL i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k)
               - xL i * (yL j * z + y * zR k - yL j * zR k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xL i * y + x * yR j - xL i * yR j) * z + (x * y) * zL k
               - (xL i * y + x * yR j - xL i * yR j) * zL k⟧
             = ⟦xL i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k)
               - xL i * (yR j * z + y * zL k - yR j * zL k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xR i * y + x * yL j - xR i * yL j) * z + (x * y) * zL k
               - (xR i * y + x * yL j - xR i * yL j) * zL k⟧
             = ⟦xR i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k)
               - xR i * (yL j * z + y * zL k - yL j * zL k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xR i * y + x * yR j - xR i * yR j) * z + (x * y) * zR k
               - (xR i * y + x * yR j - xR i * yR j) * zR k⟧
             = ⟦xR i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k)
               - xR i * (yR j * z + y * zR k - yR j * zR k)⟧,
      simp [quot_mul_assoc], abel } }
end
using_well_founded { dec_tac := pgame_wf_tac }

/-- `x * y * z` is equivalent to `x * (y * z).`-/
theorem mul_assoc_equiv (x y z : pgame) : x * y * z ≈ x * (y * z) :=
quotient.exact $ quot_mul_assoc _ _ _

/-- Because the two halves of the definition of `inv` produce more elements
on each side, we have to define the two families inductively.
This is the indexing set for the function, and `inv_val` is the function part. -/
inductive inv_ty (l r : Type u) : bool → Type u
| zero : inv_ty ff
| left₁ : r → inv_ty ff → inv_ty ff
| left₂ : l → inv_ty tt → inv_ty ff
| right₁ : l → inv_ty ff → inv_ty tt
| right₂ : r → inv_ty tt → inv_ty tt

instance (l r : Type u) [is_empty l] [is_empty r] : is_empty (inv_ty l r tt) :=
⟨by rintro (_|_|_|a|a); exact is_empty_elim a⟩

instance (l r : Type u) : inhabited (inv_ty l r ff) := ⟨inv_ty.zero⟩

instance unique_inv_ty (l r : Type u) [is_empty l] [is_empty r] : unique (inv_ty l r ff) :=
{ uniq := by { rintro (a|a|a), refl, all_goals { exact is_empty_elim a } },
  ..inv_ty.inhabited l r }

/-- Because the two halves of the definition of `inv` produce more elements
of each side, we have to define the two families inductively.
This is the function part, defined by recursion on `inv_ty`. -/
def inv_val {l r} (L : l → pgame) (R : r → pgame)
  (IHl : l → pgame) (IHr : r → pgame) : ∀ {b}, inv_ty l r b → pgame
| _ inv_ty.zero := 0
| _ (inv_ty.left₁ i j) := (1 + (R i - mk l r L R) * inv_val j) * IHr i
| _ (inv_ty.left₂ i j) := (1 + (L i - mk l r L R) * inv_val j) * IHl i
| _ (inv_ty.right₁ i j) := (1 + (L i - mk l r L R) * inv_val j) * IHl i
| _ (inv_ty.right₂ i j) := (1 + (R i - mk l r L R) * inv_val j) * IHr i

@[simp] theorem inv_val_is_empty {l r : Type u} {b} (L R IHl IHr) (i : inv_ty l r b)
  [is_empty l] [is_empty r] : inv_val L R IHl IHr i = 0 :=
begin
  cases i with a _ a _ a _ a,
  { refl },
  all_goals { exact is_empty_elim a }
end

/-- The inverse of a positive surreal number `x = {L | R}` is
given by `x⁻¹ = {0,
  (1 + (R - x) * x⁻¹L) * R, (1 + (L - x) * x⁻¹R) * L |
  (1 + (L - x) * x⁻¹L) * L, (1 + (R - x) * x⁻¹R) * R}`.
Because the two halves `x⁻¹L, x⁻¹R` of `x⁻¹` are used in their own
definition, the sets and elements are inductively generated. -/
def inv' : pgame → pgame
| ⟨l, r, L, R⟩ :=
  let l' := {i // 0 < L i},
      L' : l' → pgame := λ i, L i.1,
      IHl' : l' → pgame := λ i, inv' (L i.1),
      IHr := λ i, inv' (R i) in
  ⟨inv_ty l' r ff, inv_ty l' r tt,
    inv_val L' R IHl' IHr, inv_val L' R IHl' IHr⟩

theorem zero_lf_inv' : ∀ (x : pgame), 0 ⧏ inv' x
| ⟨xl, xr, xL, xR⟩ := by { convert lf_mk _ _ inv_ty.zero, refl }

/-- `inv' 0` has exactly the same moves as `1`. -/
def inv'_zero : inv' 0 ≡r 1 :=
begin
  change mk _ _ _ _ ≡r 1,
  refine ⟨_, _, λ i, _, is_empty_elim⟩; dsimp,
  { apply equiv.equiv_punit },
  { apply equiv.equiv_pempty },
  { simp }
end

theorem inv'_zero_equiv : inv' 0 ≈ 1 := inv'_zero.equiv

/-- `inv' 1` has exactly the same moves as `1`. -/
def inv'_one : inv' 1 ≡r (1 : pgame.{u}) :=
begin
  change relabelling (mk _ _ _ _) 1,
  haveI : is_empty {i : punit.{u+1} // (0 : pgame.{u}) < 0},
  { rw lt_self_iff_false, apply_instance },
  refine ⟨_, _, λ i, _, is_empty_elim⟩; dsimp,
  { apply equiv.equiv_punit },
  { apply equiv.equiv_pempty },
  { simp }
end

theorem inv'_one_equiv : inv' 1 ≈ 1 := inv'_one.equiv

/-- The inverse of a pre-game in terms of the inverse on positive pre-games. -/
noncomputable instance : has_inv pgame :=
⟨by { classical, exact λ x, if x ≈ 0 then 0 else if 0 < x then inv' x else -inv' (-x) }⟩

noncomputable instance : has_div pgame := ⟨λ x y, x * y⁻¹⟩

theorem inv_eq_of_equiv_zero {x : pgame} (h : x ≈ 0) : x⁻¹ = 0 := if_pos h

@[simp] theorem inv_zero : (0 : pgame)⁻¹ = 0 :=
inv_eq_of_equiv_zero (equiv_refl _)

theorem inv_eq_of_pos {x : pgame} (h : 0 < x) : x⁻¹ = inv' x :=
(if_neg h.lf.not_equiv').trans (if_pos h)

theorem inv_eq_of_lf_zero {x : pgame} (h : x ⧏ 0) : x⁻¹ = -inv' (-x) :=
(if_neg h.not_equiv).trans (if_neg h.not_gt)

/-- `1⁻¹` has exactly the same moves as `1`. -/
def inv_one : 1⁻¹ ≡r 1 :=
by { rw inv_eq_of_pos zero_lt_one, exact inv'_one }

theorem inv_one_equiv : 1⁻¹ ≈ 1 := inv_one.equiv

end pgame
