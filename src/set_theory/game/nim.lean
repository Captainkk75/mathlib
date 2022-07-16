/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import data.nat.bitwise
import set_theory.game.birthday
import set_theory.game.impartial

/-!
# Nim and the Sprague-Grundy theorem

This file contains the definition for nim for any ordinal `o`. In the game of `nim o₁` both players
may move to `nim o₂` for any `o₂ < o₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (grundy_value G)`.
Finally, we compute the sum of finite Grundy numbers: if `G` and `H` have Grundy values `n` and `m`,
where `n` and `m` are natural numbers, then `G + H` has the Grundy value `n xor m`.

## Implementation details

The pen-and-paper definition of nim defines the possible moves of `nim o` to be `set.Iio o`.
However, this definition does not work for us because it would make the type of nim
`ordinal.{u} → pgame.{u + 1}`, which would make it impossible for us to state the Sprague-Grundy
theorem, since that requires the type of `nim` to be `ordinal.{u} → pgame.{u}`. For this reason, we
instead use `o.out.α` for the possible moves. You can use `to_left_moves_nim` and
`to_right_moves_nim` to convert an ordinal less than `o` into a left or right move of `nim o`, and
viceversa.
-/

universes u

/-- `ordinal.out'` has the sole purpose of making `nim` computable. It performs the same job as
  `quotient.out` but is specific to ordinals. -/
def ordinal.out' (o : ordinal) : Well_order :=
⟨o.out.α, (<), o.out.wo⟩

open_locale pgame

namespace pgame

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
  take a positive number of stones from it on their turn. -/
def nim : ordinal → pgame
| o₁ := let f := λ o₂, have hwf : ordinal.typein o₁.out'.r o₂ < o₁ := ordinal.typein_lt_self o₂,
          nim (ordinal.typein o₁.out'.r o₂) in ⟨o₁.out'.α, o₁.out'.α, f, f⟩
using_well_founded { dec_tac := tactic.assumption }

open ordinal

lemma nim_def (o : ordinal) : nim o = pgame.mk o.out.α o.out.α
  (λ o₂, nim (ordinal.typein (<) o₂))
  (λ o₂, nim (ordinal.typein (<) o₂)) :=
by { rw nim, refl }

instance : is_empty (nim 0).left_moves :=
by { rw nim_def, exact ordinal.is_empty_out_zero }

instance : is_empty (nim 0).right_moves :=
by { rw nim_def, exact ordinal.is_empty_out_zero }

noncomputable instance : unique (nim 1).left_moves :=
by { rw nim_def, exact ordinal.unique_out_one }

noncomputable instance : unique (nim 1).right_moves :=
by { rw nim_def, exact ordinal.unique_out_one }

/-- `nim 0` has exactly the same moves as `0`. -/
def nim_zero_relabelling : nim 0 ≡r 0 := relabelling.is_empty _

theorem nim_zero_equiv : nim 0 ≈ 0 := equiv.is_empty _

/-- `nim 1` has exactly the same moves as `star`. -/
noncomputable def nim_one_relabelling : nim 1 ≡r star :=
begin
  rw nim_def,
  refine ⟨_, _, λ i, _, λ j, _⟩,
  any_goals { dsimp, apply equiv.equiv_of_unique },
  all_goals { simp, exact nim_zero_relabelling }
end

theorem nim_one_equiv : nim 1 ≈ star := nim_one_relabelling.equiv

@[simp] lemma nim_birthday (o : ordinal) : (nim o).birthday = o :=
begin
  induction o using ordinal.induction with o IH,
  rw [nim_def, birthday_def],
  dsimp,
  rw max_eq_right le_rfl,
  convert lsub_typein o,
  exact funext (λ i, IH _ (typein_lt_self i))
end

lemma left_moves_nim (o : ordinal) : (nim o).left_moves = o.out.α :=
by { rw nim_def, refl }
lemma right_moves_nim (o : ordinal) : (nim o).right_moves = o.out.α :=
by { rw nim_def, refl }

lemma move_left_nim_heq (o : ordinal) : (nim o).move_left == λ i : o.out.α, nim (typein (<) i) :=
by { rw nim_def, refl }
lemma move_right_nim_heq (o : ordinal) : (nim o).move_right == λ i : o.out.α, nim (typein (<) i) :=
by { rw nim_def, refl }

/-- Turns an ordinal less than `o` into a left move for `nim o` and viceversa. -/
noncomputable def to_left_moves_nim {o : ordinal} : set.Iio o ≃ (nim o).left_moves :=
(enum_iso_out o).to_equiv.trans (equiv.cast (left_moves_nim o).symm)

/-- Turns an ordinal less than `o` into a right move for `nim o` and viceversa. -/
noncomputable def to_right_moves_nim {o : ordinal} : set.Iio o ≃ (nim o).right_moves :=
(enum_iso_out o).to_equiv.trans (equiv.cast (right_moves_nim o).symm)

@[simp] theorem to_left_moves_nim_symm_lt {o : ordinal} (i : (nim o).left_moves) :
  ↑(to_left_moves_nim.symm i) < o :=
(to_left_moves_nim.symm i).prop

@[simp] theorem to_right_moves_nim_symm_lt {o : ordinal} (i : (nim o).right_moves) :
  ↑(to_right_moves_nim.symm i) < o :=
(to_right_moves_nim.symm i).prop

@[simp] lemma move_left_nim' {o : ordinal.{u}} (i) :
  (nim o).move_left i = nim (to_left_moves_nim.symm i).val :=
(congr_heq (move_left_nim_heq o).symm (cast_heq _ i)).symm

lemma move_left_nim {o : ordinal} (i) :
  (nim o).move_left (to_left_moves_nim i) = nim i :=
by simp

@[simp] lemma move_right_nim' {o : ordinal} (i) :
  (nim o).move_right i = nim (to_right_moves_nim.symm i).val :=
(congr_heq (move_right_nim_heq o).symm (cast_heq _ i)).symm

lemma move_right_nim {o : ordinal} (i) :
  (nim o).move_right (to_right_moves_nim i) = nim i :=
by simp

/-- A recursion principle for left moves of a nim game. -/
@[elab_as_eliminator] def nim_left_moves_rec_on {o : ordinal} {P : (nim o).left_moves → Sort*}
  (i : (nim o).left_moves) (H : ∀ (a : ordinal) (ha : a < o), P (to_left_moves_nim ⟨a, ha⟩)) :
  P i :=
by { rw ←to_left_moves_nim.apply_symm_apply i, apply H }

/-- A recursion principle for right moves of a nim game. -/
@[elab_as_eliminator] def nim_right_moves_rec_on {o : ordinal} {P : (nim o).right_moves → Sort*}
  (i : (nim o).right_moves) (H : ∀ (a : ordinal) (ha : a < o), P (to_right_moves_nim ⟨a, ha⟩)) :
  P i :=
by { rw ←to_right_moves_nim.apply_symm_apply i, apply H }

@[simp] lemma neg_nim (o : ordinal) : -nim o = nim o :=
begin
  induction o using ordinal.induction with o IH,
  rw nim_def, dsimp; congr;
  funext i;
  exact IH _ (ordinal.typein_lt_self i)
end

instance nim_impartial (o : ordinal) : impartial (nim o) :=
begin
  induction o using ordinal.induction with o IH,
  rw [impartial_def, neg_nim],
  refine ⟨equiv_rfl, λ i, _, λ i, _⟩;
  simpa using IH _ (typein_lt_self _)
end

lemma nim_fuzzy_zero_of_ne_zero {o : ordinal} (ho : o ≠ 0) : nim o ∥ 0 :=
begin
  rw [impartial.fuzzy_zero_iff_lf, nim_def, lf_zero_le],
  rw ←ordinal.pos_iff_ne_zero at ho,
  exact ⟨(ordinal.principal_seg_out ho).top, by simp⟩
end

@[simp] lemma nim_add_equiv_zero_iff (o₁ o₂ : ordinal) : nim o₁ + nim o₂ ≈ 0 ↔ o₁ = o₂ :=
begin
  split,
  { contrapose,
    intro h,
    rw [impartial.not_equiv_zero_iff],
    wlog h' : o₁ ≤ o₂ using [o₁ o₂, o₂ o₁],
    { exact le_total o₁ o₂ },
    { have h : o₁ < o₂ := lt_of_le_of_ne h' h,
      rw [impartial.fuzzy_zero_iff_gf, zero_lf_le, nim_def o₂],
      refine ⟨to_left_moves_add (sum.inr _), _⟩,
      { exact (ordinal.principal_seg_out h).top },
      { simpa using (impartial.add_self (nim o₁)).2 } },
    { exact (fuzzy_congr_left add_comm_equiv).1 (this (ne.symm h)) } },
  { rintro rfl,
    exact impartial.add_self (nim o₁) }
end

@[simp] lemma nim_add_fuzzy_zero_iff {o₁ o₂ : ordinal} : nim o₁ + nim o₂ ∥ 0 ↔ o₁ ≠ o₂ :=
by rw [iff_not_comm, impartial.not_fuzzy_zero_iff, nim_add_equiv_zero_iff]

@[simp] lemma nim_equiv_iff_eq {o₁ o₂ : ordinal} : nim o₁ ≈ nim o₂ ↔ o₁ = o₂ :=
by rw [impartial.equiv_iff_add_equiv_zero, nim_add_equiv_zero_iff]

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def grundy_value : Π (G : pgame.{u}), ordinal.{u}
| G := ordinal.mex.{u u} (λ i, grundy_value (G.move_left i))
using_well_founded { dec_tac := pgame_wf_tac }

lemma grundy_value_def (G : pgame) :
  grundy_value G = ordinal.mex.{u u} (λ i, grundy_value (G.move_left i)) :=
by rw grundy_value

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem equiv_nim_grundy_value : ∀ (G : pgame.{u}) [G.impartial], G ≈ nim (grundy_value G)
| G :=
begin
  introI hG,
  rw [impartial.equiv_iff_add_equiv_zero, ←impartial.forall_left_moves_fuzzy_iff_equiv_zero],
  intro i,
  apply left_moves_add_cases i,
  { intro i₁,
    rw add_move_left_inl,
    apply (fuzzy_congr_left (add_congr_left (equiv_nim_grundy_value (G.move_left i₁)).symm)).1,
    rw nim_add_fuzzy_zero_iff,
    intro heq,
    rw [eq_comm, grundy_value_def G] at heq,
    have h := ordinal.ne_mex _,
    rw heq at h,
    exact (h i₁).irrefl },
  { intro i₂,
    rw [add_move_left_inr, ←impartial.exists_left_move_equiv_iff_fuzzy_zero],
    revert i₂,
    rw nim_def,
    intro i₂,

    have h' : ∃ i : G.left_moves, (grundy_value (G.move_left i)) =
      ordinal.typein (quotient.out (grundy_value G)).r i₂,
    { revert i₂,
      rw grundy_value_def,
      intros i₂,
      have hnotin : _ ∉ _ := λ hin, (le_not_le_of_lt (ordinal.typein_lt_self i₂)).2 (cInf_le' hin),
      simpa using hnotin},

    cases h' with i hi,
    use to_left_moves_add (sum.inl i),
    rw [add_move_left_inl, move_left_mk],
    apply (add_congr_left (equiv_nim_grundy_value (G.move_left i))).trans,
    simpa only [hi] using impartial.add_self (nim (grundy_value (G.move_left i))) }
end
using_well_founded { dec_tac := pgame_wf_tac }

lemma grundy_value_eq_iff_equiv_nim {G : pgame} [G.impartial] {o : ordinal} :
  grundy_value G = o ↔ G ≈ nim o :=
⟨by { rintro rfl, exact equiv_nim_grundy_value G },
  by { intro h, rw ←nim_equiv_iff_eq, exact (equiv_nim_grundy_value G).symm.trans h }⟩

@[simp] lemma nim_grundy_value (o : ordinal.{u}) : grundy_value (nim o) = o :=
grundy_value_eq_iff_equiv_nim.2 pgame.equiv_rfl

lemma grundy_value_eq_iff_equiv (G H : pgame) [G.impartial] [H.impartial] :
  grundy_value G = grundy_value H ↔ G ≈ H :=
grundy_value_eq_iff_equiv_nim.trans (equiv_congr_left.1 (equiv_nim_grundy_value H) _).symm

@[simp] lemma grundy_value_zero : grundy_value 0 = 0 :=
grundy_value_eq_iff_equiv_nim.2 nim_zero_equiv.symm

lemma grundy_value_iff_equiv_zero (G : pgame) [G.impartial] : grundy_value G = 0 ↔ G ≈ 0 :=
by rw [←grundy_value_eq_iff_equiv, grundy_value_zero]

@[simp] lemma grundy_value_star : grundy_value star = 1 :=
grundy_value_eq_iff_equiv_nim.2 nim_one_equiv.symm

/-- The Grundy value of the sum of two nim games with natural numbers of piles equals their bitwise
xor. We prove this inductively, by showing a -/
@[simp] lemma grundy_value_nim_add_nim (n m : ℕ) :
  grundy_value (nim.{u} n + nim.{u} m) = nat.lxor n m :=
begin
  induction n using nat.strong_induction_on with n hn generalizing m,
  induction m using nat.strong_induction_on with m hm,
  rw grundy_value_def,
  apply (ordinal.mex_le_of_ne.{u u} (λ i, _)).antisymm (ordinal.le_mex_of_forall (λ ou hu, _)),
  { apply left_moves_add_cases i;
    { refine λ a, nim_left_moves_rec_on a (λ ok hk, _),
      obtain ⟨k, rfl⟩ := ordinal.lt_omega.1 (hk.trans (ordinal.nat_lt_omega _)),
      simp only [add_move_left_inl, add_move_left_inr, move_left_nim', equiv.symm_apply_apply],
      rw nat_cast_lt at hk,
      rw hn _ hk <|> rw hm _ hk,
      refine λ h, hk.ne _,
      rw ordinal.nat_cast_inj at h,
      exact nat.lxor_left_inj h <|> exact nat.lxor_right_inj h } },
  { obtain ⟨u, rfl⟩ := ordinal.lt_omega.1 (hu.trans (ordinal.nat_lt_omega _)),
    replace hu := ordinal.nat_cast_lt.1 hu,
    cases nat.lt_lxor_cases hu with h h,
    { refine ⟨to_left_moves_add (sum.inl $ to_left_moves_nim ⟨_, ordinal.nat_cast_lt.2 h⟩), _⟩,
      simp [nat.lxor_cancel_right, hn _ h] },
    { refine ⟨to_left_moves_add (sum.inr $ to_left_moves_nim ⟨_, ordinal.nat_cast_lt.2 h⟩), _⟩,
      have : n.lxor (u.lxor n) = u, rw [nat.lxor_comm u, nat.lxor_cancel_left],
      simpa [hm _ h] using this } }
end

lemma nim_add_nim_equiv {n m : ℕ} : nim n + nim m ≈ nim (nat.lxor n m) :=
by rw [←grundy_value_eq_iff_equiv_nim, grundy_value_nim_add_nim]

lemma grundy_value_add (G H : pgame) [G.impartial] [H.impartial] {n m : ℕ} (hG : grundy_value G = n)
  (hH : grundy_value H = m) : grundy_value (G + H) = nat.lxor n m :=
begin
  rw [←nim_grundy_value (nat.lxor n m), grundy_value_eq_iff_equiv],
  refine equiv.trans _ nim_add_nim_equiv,
  convert add_congr (equiv_nim_grundy_value G) (equiv_nim_grundy_value H);
  simp only [hG, hH]
end

end pgame
