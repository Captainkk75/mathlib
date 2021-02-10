/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import order.category.NonemptyFinLinOrd.basic
import data.finset.sort
import tactic.apply_fun
import tactic.linarith

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `fin (n+1)` to `fin (m+1)`.

We show that this category is equivalent to `NonemptyFinLinOrd`.
-/

universe variables u

open category_theory

/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms are monotone functions `fin (m+1) → fin (n+1)`
-/
def simplex_category := ℕ

namespace simplex_category

instance : small_category simplex_category :=
{ hom := λ m n, preorder_hom (fin (m+1)) (fin (n+1)),
  id := λ m, preorder_hom.id,
  comp := λ _ _ _ f g, preorder_hom.comp g f, }

@[simp] lemma id_apply {n : simplex_category} (i : fin (n+1)) :
  (𝟙 n : fin _ → fin _) i = i := rfl
@[simp] lemma comp_apply {l m n : simplex_category} (f : l ⟶ m) (g : m ⟶ n) (i : fin (l+1)) :
  (f ≫ g) i = g (f i) := rfl

section generators
/-!
## Generating maps for the simplex category

TODO: prove the remaining simplicial identities
TODO: prove that these generate the category
-/

/-- The `i`-th face map from `[n]` to `[n+1]` -/
def δ {n} (i : fin (n+2)) :
  @has_hom.hom simplex_category _ n (n+1 : ℕ) :=
{ to_fun := fin.succ_above i,
  monotone' :=
  begin
    intros a b H,
    dsimp [fin.succ_above],
    split_ifs with ha hb hb,
    { simpa using H, },
    { simp at hb,
      apply le_of_lt,
      calc _ < _ : ha
         ... ≤ _ : hb
         ... < _ : fin.cast_succ_lt_succ b, },
    { simp at ha,
      apply_fun fin.cast_succ at H,
      exfalso,
      apply lt_irrefl i,
      calc _ ≤ _ : ha
         ... ≤ _ : H
         ... < _ : hb, },
    { simpa using H, },
  end }

/-- The `i`-th degeneracy map from `[n+1]` to `[n]` -/
def σ {n} (i : fin (n+1)) :
  @has_hom.hom simplex_category _ (n+1 : ℕ) n :=
{ to_fun := λ a, if h : a.val ≤ i.val
  then a.cast_lt (lt_of_le_of_lt h i.is_lt)
  else ⟨a.val.pred,
    (nat.sub_lt_right_iff_lt_add (lt_of_le_of_lt i.val.zero_le (not_le.mp h))).mpr a.is_lt⟩,
  monotone' := λ a b H,
  begin
    dsimp,
    split_ifs with ha hb,
    all_goals { simp only [fin.le_iff_coe_le_coe], simp, },
    { exact H, },
    { simp at hb, exact nat.le_pred_of_lt (lt_of_le_of_lt ha hb), },
    { calc _ ≤ _ : nat.pred_le _
         ... ≤ _ : H, },
    { exact nat.pred_le_pred H, }
  end }

@[simp] lemma fin.cast_succ_mk (n i : ℕ) (h : i < n) : fin.cast_succ ⟨i, h⟩ = ⟨i, nat.lt.step h⟩ :=
rfl

@[simp] lemma fin.succ_mk (n i : ℕ) (h : i < n) : fin.succ ⟨i, h⟩ = ⟨i + 1, nat.succ_lt_succ h⟩ :=
rfl

/-- The first simplicial identity -/
lemma δ_comp_δ {n} {i j : fin (n+2)} (H : i ≤ j) :
  δ i ≫ δ j.succ = δ j ≫ δ i.cast_succ :=
begin
  ext k,
  dsimp [δ, fin.succ_above],
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  rcases k with ⟨k, _⟩,
  split_ifs; { simp at *, try { linarith } },
end

@[simp]
lemma dite_eq_ite (P : Prop) [decidable P] {α : Type*} (x y : α) :
  dite P (λ h, x) (λ h, y) = ite P x y := rfl

/-- The second simplicial identity -/
lemma δ_comp_σ {n} {i : fin (n+2)} {j : fin (n+1)} (H : i ≤ j.cast_succ) :
  δ i.cast_succ ≫ σ j.succ = σ j ≫ δ i :=
begin
  ext k,
  dsimp [δ, σ, fin.succ_above],
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  rcases k with ⟨k, _⟩,
  simp only [subtype.mk_le_mk, simplex_category.dite_eq_ite, if_congr, subtype.mk_lt_mk,
    simplex_category.fin.succ_mk, fin.coe_cast_lt, fin.coe_succ, fin.coe_cast_succ, dif_ctx_congr,
     dite_cast, order_embedding.lt_iff_lt, simplex_category.fin.cast_succ_mk, fin.coe_mk, ite_cast] at *,
  split_ifs,
  -- Hope for the best from `linarith`:
  all_goals { simp at *, try { linarith } },
  -- Two of the goals need special handling:
  { replace h_3 := nat.le_of_pred_lt h_3, linarith, },
  { exact (nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) h_1)).symm, }
end

/-- The fifth simplicial identity -/
lemma σ_comp_σ {n} {i j : fin (n+1)} (H : i ≤ j) :
  σ i.cast_succ ≫ σ j = σ j.succ ≫ σ i :=
begin
  change i.val ≤ j.val at H,
  ext k,
  sorry
end

end generators

section skeleton

/-- The functor that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
def skeletal_functor :
  simplex_category ⥤ NonemptyFinLinOrd.{u} :=
{ obj := λ n, NonemptyFinLinOrd.of $ ulift (fin (n+1)),
  map := λ m n f, ⟨λ i, ⟨f i.down⟩, λ ⟨i⟩ ⟨j⟩ h, show f i ≤ f j, from f.monotone h⟩, }

namespace skeletal_functor

instance full : full.{0 u 0 (u+1)} skeletal_functor.{u} :=
{ preimage := λ m n f, ⟨λ i, (f ⟨i⟩).down, λ i j h, f.monotone h⟩,
  witness' := by { intros m n f, dsimp at *, ext1 ⟨i⟩, ext1, refl } }

instance : faithful skeletal_functor.{u} :=
{ map_injective' := λ m n f g h,
  begin
    ext1 i, apply equiv.ulift.symm.injective,
    show skeletal_functor.map f ⟨i⟩ = skeletal_functor.map g ⟨i⟩,
    rw h,
  end }

instance : ess_surj skeletal_functor.{u} :=
{ mem_ess_image := λ X, ⟨(fintype.card X - 1 : ℕ), ⟨begin
    have aux : fintype.card X = fintype.card X - 1 + 1,
    { exact (nat.succ_pred_eq_of_pos $ fintype.card_pos_iff.mpr ⟨⊥⟩).symm, },
    let f := mono_equiv_of_fin X aux,
    have hf := (finset.univ.order_emb_of_fin aux).strict_mono,
    refine
    { hom := ⟨λ i, f i.down, _⟩,
      inv := ⟨λ i, ⟨f.symm i⟩, _⟩,
      hom_inv_id' := _,
      inv_hom_id' := _ },
    { rintro ⟨i⟩ ⟨j⟩ h, show f i ≤ f j, exact hf.monotone h, },
    { intros i j h, show f.symm i ≤ f.symm j, rw ← hf.le_iff_le,
      show f (f.symm i) ≤ f (f.symm j), simpa only [order_iso.apply_symm_apply], },
    { ext1 ⟨i⟩, ext1, exact f.symm_apply_apply i },
    { ext1 i, exact f.apply_symm_apply i },
  end⟩⟩,}

noncomputable instance is_equivalence : is_equivalence skeletal_functor.{u} :=
equivalence.equivalence_of_fully_faithfully_ess_surj skeletal_functor

end skeletal_functor

/-- The equivalence that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletal_equivalence :
  simplex_category ≌ NonemptyFinLinOrd.{u} :=
functor.as_equivalence skeletal_functor.{u}

end skeleton

end simplex_category
