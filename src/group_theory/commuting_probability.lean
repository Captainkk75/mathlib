/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import group_theory.complement
import group_theory.group_action.conj_act
import group_theory.index
import group_theory.solvable

/-!
# Commuting Probability
This file introduces the commuting probability of finite groups.

## Main definitions
* `comm_prob`: The commuting probability of a finite type with a multiplication operation.

## Todo
* Neumann's theorem.
-/

section for_mathlib

/-lemma subgroup.mem_centralizer_iff_commutator_eq_one {G : Type*} [group G] {H : subgroup G} {g : G} :
  g ∈ H.centralizer ↔ ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ = 1 :=
by simp_rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, subgroup.mem_centralizer_iff, eq_comm]-/

@[to_additive] instance subgroup.centralizer.characteristic
  {G : Type*} [group G] (H : subgroup G) [H.characteristic] :
  H.centralizer.characteristic := sorry

instance subgroup.commutator.characteristic (G : Type*) [group G] :
  (commutator G).characteristic := sorry

lemma general_commutator_eq_bot_iff_le_centralizer {G : Type*} [group G] {H K : subgroup G} :
  ⁅H, K⁆ = ⊥ ↔ H ≤ K.centralizer :=
sorry

lemma general_commutator_le_commutator {G : Type*} [group G] (H K : subgroup G) :
  ⁅H, K⁆ ≤ commutator G := sorry

lemma centralizer_top_eq_center (G : Type*) [group G] :
  (⊤ : subgroup G).centralizer = subgroup.center G :=
begin
  sorry
end

lemma centralizer_mono {G : Type*} [group G] {H K : subgroup G} (h : H ≤ K) :
  K.centralizer ≤ H.centralizer := sorry

instance commutator_element {G : Type*} [group G] : has_bracket G G :=
⟨λ g₁ g₂, g₁ * g₂ * g₁⁻¹ * g₂⁻¹⟩

lemma three_subgroups_lemma {G : Type*} [group G] {X Y Z : subgroup G}
  (h1 : ⁅⁅X, Y⁆, Z⁆ = ⊥) (h2 : ⁅⁅Y, Z⁆, X⁆ = ⊥) : ⁅⁅Z, X⁆, Y⁆ = ⊥ :=
begin
  rw [general_commutator_eq_bot_iff_le_centralizer, general_commutator_le] at h1 h2 ⊢,
  simp_rw [subgroup.mem_centralizer_iff_commutator_eq_one] at h1 h2 ⊢,
  intros z hz x hx y hy,
  change ⁅y, ⁅z, x⁆⁆ = _,
  change ∀ (x ∈ X) (y ∈ Y) (z ∈ Z), ⁅z, ⁅x, y⁆⁆ = (1 : G) at h1,
  change ∀ (y ∈ Y) (z ∈ Z) (x ∈ X), ⁅x, ⁅y, z⁆⁆ = (1 : G) at h2,
  have key : ⁅y, ⁅z, x⁆⁆ = z * y * ⁅x, ⁅y⁻¹, z⁻¹⁆⁆⁻¹ * y⁻¹ * x * ⁅z⁻¹, ⁅x⁻¹, y⁆⁆⁻¹ * x⁻¹ * z⁻¹ :=
  by { dsimp only [commutator_element], group, },
  rw [key, h2 _ (Y.inv_mem hy) _ (Z.inv_mem hz) x hx, h1 _ (X.inv_mem hx) y hy _ (Z.inv_mem hz),
      one_inv, mul_one, mul_one, mul_inv_cancel_right, mul_inv_cancel_right, mul_inv_self],
end

lemma commutator_centralizer_commutator_le_center (G : Type*) [group G] :
  ⁅(commutator G).centralizer, (commutator G).centralizer⁆ ≤ subgroup.center G :=
begin
  rw [←centralizer_top_eq_center, ←general_commutator_eq_bot_iff_le_centralizer],
  suffices : ⁅⁅⊤, (commutator G).centralizer⁆, (commutator G).centralizer⁆ = ⊥,
  { exact three_subgroups_lemma (by rwa general_commutator_comm (commutator G).centralizer) this },
  rw [general_commutator_comm, general_commutator_eq_bot_iff_le_centralizer],
  apply centralizer_mono,
  apply general_commutator_le_commutator,
end

lemma subgroup.map_subtype_le_map_subtype {G' : Type*} [group G'] {G : subgroup G'}
  {H K : subgroup G} : H.map G.subtype ≤ K.map G.subtype ↔ H ≤ K :=
subgroup.map_le_map_iff_of_injective subtype.coe_injective

lemma map_commutator_eq_general_commutator {G H : Type*} [group G] [group H] (ϕ : G →* H) :
  (commutator G).map ϕ = ⁅ϕ.range, ϕ.range⁆ :=
sorry

lemma subgroup.commutator_eq_general_commutator {G : Type*} [group G] (H : subgroup G) :
  (commutator H).map H.subtype = ⁅H, H⁆ :=
by rw [map_commutator_eq_general_commutator, subgroup.subtype_range]

lemma general_commutator_map {G G' : Type*} [group G] [group G'] (ϕ : G →* G') {H K : subgroup G} :
  ⁅H, K⁆.map ϕ = ⁅H.map ϕ, K.map ϕ⁆ :=
begin
  sorry
end

lemma map_center_map {G : Type*} [group G] (H : subgroup G) (K : subgroup H) :
  (subgroup.center (K.map H.subtype)).map (subgroup.subtype _) =
    (K.center.map K.subtype).map H.subtype :=
begin
  sorry
end

end for_mathlib

noncomputable theory
open_locale classical
open_locale big_operators

open fintype

section technical

open_locale pointwise

namespace mem_left_transversals

def to_equiv {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.left_transversals (H : set G)) : G ⧸ H ≃ S :=
(equiv.of_bijective _ (subgroup.mem_left_transversals_iff_bijective.mp hS)).symm

lemma mk'_to_equiv {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.left_transversals (H : set G)) (q : G ⧸ H) :
  quotient.mk' (to_equiv hS q : G) = q :=
(to_equiv hS).symm_apply_apply q

def to_fun {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.left_transversals (H : set G)) : G → S :=
to_equiv hS ∘ quotient.mk'

lemma to_fun_inv_mul {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.left_transversals (H : set G)) (g : G) : (to_fun hS g : G)⁻¹ * g ∈ H :=
quotient.exact' (mk'_to_equiv hS g)

end mem_left_transversals

namespace mem_right_transversals

def to_equiv {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.right_transversals (H : set G)) : quotient (quotient_group.right_rel H) ≃ S :=
(equiv.of_bijective _ (subgroup.mem_right_transversals_iff_bijective.mp hS)).symm

lemma mk'_to_equiv {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.right_transversals (H : set G)) (q : quotient (quotient_group.right_rel H)) :
  quotient.mk' (to_equiv hS q : G) = q :=
(to_equiv hS).symm_apply_apply q

def to_fun {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.right_transversals (H : set G)) : G → S :=
to_equiv hS ∘ quotient.mk'

lemma to_fun_mul_inv {G : Type*} [group G] {H : subgroup G} {S : set G}
  (hS : S ∈ subgroup.right_transversals (H : set G)) (g : G) : g * (to_fun hS g : G)⁻¹ ∈ H :=
quotient.exact' (mk'_to_equiv hS _)

end mem_right_transversals

/-- **Schreier's Lemma** -/
lemma schreier' {G : Type*} [group G] {H : subgroup G} {R S : set G}
  (hR : R ∈ subgroup.right_transversals (H : set G)) (hS : subgroup.closure S = ⊤) :
  subgroup.closure ((R * S).image (λ g, (⟨g * (mem_right_transversals.to_fun hR g)⁻¹,
    mem_right_transversals.to_fun_mul_inv hR g⟩ : H))) =
    (⊤ : subgroup H) :=
begin
  sorry
end

/-- **Schreier's Lemma** -/
lemma schreier {G : Type*} [group G] {H : subgroup G} {R S : set G}
  (hR : R ∈ subgroup.right_transversals (H : set G)) (hS : subgroup.closure S = ⊤) :
  subgroup.closure ((R * S).image (λ g, g * (mem_right_transversals.to_fun hR g)⁻¹)) = H :=
begin
  conv_rhs { rw [←H.subtype_range] },
  rw [monoid_hom.range_eq_map, ←schreier' hR hS, monoid_hom.map_closure],
  apply congr_arg subgroup.closure,
  simp only [set.ext_iff],
  simp only [set.mem_image, subgroup.coe_subtype, exists_exists_and_eq_and, subgroup.coe_mk, iff_self, forall_const],
end

def generated_by (G : Type*) [group G] (n : ℕ) :=
∃ S : set G, subgroup.closure S = ⊤ ∧ ∃ hS, @fintype.card S hS ≤ n

def schreier_bound : ℕ → ℕ → ℕ := (*)

lemma fintype.card_image_le {α β : Type*} (f : α → β) (s : set α) [fintype s] :
  fintype.card (f '' s) ≤ fintype.card s :=
fintype.card_le_of_surjective (s.image_factorization f) set.surjective_onto_image

lemma fintype.card_image2_le {α β γ : Type*} (f : α → β → γ) (s : set α) (t : set β) [fintype s] [fintype t] :
  fintype.card (set.image2 f s t) ≤ fintype.card s * fintype.card t :=
sorry

def card_mul_le {α : Type*} [has_mul α] [decidable_eq α] (s t : set α) [hs : fintype s] [ht : fintype t] :
  card (s * t : set α) ≤ card s * card t :=
by convert fintype.card_image2_le _ s t

lemma schreier'' {m n : ℕ} {G : Type*} [group G] {H : subgroup G}
  (h1 : H.index ≤ m) (h2 : generated_by G n) : generated_by H (schreier_bound m n) :=
begin
  obtain ⟨R, hR⟩ := @subgroup.right_transversals.inhabited G _ H,
  obtain ⟨S, hS, hS_fintype, hS_card⟩ := h2,
  haveI : fintype (quotient (quotient_group.right_rel H)) := sorry,
  haveI : fintype R := fintype.of_equiv _ (mem_right_transversals.to_equiv hR),
  haveI : fintype S := hS_fintype,
  let T : set G := R * S,
  let f : G → H := λ g, (⟨g * (mem_right_transversals.to_fun hR g)⁻¹,
    mem_right_transversals.to_fun_mul_inv hR g⟩ : H),

  refine ⟨_, schreier' hR hS, by apply_instance, _⟩,
  change card (f '' T) ≤ schreier_bound m n,
  have key := fintype.card_image_le f T,
  convert key.trans _,
  convert (card_mul_le R S).trans _,
  convert mul_le_mul' _ hS_card,
end

end technical

variables (M : Type*) [fintype M] [has_mul M]

/-- The commuting probability of a finite type with a multiplication operation -/
def comm_prob : ℚ := card {p : M × M // p.1 * p.2 = p.2 * p.1} / card M ^ 2

lemma comm_prob_def : comm_prob M = card {p : M × M // p.1 * p.2 = p.2 * p.1} / card M ^ 2 :=
rfl

lemma comm_prob_pos [h : nonempty M] : 0 < comm_prob M :=
h.elim (λ x, div_pos (nat.cast_pos.mpr (card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
  (pow_pos (nat.cast_pos.mpr card_pos) 2))

lemma comm_prob_le_one : comm_prob M ≤ 1 :=
begin
  refine div_le_one_of_le _ (sq_nonneg (card M)),
  rw [←nat.cast_pow, nat.cast_le, sq, ←card_prod],
  apply set_fintype_card_le_univ,
end

variables {M}

lemma comm_prob_eq_one_iff [h : nonempty M] : comm_prob M = 1 ↔ commutative ((*) : M → M → M) :=
begin
  change (card {p : M × M | p.1 * p.2 = p.2 * p.1} : ℚ) / _ = 1 ↔ _,
  rw [div_eq_one_iff_eq, ←nat.cast_pow, nat.cast_inj, sq, ←card_prod,
      set_fintype_card_eq_univ_iff, set.eq_univ_iff_forall],
  { exact ⟨λ h x y, h (x, y), λ h x, h x.1 x.2⟩ },
  { exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero) },
end

variables (G : Type*) [group G] [fintype G]

lemma card_comm_eq_card_conj_classes_mul_card :
  card {p : G × G // p.1 * p.2 = p.2 * p.1} = card (conj_classes G) * card G :=
calc card {p : G × G // p.1 * p.2 = p.2 * p.1} = card (Σ g, {h // g * h = h * g}) :
  card_congr (equiv.subtype_prod_equiv_sigma_subtype (λ g h : G, g * h = h * g))
... = ∑ g, card {h // g * h = h * g} : card_sigma _
... = ∑ g, card (mul_action.fixed_by (conj_act G) G g) : sum_equiv conj_act.to_conj_act.to_equiv
  _ _ (λ g, card_congr' $ congr_arg _ $ funext $ λ h, mul_inv_eq_iff_eq_mul.symm.to_eq)
... = card (quotient (mul_action.orbit_rel (conj_act G) G)) * card G :
  mul_action.sum_card_fixed_by_eq_card_orbits_mul_card_group (conj_act G) G
... = card (quotient (is_conj.setoid G)) * card G :
  have this : mul_action.orbit_rel (conj_act G) G = is_conj.setoid G :=
    setoid.ext (λ g h, (setoid.comm' _).trans is_conj_iff.symm),
  by cc

lemma comm_prob_def' : comm_prob G = card (conj_classes G) / card G :=
begin
  rw [comm_prob, card_comm_eq_card_conj_classes_mul_card, nat.cast_mul, sq],
  exact mul_div_mul_right (card (conj_classes G)) (card G) (nat.cast_ne_zero.mpr card_ne_zero),
end

variables {G} (H : subgroup G)

lemma subgroup.comm_prob_subgroup_le : comm_prob H ≤ comm_prob G * H.index ^ 2 :=
begin
  /- After rewriting with `comm_prob_def`, we reduce to showing that `G` has at least as many
    commuting pairs as `H`. -/
  rw [comm_prob_def, comm_prob_def, div_le_iff, mul_assoc, ←mul_pow, ←nat.cast_mul,
      H.index_mul_card, div_mul_cancel, nat.cast_le],
  { apply card_le_of_injective _ _,
    exact λ p, ⟨⟨p.1.1, p.1.2⟩, subtype.ext_iff.mp p.2⟩,
    exact λ p q h, by simpa only [subtype.ext_iff, prod.ext_iff] using h },
  { exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero) },
  { exact pow_pos (nat.cast_pos.mpr card_pos) 2 },
end

lemma subgroup.comm_prob_quotient_le [H.normal] : comm_prob (G ⧸ H) ≤ comm_prob G * card H :=
begin
  /- After rewriting with `comm_prob_def'`, we reduce to showing that `G` has at least as many
    conjugacy classes as `G ⧸ H`. -/
  rw [comm_prob_def', comm_prob_def', div_le_iff, mul_assoc, ←nat.cast_mul, mul_comm (card H),
      ←subgroup.card_eq_card_quotient_mul_card_subgroup, div_mul_cancel, nat.cast_le],
  { exact card_le_of_surjective (conj_classes.map (quotient_group.mk' H))
      (conj_classes.map_surjective quotient.surjective_quotient_mk') },
  { exact nat.cast_ne_zero.mpr card_ne_zero },
  { exact nat.cast_pos.mpr card_pos },
end

variables (G)

lemma inv_card_commutator_le_comm_prob : (↑(card (commutator G)))⁻¹ ≤ comm_prob G :=
(inv_pos_le_iff_one_le_mul (by exact nat.cast_pos.mpr card_pos)).mpr
  (le_trans (ge_of_eq (comm_prob_eq_one_iff.mpr (abelianization.comm_group G).mul_comm))
    (commutator G).comm_prob_quotient_le)

section neumann

def weak_neumann_commutator_bound : ℚ → ℕ := sorry

def weak_neumann_commutator_index_bound : ℚ → ℕ := sorry

lemma weak_neumann :
  ∃ K : subgroup G, K.normal ∧
  card (commutator K) ≤ weak_neumann_commutator_bound (comm_prob G)
  ∧ K.index ≤ weak_neumann_commutator_index_bound (comm_prob G) :=
begin
  sorry
end

def strong_neumann_commutator_bound : ℚ → ℕ := weak_neumann_commutator_bound

def strong_neumann_commutator_index_bound : ℚ → ℕ :=
λ q, weak_neumann_commutator_index_bound q * (weak_neumann_commutator_bound q).factorial

lemma strong_neumann :
  ∃ K : subgroup G, K.normal ∧ commutator K ≤ K.center ∧
  card (commutator K) ≤ strong_neumann_commutator_bound (comm_prob G)
  ∧ K.index ≤ strong_neumann_commutator_index_bound (comm_prob G) :=
begin
  obtain ⟨K, hK1, hK2, hK3⟩ := weak_neumann G,
  refine ⟨(commutator K).centralizer.map K.subtype, _, _, _, _⟩,
  { haveI : (commutator K).characteristic := by apply_instance,
    -- why doesn't apply_instance work directly?
    apply_instance },
  { rw [←subgroup.map_subtype_le_map_subtype, subgroup.commutator_eq_general_commutator,
        ←general_commutator_map, map_center_map, subgroup.map_subtype_le_map_subtype],
    refine (commutator_centralizer_commutator_le_center K).trans _,
    refine λ a ha, ⟨⟨a, λ b hb, ha b⟩, λ b, subtype.ext (ha b), rfl⟩, },
  { refine le_trans _ hK2,
    refine nat.le_of_dvd card_pos _,
    have key : ∀ H : subgroup G, card (commutator H) =
      card ↥⁅H, H⁆,
    { intro H,
      rw ← subgroup.commutator_eq_general_commutator,
      exact fintype.card_congr
        ((commutator H).equiv_map_of_injective H.subtype subtype.coe_injective).to_equiv },
    rw [key, key],
    apply subgroup.card_dvd_of_le,
    apply general_commutator_mono (commutator ↥K).centralizer.map_subtype_le
      (commutator ↥K).centralizer.map_subtype_le },
  { sorry },
end

end neumann
