/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action.basic
import data.fintype.basic
/-!
This file defines the conjugation action of a group on its subgroups
-/

open mul_action

variables {G : Type*} [group G]

instance subgroup.mul_action' : mul_action G (subgroup G) :=
{ smul := λ g H, H.comap ((mul_aut.conj g)⁻¹).to_monoid_hom,
  one_smul := λ _, by ext; simp,
  mul_smul := λ _ _ _, by ext; simp }

namespace subgroup

lemma smul_eq_comap_conj (g : G) (H : subgroup G) :
  g • H = H.comap ((mul_aut.conj g)⁻¹).to_monoid_hom := rfl

lemma smul_eq_map_conj (g : G) (H : subgroup G) :
  g • H = H.map (mul_aut.conj g).to_monoid_hom :=
begin
  ext,
  simp only [smul_eq_comap_conj, subgroup.mem_comap, subgroup.mem_map, exists_prop, mul_equiv.coe_to_monoid_hom,
    mul_aut.conj_apply, mul_aut.conj_inv_apply, monoid_hom.map_inv],
  exact ⟨λ h, ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩,
    by rintros ⟨y, hy, rfl⟩; simp [mul_assoc, *]⟩
end

@[simp] lemma mem_smul (g h : G) (H : subgroup G) :
  h ∈ (g • H) ↔ g⁻¹ * h * g ∈ H :=
by simp [smul_eq_comap_conj]

instance decidable_mem_smul (g : G) (H : subgroup G) [decidable_pred (∈ H)] :
  decidable_pred (∈ g • H) :=
λ h, decidable_of_iff _ (mem_smul g h H).symm

/-- A subgroup is isomorphic to its conjugates -/
noncomputable def equiv_smul [fintype G] (g : G) (H : subgroup G) : H ≃* (g • H : subgroup G) :=
eq.rec_on (smul_eq_map_conj g H).symm
  (H.equiv_map_of_injective (mul_aut.conj g).to_monoid_hom (mul_aut.conj g).injective)

@[simp] lemma card_smul [fintype G] (g : G) (H : subgroup G)
  [decidable_pred (∈ H)] {h : fintype ↥(g • H : subgroup G)} :
  fintype.card (g • H : subgroup G) = fintype.card H :=
fintype.card_congr (equiv_smul _ _).to_equiv.symm

lemma smul_eq_self_of_mem {H : subgroup G} {x : G} (hx : x ∈ H) : x • H = H :=
subgroup.ext (λ _, by simp [*, mul_mem_cancel_left, mul_mem_cancel_right] at *)

@[simp] lemma smul_self {H : subgroup G} (x : H) : x • H = H :=
smul_eq_self_of_mem x.2

lemma smul_le_iff_le_smul {g : G} {H K : subgroup G} : g • H ≤ K ↔ H ≤ g⁻¹ • K :=
begin
  simp only [set_like.le_def, mem_smul],
  exact ⟨λ h x hx, h (by simpa [mul_assoc] using hx),
         λ h x hx, by simpa [mul_assoc] using h hx⟩
end

section map_comap
variables {H : Type*} [group H] (f : G →* H)

@[simp] lemma map_smul (g : G) (K : subgroup G) : map f (g • K) = f g • map f K :=
begin
  rw [smul_eq_map_conj, smul_eq_map_conj, map_map, map_map],
  congr,
  ext,
  simp,
end

@[simp] lemma comap_smul (g : G) (K : subgroup H) : comap f (f g • K) = g • comap f K :=
begin
  rw [smul_eq_comap_conj, smul_eq_comap_conj, comap_comap, comap_comap],
  congr,
  ext,
  simp,
end

end map_comap

/-- The stabilizer of a subgroup under the conjugation action is the normalizer. -/
lemma stabilizer_eq_normalizer (H : subgroup G) :
  stabilizer G H = normalizer H :=
subgroup.ext $ λ x,
  begin
    rw [mem_stabilizer_iff, mem_normalizer_iff, ← smul_left_cancel_iff (x⁻¹),
      inv_smul_smul, set_like.ext_iff],
    simp
  end

/-- A subgroup is contained in its own stabilizer under the conjugation action -/
lemma le_stabilizer_self (H : subgroup G) : H ≤ stabilizer G H :=
by rw [stabilizer_eq_normalizer]; exact le_normalizer

/-- A subgroup is a fixed point of the conjugation action iff it is normal -/
lemma mem_fixed_points_iff_normal (H : subgroup G) :
  H ∈ fixed_points G (subgroup G) ↔ normal H :=
by simp only [mem_fixed_points_iff_stabilizer_eq_top,
  stabilizer_eq_normalizer, normal_iff_normalizer_eq_top]

@[simp] lemma normalizer_smul (g : G) (H : subgroup G) :
  normalizer (g • H) = g • normalizer H :=
by rw [smul_eq_map_conj, smul_eq_map_conj, map_equiv_normalizer_eq]

end subgroup
