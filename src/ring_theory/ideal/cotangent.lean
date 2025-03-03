/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.ideal.operations
import algebra.module.torsion
import algebra.ring.idempotents
import linear_algebra.finite_dimensional
import ring_theory.ideal.local_ring
import ring_theory.nakayama

/-!
# The module `I ⧸ I ^ 2`

In this file, we provide special API support for the module `I ⧸ I ^ 2`. The official
definition is a quotient module of `I`, but the alternative definition as an ideal of `R ⧸ I ^ 2` is
also given, and the two are `R`-equivalent as in `ideal.cotangent_equiv_ideal`.

Additional support is also given to the cotangent space `m ⧸ m ^ 2` of a local ring.

-/

namespace ideal

variables {R S : Type*} [comm_ring R] [comm_semiring S] [algebra S R] (I : ideal R)

/-- `I ⧸ I ^ 2` as a quotient of `I`. -/
@[derive [add_comm_group, module (R ⧸ I)]]
def cotangent : Type* := I ⧸ (I • ⊤ : submodule R I)

instance : inhabited I.cotangent := ⟨0⟩

instance cotangent.module_of_tower : module S I.cotangent :=
submodule.quotient.module' _

instance : is_scalar_tower S R I.cotangent := by { delta cotangent, apply_instance }

instance [is_noetherian R I] : is_noetherian R I.cotangent := by { delta cotangent, apply_instance }

/-- The quotient map from `I` to `I ⧸ I ^ 2`. -/
@[simps apply (lemmas_only)]
def to_cotangent : I →ₗ[R] I.cotangent := submodule.mkq _

lemma map_to_cotangent_ker : I.to_cotangent.ker.map I.subtype = I ^ 2 :=
by simp [ideal.to_cotangent, submodule.map_smul'', pow_two]

lemma mem_to_cotangent_ker {x : I} : x ∈ I.to_cotangent.ker ↔ (x : R) ∈ I ^ 2 :=
begin
  rw ← I.map_to_cotangent_ker,
  simp,
end

lemma to_cotangent_eq {x y : I} : I.to_cotangent x = I.to_cotangent y ↔ (x - y : R) ∈ I ^ 2 :=
begin
  rw [← sub_eq_zero, ← map_sub],
  exact I.mem_to_cotangent_ker
end

lemma to_cotangent_eq_zero (x : I) : I.to_cotangent x = 0 ↔ (x : R) ∈ I ^ 2 :=
I.mem_to_cotangent_ker

lemma to_cotangent_surjective : function.surjective I.to_cotangent :=
submodule.mkq_surjective _

lemma to_cotangent_range : I.to_cotangent.range = ⊤ :=
submodule.range_mkq _

lemma cotangent_subsingleton_iff :
  subsingleton I.cotangent ↔ is_idempotent_elem I :=
begin
  split,
  { introI H,
    refine (pow_two I).symm.trans (le_antisymm (ideal.pow_le_self two_ne_zero) _),
    exact λ x hx, (I.to_cotangent_eq_zero ⟨x, hx⟩).mp (subsingleton.elim _ _) },
  { exact λ e, ⟨λ x y, quotient.induction_on₂' x y $ λ x y,
      I.to_cotangent_eq.mpr $ ((pow_two I).trans e).symm ▸ I.sub_mem x.prop y.prop⟩ }
end

/-- The inclusion map `I ⧸ I ^ 2` to `R ⧸ I ^ 2`. -/
def cotangent_to_quotient_square : I.cotangent →ₗ[R] R ⧸ I ^ 2 :=
submodule.mapq (I • ⊤) (I ^ 2) I.subtype
  (by { rw [← submodule.map_le_iff_le_comap, submodule.map_smul'', submodule.map_top,
    submodule.range_subtype, smul_eq_mul, pow_two], exact rfl.le })

lemma to_quotient_square_comp_to_cotangent : I.cotangent_to_quotient_square.comp I.to_cotangent =
  (I ^ 2).mkq.comp (submodule.subtype I) :=
linear_map.ext $ λ _, rfl

@[simp]
lemma to_cotangent_to_quotient_square (x : I) : I.cotangent_to_quotient_square (I.to_cotangent x) =
  (I ^ 2).mkq x := rfl

/-- `I ⧸ I ^ 2` as an ideal of `R ⧸ I ^ 2`. -/
def cotangent_ideal (I : ideal R) : ideal (R ⧸ I ^ 2) :=
begin
  haveI : @ring_hom_surjective R (R ⧸ I ^ 2) _ _ _ := ⟨ideal.quotient.mk_surjective⟩,
  exact submodule.map (ring_hom.to_semilinear_map (I ^ 2)^.quotient.mk) I,
end

lemma to_quotient_square_range :
  I.cotangent_to_quotient_square.range = I.cotangent_ideal.restrict_scalars R :=
begin
  transitivity (I.cotangent_to_quotient_square.comp I.to_cotangent).range,
  { rw [linear_map.range_comp, I.to_cotangent_range, submodule.map_top] },
  { rw [to_quotient_square_comp_to_cotangent, linear_map.range_comp, I.range_subtype], ext, refl }
end

/-- The equivalence of the two definitions of `I / I ^ 2`, either as the quotient of `I` or the
ideal of `R / I ^ 2`. -/
noncomputable
def cotangent_equiv_ideal : I.cotangent ≃ₗ[R] I.cotangent_ideal :=
begin
  refine
  { ..(I.cotangent_to_quotient_square.cod_restrict (I.cotangent_ideal.restrict_scalars R)
    (λ x, by { rw ← to_quotient_square_range, exact linear_map.mem_range_self _ _ })),
    ..(equiv.of_bijective _ ⟨_, _⟩) },
  { rintros x y e,
    replace e := congr_arg subtype.val e,
    obtain ⟨x, rfl⟩ := I.to_cotangent_surjective x,
    obtain ⟨y, rfl⟩ := I.to_cotangent_surjective y,
    rw I.to_cotangent_eq,
    dsimp only [to_cotangent_to_quotient_square, submodule.mkq_apply] at e,
    rwa submodule.quotient.eq at e },
  { rintro ⟨_, x, hx, rfl⟩,
    refine ⟨I.to_cotangent ⟨x, hx⟩, subtype.ext rfl⟩ }
end

@[simp, nolint simp_nf]
lemma cotangent_equiv_ideal_apply (x : I.cotangent) :
  ↑(I.cotangent_equiv_ideal x) = I.cotangent_to_quotient_square x := rfl

lemma cotangent_equiv_ideal_symm_apply (x : R) (hx : x ∈ I) :
  I.cotangent_equiv_ideal.symm ⟨(I ^ 2).mkq x, submodule.mem_map_of_mem hx⟩ =
    I.to_cotangent ⟨x, hx⟩ :=
begin
  apply I.cotangent_equiv_ideal.injective,
  rw I.cotangent_equiv_ideal.apply_symm_apply,
  ext,
  refl
end

end ideal

namespace local_ring

variables (R : Type*) [comm_ring R] [local_ring R]

/-- The `A ⧸ I`-vector space `I ⧸ I ^ 2`. -/
@[reducible] def cotangent_space : Type* := (maximal_ideal R).cotangent

instance : module (residue_field R) (cotangent_space R) :=
ideal.cotangent.module _

instance : is_scalar_tower R (residue_field R) (cotangent_space R) :=
module.is_torsion_by_set.is_scalar_tower _

instance [is_noetherian_ring R] : finite_dimensional (residue_field R) (cotangent_space R) :=
module.finite.of_restrict_scalars_finite R _ _

end local_ring
