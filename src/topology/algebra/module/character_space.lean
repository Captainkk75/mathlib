/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import topology.algebra.module.weak_dual
import algebra.algebra.spectrum
import topology.continuous_function.bounded
import topology.algebra.algebra

/-!
# Character space of a topological algebra

The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. This space is used in the Gelfand transform, which gives an
isomorphism between a commutative C⋆-algebra and continuous functions on the character space
of the algebra. This, in turn, is used to construct the continuous functional calculus on
C⋆-algebras.


## Implementation notes

We define `character_space 𝕜 A` as a subset of the weak dual, which automatically puts the
correct topology on the space. We then define `to_alg_hom` which provides the algebra homomorphism
corresponding to any element. We also provide `to_clm` which provides the element as a
continuous linear map. (Even though `weak_dual 𝕜 A` is a type copy of `A →L[𝕜] 𝕜`, this is
often more convenient.)

## Tags

character space, Gelfand transform, functional calculus

-/

variables {𝕜 : Type*} {A : Type*}
open_locale bounded_continuous_function

namespace weak_dual

/-- The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. -/
def character_space (𝕜 : Type*) (A : Type*) [comm_semiring 𝕜] [topological_space 𝕜]
  [has_continuous_add 𝕜] [has_continuous_const_smul 𝕜 𝕜]
  [non_unital_non_assoc_semiring A] [topological_space A] [module 𝕜 A] :=
  {φ : weak_dual 𝕜 A | (φ ≠ 0) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))}

namespace character_space

section non_unital_non_assoc_semiring

variables [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [non_unital_non_assoc_semiring A] [topological_space A]
  [module 𝕜 A]

lemma coe_apply (φ : character_space 𝕜 A) (x : A) : (φ : weak_dual 𝕜 A) x = φ x := rfl

/-- An element of the character space, as a continuous linear map. -/
def to_clm (φ : character_space 𝕜 A) : A →L[𝕜] 𝕜 := (φ : weak_dual 𝕜 A)

lemma to_clm_apply (φ : character_space 𝕜 A) (x : A) : φ x = to_clm φ x := rfl

/-- An element of the character space, as an non-unital algebra homomorphism. -/
@[simps] def to_non_unital_alg_hom (φ : character_space 𝕜 A) : A →ₙₐ[𝕜] 𝕜 :=
{ to_fun := (φ : A → 𝕜),
  map_mul' := φ.prop.2,
  map_smul' := (to_clm φ).map_smul,
  map_zero' := continuous_linear_map.map_zero _,
  map_add' := continuous_linear_map.map_add _ }

lemma map_zero (φ : character_space 𝕜 A) : φ 0 = 0 := (to_non_unital_alg_hom φ).map_zero
lemma map_add (φ : character_space 𝕜 A) (x y : A) : φ (x + y) = φ x + φ y :=
  (to_non_unital_alg_hom φ).map_add _ _
lemma map_smul (φ : character_space 𝕜 A) (r : 𝕜) (x : A) : φ (r • x) = r • (φ x) :=
  (to_clm φ).map_smul _ _
lemma map_mul (φ : character_space 𝕜 A) (x y : A) : φ (x * y) = φ x * φ y :=
  (to_non_unital_alg_hom φ).map_mul _ _
lemma continuous (φ : character_space 𝕜 A) : continuous φ := (to_clm φ).continuous

end non_unital_non_assoc_semiring

section unital

variables [comm_ring 𝕜] [no_zero_divisors 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [topological_space A] [semiring A] [algebra 𝕜 A]

lemma map_one (φ : character_space 𝕜 A) : φ 1 = 1 :=
begin
  have h₁ : (φ 1) * (1 - φ 1) = 0 := by rw [mul_sub, sub_eq_zero, mul_one, ←map_mul φ, one_mul],
  rcases mul_eq_zero.mp h₁ with h₂|h₂,
  { exfalso,
    apply φ.prop.1,
    ext,
    rw [continuous_linear_map.zero_apply, ←one_mul x, coe_apply, map_mul φ, h₂, zero_mul] },
  { rw [sub_eq_zero] at h₂,
    exact h₂.symm },
end

@[simp] lemma map_algebra_map (φ : character_space 𝕜 A) (r : 𝕜) : φ (algebra_map 𝕜 A r) = r :=
by rw [algebra.algebra_map_eq_smul_one, map_smul, map_one, smul_eq_mul, mul_one]

/-- An element of the character space, as an algebra homomorphism. -/
@[simps] def to_alg_hom (φ : character_space 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
{ map_one' := map_one φ,
  commutes' := λ r, by
  { rw [algebra.algebra_map_eq_smul_one, algebra.id.map_eq_id, ring_hom.id_apply],
    change ((φ : weak_dual 𝕜 A) : A →L[𝕜] 𝕜) (r • 1) = r,
    rw [continuous_linear_map.map_smul, algebra.id.smul_eq_mul, coe_apply, map_one φ, mul_one] },
  ..to_non_unital_alg_hom φ }

lemma eq_set_map_one_map_mul [nontrivial 𝕜] : character_space 𝕜 A =
  {φ : weak_dual 𝕜 A | (φ 1 = 1) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))} :=
begin
  ext x,
  refine ⟨λ h, ⟨map_one ⟨x, h⟩, h.2⟩, λ h, ⟨_, h.2⟩⟩,
  rintro rfl,
  have := h.1,
  rw [continuous_linear_map.zero_apply] at this,
  exact zero_ne_one this,
end

lemma is_closed [nontrivial 𝕜] [t2_space 𝕜] [has_continuous_mul 𝕜] :
  is_closed (character_space 𝕜 A) :=
begin
  rw [eq_set_map_one_map_mul],
  refine is_closed.inter (is_closed_eq (eval_continuous _) continuous_const) _,
  change is_closed {φ : weak_dual 𝕜 A | ∀ x y : A, φ (x * y) = φ x * φ y},
  rw [set.set_of_forall],
  refine is_closed_Inter (λ a, _),
  rw [set.set_of_forall],
  exact is_closed_Inter (λ _, is_closed_eq (eval_continuous _)
    ((eval_continuous _).mul (eval_continuous _)))
end

end unital

section ring

variables [comm_ring 𝕜] [no_zero_divisors 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [topological_space A] [ring A] [algebra 𝕜 A]

lemma apply_mem_spectrum [nontrivial 𝕜] (φ : character_space 𝕜 A) (a : A) : φ a ∈ spectrum 𝕜 a :=
(to_alg_hom φ).apply_mem_spectrum a

end ring

end character_space

end weak_dual

section gelfand_transform

open weak_dual

variables [normed_field 𝕜] [topological_space A] [semiring A] [algebra 𝕜 A]
  [compact_space (character_space 𝕜 A)]

variables (𝕜) (A)

/-- The Gelfand transform of a element `a` of an algebra is the function that takes a character `φ`
and evaluates it at `a`. -/
def gelfand_transform : A →ₐ[𝕜] (character_space 𝕜 A →ᵇ 𝕜) :=
{ to_fun := λ a, bounded_continuous_function.mk_of_compact
  { to_fun := λ φ, φ a,
    continuous_to_fun := (weak_dual.eval_continuous a).comp (continuous_subtype_coe) },
  map_one' := by { ext, exact character_space.map_one _ },
  map_mul' := λ _ _, by { ext, exact character_space.map_mul _ _ _ },
  map_zero' := by { ext, exact character_space.map_zero _ },
  map_add' := λ _ _, by { ext, exact character_space.map_add _ _ _},
  commutes' := λ r, by { ext φ, exact character_space.map_algebra_map _ _ } }

/-- A type class that states that the Gelfand transform is bijective. -/
class bijective_gelfand_transform : Prop :=
(bijective : function.bijective (gelfand_transform 𝕜 A))

/-- The Gelfand transform packaged as an algebra equiv in the case when the Gelfand transform
is bijective. -/
noncomputable def gelfand_transform_equiv [bijective_gelfand_transform 𝕜 A] :
  A ≃ₐ[𝕜] (character_space 𝕜 A →ᵇ 𝕜) :=
alg_equiv.of_bijective (gelfand_transform 𝕜 A) bijective_gelfand_transform.bijective

end gelfand_transform

section continuous_functional_calculus
open weak_dual

variables [normed_field 𝕜] [topological_space A] [ring A] [topological_ring A] [algebra 𝕜 A]
  [compact_space (character_space 𝕜 A)] [bijective_gelfand_transform 𝕜 A]

variables (A)
/-- Lift a continuous function `f : 𝕜 → 𝕜` to a `𝕜`-algebra `A`. -/
noncomputable def continuous_functional_calculus : C(𝕜, 𝕜) →ₐ[𝕜] (A → A) :=
{ to_fun := λ f a, (gelfand_transform_equiv 𝕜 _).symm $ bounded_continuous_function.mk_of_compact $ f.comp $
  ((gelfand_transform_equiv 𝕜 _) a).to_continuous_map,
  map_add' := λ f g, by { ext, simp only [continuous_map.add_comp,
              bounded_continuous_function.mk_of_compact_add, map_add, pi.add_apply] },
  map_one' := by { ext, simp only [continuous_map.one_comp,
                     bounded_continuous_function.mk_of_compact_one, map_one, pi.one_apply] },
  map_zero' :=  by { ext, simp only [continuous_map.zero_comp,
             bounded_continuous_function.mk_of_compact_zero, map_zero, pi.zero_apply] },
  map_mul' := sorry,
  commutes' := sorry }

variables {A}

local notation `⇈[`:max R:max `]`:0 := continuous_functional_calculus R

--namespace continuous_functional_calculus
--
--@[simp] lemma map_add (f g : C(𝕜, 𝕜)) : ⇈[A](f + g) = ⇈[A]f + ⇈[A]g :=
--by { ext, simp only [continuous_functional_calculus, continuous_map.add_comp,
--              bounded_continuous_function.mk_of_compact_add, map_add, pi.add_apply] }
--
--@[simp] lemma map_zero : ⇈[A](0 : C(𝕜, 𝕜)) = 0 :=
--by { ext, simp only [continuous_functional_calculus, continuous_map.zero_comp,
--             bounded_continuous_function.mk_of_compact_zero, map_zero, pi.zero_apply] }
--
--@[simp] lemma map_one : ⇈[A](1 : C(𝕜, 𝕜)) = 1 :=
--by { ext, simp only [continuous_functional_calculus, continuous_map.one_comp,
--                     bounded_continuous_function.mk_of_compact_one, map_one, pi.one_apply] }
--
--@[simp] lemma map_neg (f : C(𝕜, 𝕜)) : ⇈[A](-f) = -⇈[A]f :=
--by { ext, simp only [continuous_functional_calculus, continuous_map.neg_comp,
--                     bounded_continuous_function.mk_of_compact_neg, map_neg, pi.neg_apply] }
--
--@[simp] lemma map_sub (f g : C(𝕜, 𝕜)) : ⇈[A](f - g) = ⇈[A]f - ⇈[A]g :=
--by { ext, simp only [continuous_functional_calculus, continuous_map.sub_comp,
--                     bounded_continuous_function.mk_of_compact_sub, map_sub, pi.sub_apply] }
--
--lemma map_mul (f g : C(𝕜, 𝕜)) : ⇈[A](f * g) = ⇈[A]f * ⇈[A]g := sorry
--
--end continuous_functional_calculus

end continuous_functional_calculus
