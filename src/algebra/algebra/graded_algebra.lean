/-
Copyright (c) 2019 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum
import linear_algebra.direct_sum_module
import algebra.algebra.basic
import algebra.algebra.subalgebra

import algebra.algebra.basic
import linear_algebra.finsupp

/-!
# Graded algebras

When the domain of a `direct_sum` has an additive structure, the indexed types are submodule,
and the convolution product of `add_monoid_algebra` respects the indices of those types, we can
lift the convolution product to the direct sum `⨁ i, g.submodules i`.

## Implementation notes

This defines a struct `grading R A` which defines a grading over an algebra `A`. When coerced to
a type with `has_coe_to_sort`, a grading `g` becomes a `⨁ i, G.submodules i` endowed with a product
that preserves the grading and is equivalent to the product on `A`.

Note that gradings are not unique - any algebra can be graded as lying solely within grade 0.
-/
variables
  (R : Type*) [comm_semiring R] (A : Type*) [semiring A] [algebra R A]
  (ι : Type*) [add_comm_monoid ι] [decidable_eq ι] [Π (x : A), decidable (x ≠ 0)]

open_locale direct_sum

lemma linear_map.idem_iff_id {M : Type*} [add_comm_monoid M] [semimodule R M] (f : M →ₗ[R] M) :
  (∀ a, f a = a) ↔ f = linear_map.id :=
⟨λ hm, linear_map.ext hm, λ h, h.symm ▸ λ a, rfl⟩

@[simp]
lemma dfinsupp.lsum_apply_to_add_monoid_hom
  (β : ι → Type*) {γ : Type*}
  [Π (i : ι), add_comm_monoid (β i)] [Π (i : ι), semimodule R (β i)]
  [add_comm_monoid γ] [semimodule R γ] (F) :
  (dfinsupp.lsum F : (Π₀ i, β i) →ₗ[R] γ).to_add_monoid_hom = dfinsupp.lift_add_hom (λ i, (F i).to_add_monoid_hom) :=
rfl

section
variables {ι}
def dfinsupp.leval'
  (β : ι → Type*) [Π (i : ι), add_comm_monoid (β i)] [Π (i : ι), semimodule R (β i)] (i : ι) :
  (Π₀ i, β i) →ₗ[R] β i :=
{ to_fun := λ f, f i,
  map_add' := λ _ _, dfinsupp.add_apply _ _ i,
  map_smul' := λ _ _, dfinsupp.smul_apply _ _ i}
end

structure grading :=
(submodules : ι → submodule R A)
(one_mem : (1 : A) ∈ submodules 0)
(mul_mem : ∀ {i j} (gi : submodules i) (gj : submodules j), (gi * gj : A) ∈ submodules (i + j))

namespace grading

variables {R A ι} (G : grading R A ι)


@[reducible]
def submodule_types (i : ι) := ↥(G.submodules i)

local notation g `[`:max i `]`:max := submodule_types g i

instance : has_coe_to_sort (grading R A ι) := ⟨_, λ g, ⨁ i, g[i]⟩

instance : add_comm_monoid G := infer_instance
instance : semimodule R G := infer_instance
instance : add_comm_monoid (Π₀ (i : ι), G[i]) := (@dfinsupp.add_comm_monoid ι G.submodule_types _)
instance : semimodule R (Π₀ (i : ι), G[i]) := (@dfinsupp.semimodule ι G.submodule_types R _ _ _)

-- TODO: move, or use classical
instance (S : submodule R A) (x : S) : decidable (x ≠ 0) :=
decidable.rec_on (infer_instance : decidable ((x : A) ≠ 0))
  (λ hfalse, decidable.is_false $ by simp * at *)
  (λ htrue, decidable.is_true $ by simp * at *)

section semiring

def lmul {i j} : G[i] →ₗ[R] G[j] →ₗ[R] G[i+j] :=
linear_map.mk₂ R (λ gi gj, ⟨gi * gj, G.mul_mem _ _⟩)
  (λ gi₁ gi₂ gj, subtype.eq $ add_mul _ _ _)
  (λ c gi gj, subtype.eq $ algebra.smul_mul_assoc _ _ _)
  (λ gi gj₁ gj₂, subtype.eq $ mul_add _ _ _)
  (λ c gi gj, subtype.eq $ algebra.mul_smul_comm _ _ _)

def lone : G[0] := ⟨1, G.one_mem⟩

lemma one_lmul {i} (a : G[i]) : G.lmul (lone G) a == a := begin
  have : ∀ x, x ∈ G.submodules (0 + i) ↔ x ∈ G.submodules i := λ x, by rw zero_add,
  rw subtype.heq_iff_coe_eq this,
  simp only [lmul, lone, linear_map.mk₂_apply, submodule.coe_mk,  one_mul],
end

lemma lmul_one {i} (a : G[i]) : G.lmul a (lone G) == a := begin
  have : ∀ x, x ∈ G.submodules (i + 0) ↔ x ∈ G.submodules i := λ x, by rw add_zero,
  rw subtype.heq_iff_coe_eq this,
  simp only [lmul, lone, linear_map.mk₂_apply, submodule.coe_mk, mul_one],
end

lemma lmul_assoc {i j k} (a : G[i]) (b : G[j]) (c : G[k]) : G.lmul a (G.lmul b c) == G.lmul (G.lmul a b) c := begin
  have : ∀ x, x ∈ G.submodules (i + (j + k)) ↔ x ∈ G.submodules (i + j + k) := λ x, by rw add_assoc,
  rw subtype.heq_iff_coe_eq this,
  simp only [lmul, linear_map.mk₂_apply, submodule.coe_mk, mul_assoc],
end

@[simps mul]
instance : has_mul G :=
⟨λ x y,
  (dfinsupp.lsum $ λ j,
    (dfinsupp.lsum $ λ i,
      (G.lmul : G[i] →ₗ[R] G[j] →ₗ[R] G[_]).compr₂ (dfinsupp.lsingle _ : G[_] →ₗ[R] _))
    x)
  y⟩

#check dfinsupp.sum_apply

@[simps one]
instance : has_one G :=
⟨(dfinsupp.lsingle 0 : _ →ₗ[R] _) (lone G)⟩

/-! These proofs are very slow, so these lemmas are defined separately -/

private lemma one_mul (a : G) : 1 * a = a :=
begin
  suffices : ∀ i xi, dfinsupp.single (0 + i) (G.lmul G.lone xi) = dfinsupp.single i xi,
  {
    simp_rw [has_mul_mul, has_one_one],
    revert a,
    rw linear_map.idem_iff_id,
    rw ←dfinsupp.lsum_lsingle,
    congr' 1,
    ext1 i, ext1 xi,
    rw [dfinsupp.lsingle_apply, dfinsupp.lsum_apply_single],
    exact this _ _,
  },
  intros i xi,
  have := zero_add i,
  congr,
  exact this,
  exact one_lmul G xi,
end


private lemma mul_one : ∀ (a : G), a * 1= a :=
begin
  suffices : ∀ i xi, dfinsupp.single (i + 0) (G.lmul xi G.lone) = dfinsupp.single i xi,
  {
    -- simp_rw [has_mul_mul, has_one_one],
    -- simp_rw [dfinsupp.lsingle_apply, dfinsupp.lsum_apply_single],
    -- intro a,
    -- rw ←linear_map.flip_apply,
    -- simp only [dfinsupp.lsum_apply, linear_map.compr₂_apply,
    --   dfinsupp.linear_map.dfinsupp_sum_apply, dfinsupp.lsingle_apply, linear_map.flip_apply],
    -- convert dfinsupp.sum_single,
    -- ext1 i, ext1 xi,
    -- exact this _ _,
    -- classical,
    -- apply_instance,
    sorry,
  },
  intros i xi,
  apply dfinsupp.single_eq_single_iff,
  -- have := add_zero i,
  -- congr,
  -- exact this,
  -- exact lmul_one G xi,
end

#print linear_map.flip


#check dfinsupp.single_eq_single_iff
-- private lemma mul_one (a : G) : a * 1 = a := begin
--   simp only [has_mul_mul, has_one_one, direct_sum.of, add_monoid_hom.coe_mk],
--   convert @dfinsupp.sum_single ι _ _ _ _ a,
--   ext1 i, ext1,
--   rw dfinsupp.sum_single_index,
--   { congr, exact add_zero i,
--     rw subtype.heq_iff_coe_eq,
--     { rw [submodule.coe_mk, submodule.coe_mk, mul_one], },
--     { intro x, rw add_zero }, },
--   { convert @dfinsupp.single_zero ι _ _ _ _,
--     rw [submodule.coe_zero, mul_zero], }
-- end

-- private lemma zero_mul (a : G) : 0 * a = 0 := by { rw has_mul_mul, exact dfinsupp.sum_zero_index }

-- private lemma mul_zero (a : G) : a * 0 = 0 := by { rw has_mul_mul, convert dfinsupp.sum_zero, }

-- private lemma mul_assoc (a b c : G) : a * b * c = a * (b * c) := begin
--   simp only [has_mul_mul, direct_sum.of, add_monoid_hom.coe_mk],
--   convert dfinsupp.sum_sum_index (λ i : ι, _) (λ i (bi ci : G[i]), _),
--   { ext1 ai, ext1,
--     simp,
--     rw dfinsupp.sum_sum_index (λ i : ι, _) (λ i (bi ci : G[i]), _),
--     { rw dfinsupp.sum_sum_index (λ i : ι, _) (λ i (bi ci : G[i]), _),
--       { congr,
--         ext1 bi, ext1,
--         rw dfinsupp.sum_single_index,
--         { rw dfinsupp.sum_sum_index (λ i : ι, _) (λ i (bi ci : G[i]), _),
--           { congr,
--             ext1 ci, ext1,
--             rw dfinsupp.sum_single_index,
--             { congr' 1,
--               exact (add_assoc ai bi ci).symm,
--               rw subtype.heq_iff_coe_eq,
--               { simp [mul_assoc], },
--               { intro x, simp [add_assoc] }, },
--             { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, }, },
--           { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, },
--           { convert dfinsupp.single_add, simp [mul_add]}, },
--         { convert @dfinsupp.sum_zero ι (λ i, G[i]) _ _ _ _ _ _,
--           ext1 ai, ext1,
--           { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, }, } },
--       { convert @dfinsupp.sum_zero ι (λ i, G[i]) _ _ _ _ _ _,
--         ext1 ai, ext1,
--         { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, }, },
--       { convert dfinsupp.sum_add,
--         ext1 ai, ext1,
--         rw ← dfinsupp.single_add,
--         congr,
--         simp [add_mul], }, },
--     { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, },
--     { convert dfinsupp.single_add, simp [mul_add]}, },
--   { convert @dfinsupp.sum_zero ι (λ i, G[i]) _ _ _ _ _ _,
--     ext1 ai, ext1,
--     { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, }, },
--   { convert dfinsupp.sum_add,
--     ext1 ai, ext1,
--     rw ← dfinsupp.single_add,
--     congr,
--     simp [add_mul], },
-- end

-- private lemma left_distrib (a b c : G) : a * (b + c) = a * b + a * c :=
-- begin
--   simp only [has_mul_mul, direct_sum.of, add_monoid_hom.coe_mk],
--   convert dfinsupp.sum_add,
--   ext1, ext1,
--   convert dfinsupp.sum_add_index (λ i, _) (λ i ai bi, _),
--   { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, },
--   { convert dfinsupp.single_add, simp [mul_add] }
-- end

-- private lemma right_distrib (a b c : G) : (a + b) * c = a * c + b * c :=
-- begin
--   simp only [has_mul_mul, direct_sum.of, add_monoid_hom.coe_mk],
--   convert dfinsupp.sum_add_index (λ i, _) (λ i ai bi, _),
--   { convert @dfinsupp.sum_zero ι (λ i, G[i]) _ _ _ _ _ _,
--     ext1, ext1,
--     convert @dfinsupp.single_zero ι _ _ _ _,
--     simp, },
--   convert dfinsupp.sum_add,
--   ext1, ext1,
--   convert dfinsupp.single_add,
--   simp [add_mul],
-- end

-- instance : semiring G := {
--   one_mul := one_mul G,
--   mul_one := mul_one G,
--   mul_assoc := mul_assoc G,
--   zero_mul := zero_mul G,
--   mul_zero := mul_zero G,
--   left_distrib := left_distrib G,
--   right_distrib := right_distrib G,
--   ..(infer_instance : add_comm_monoid G),
--   ..(infer_instance : has_mul G),
--   ..(infer_instance : has_one G),
-- }

end semiring

end grading
