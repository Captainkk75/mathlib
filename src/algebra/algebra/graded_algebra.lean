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

-- TODO: move, or use classical
instance (S : submodule R A) (x : S) : decidable (x ≠ 0) :=
decidable.rec_on (infer_instance : decidable ((x : A) ≠ 0))
  (λ hfalse, decidable.is_false $ by simp * at *)
  (λ htrue, decidable.is_true $ by simp * at *)

namespace semiring

@[simps mul]
instance : has_mul G := {
  mul := λ a b,
    a.sum (λ i ai,
      b.sum (λ j bj,
        let abij : ↥(G.submodules (i + j)) := ⟨(ai * bj : A), G.mul_mem ai bj⟩ in
        direct_sum.of (λ i, G.submodules i) (i + j) abij
      )
    )
}

@[simps one]
instance : has_one G := {
  one := direct_sum.of (λ i, G.submodules i) 0 ⟨1, G.one_mem⟩,
}

/-! These proofs are very slow, so these lemmas are defined separately -/

private lemma one_mul (a : G) : 1 * a = a :=
begin
  simp only [has_mul_mul, has_one_one, direct_sum.of, dfinsupp.single_add_hom,
    add_monoid_hom.coe_mk],
  rw dfinsupp.sum_single_index,
  { convert @dfinsupp.sum_single ι (λ i, G[i]) _ _ _ a,
    ext1 i, ext1,
    congr, exact zero_add i,
    rw subtype.heq_iff_coe_eq,
    { rw [submodule.coe_mk, submodule.coe_mk, one_mul], },
    { intro x, rw zero_add }, },
  { convert @dfinsupp.sum_zero _ _ _ _ _ _ _ a,
    ext1 i, ext1,
    convert @dfinsupp.single_zero ι _ _ _ _,
    simp only [zero_mul, submodule.coe_zero], }
end

private lemma mul_one (a : G) : a * 1 = a := begin
  simp only [has_mul_mul, has_one_one, direct_sum.of, dfinsupp.single_add_hom,
    add_monoid_hom.coe_mk],
  convert @dfinsupp.sum_single ι _ _ _ _ a,
  ext1 i, ext1,
  rw dfinsupp.sum_single_index,
  { congr, exact add_zero i,
    rw subtype.heq_iff_coe_eq,
    { rw [submodule.coe_mk, submodule.coe_mk, mul_one], },
    { intro x, rw add_zero }, },
  { convert @dfinsupp.single_zero ι _ _ _ _,
    rw [submodule.coe_zero, mul_zero], },
end

private lemma zero_mul (a : G) : 0 * a = 0 := by { rw has_mul_mul, exact dfinsupp.sum_zero_index }

private lemma mul_zero (a : G) : a * 0 = 0 := by { rw has_mul_mul, convert dfinsupp.sum_zero, }

private lemma mul_assoc (a b c : G) : a * b * c = a * (b * c) := begin
  simp only [has_mul_mul, direct_sum.of, dfinsupp.single_add_hom, add_monoid_hom.coe_mk],
  convert dfinsupp.sum_sum_index (λ i : ι, _) (λ i (bi ci : G[i]), _),
  { ext1 ai, ext1,
    simp,
    rw dfinsupp.sum_sum_index (λ i : ι, _) (λ i (bi ci : G[i]), _),
    { rw dfinsupp.sum_sum_index (λ i : ι, _) (λ i (bi ci : G[i]), _),
      { congr,
        ext1 bi, ext1,
        rw dfinsupp.sum_single_index,
        { rw dfinsupp.sum_sum_index (λ i : ι, _) (λ i (bi ci : G[i]), _),
          { congr,
            ext1 ci, ext1,
            rw dfinsupp.sum_single_index,
            { congr' 1,
              exact (add_assoc ai bi ci).symm,
              rw subtype.heq_iff_coe_eq,
              { simp [mul_assoc], },
              { intro x, simp [add_assoc] }, },
            { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, }, },
          { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, },
          { convert dfinsupp.single_add, simp [mul_add]}, },
        { convert @dfinsupp.sum_zero ι (λ i, G[i]) _ _ _ _ _ _,
          ext1 ai, ext1,
          { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, }, } },
      { convert @dfinsupp.sum_zero ι (λ i, G[i]) _ _ _ _ _ _,
        ext1 ai, ext1,
        { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, }, },
      { convert dfinsupp.sum_add,
        ext1 ai, ext1,
        rw ← dfinsupp.single_add,
        congr,
        simp [add_mul], }, },
    { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, },
    { convert dfinsupp.single_add, simp [mul_add]}, },
  { convert @dfinsupp.sum_zero ι (λ i, G[i]) _ _ _ _ _ _,
    ext1 ai, ext1,
    { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, }, },
  { convert dfinsupp.sum_add,
    ext1 ai, ext1,
    rw ← dfinsupp.single_add,
    congr,
    simp [add_mul], },
end

private lemma left_distrib (a b c : G) : a * (b + c) = a * b + a * c :=
begin
  simp only [has_mul_mul, direct_sum.of, dfinsupp.single_add_hom, add_monoid_hom.coe_mk],
  convert dfinsupp.sum_add,
  ext1, ext1,
  convert dfinsupp.sum_add_index (λ i, _) (λ i ai bi, _),
  { convert @dfinsupp.single_zero ι (λ i, G[i]) _ _ _, simp, },
  { convert dfinsupp.single_add, simp [mul_add] }
end

private lemma right_distrib (a b c : G) : (a + b) * c = a * c + b * c :=
begin
  simp only [has_mul_mul, direct_sum.of, dfinsupp.single_add_hom, add_monoid_hom.coe_mk],
  convert dfinsupp.sum_add_index (λ i, _) (λ i ai bi, _),
  { convert @dfinsupp.sum_zero ι (λ i, G[i]) _ _ _ _ _ _,
    ext1, ext1,
    convert @dfinsupp.single_zero ι _ _ _ _,
    simp, },
  convert dfinsupp.sum_add,
  ext1, ext1,
  convert dfinsupp.single_add,
  simp [add_mul],
end

instance : semiring G := {
  one_mul := one_mul G,
  mul_one := mul_one G,
  mul_assoc := mul_assoc G,
  zero_mul := zero_mul G,
  mul_zero := mul_zero G,
  left_distrib := left_distrib G,
  right_distrib := right_distrib G,
  ..(infer_instance : add_comm_monoid G),
  ..(infer_instance : has_mul G),
  ..(infer_instance : has_one G),
}

end semiring

end grading
