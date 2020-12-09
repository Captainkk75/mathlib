/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser.
-/

import algebra.ring_quot
import linear_algebra.tensor_algebra
import group_theory.perm.sign

/-!
# Exterior Algebras

We construct the exterior algebra of a semimodule `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-semimodule `M` is denoted as `exterior_algebra R M`.
It is endowed with the structure of an `R`-algebra. Some results only hold at the level of
generality of an `S`-module `M` and the space `exterior_algebra S N`.

Given a linear morphism `f : M → A` from a semimodule `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `exterior_algebra.lift R f cond`.

The canonical linear map `M → exterior_algebra R M` is denoted `exterior_algebra.ι R`.

The canonical multilinear map `(fin q → M) → exterior_algebra R M` is denoted `wedge R M`.

## Theorems

The main theorems proved ensure that `exterior_algebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is  fact that the composition of `ι R` with `lift R f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R f cond` with respect to 1.
3. `wedge_perm` says that for any permutation `σ` of `fin q` and any `ν : fin q → N`, we have that
`wedge S N ν = (equiv.perm.sign σ) • wedge S n (ν ∘ σ)`.

## Implementation details

The exterior algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `exterior_algebra.rel R M` on `tensor_algebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `0`.
2. The exterior algebra is the quotient of the tensor algebra by this relation.

-/

variables (R : Type*) [comm_semiring R]
variables (M : Type*) [add_comm_monoid M] [semimodule R M]
variables {S : Type*} [comm_ring S]
variables {N : Type*} [add_comm_group N] [module S N]
variable {q : ℕ}

namespace exterior_algebra
open tensor_algebra

/-- `rel` relates each `ι m * ι m`, for `m : M`, with `0`.

The exterior algebra of `M` is defined as the quotient modulo this relation.
-/
inductive rel : tensor_algebra R M → tensor_algebra R M → Prop
| of (m : M) : rel ((ι R m) * (ι R m)) 0

end exterior_algebra

/--
The exterior algebra of an `R`-semimodule `M`.
-/
@[derive [inhabited, semiring, algebra R]]
def exterior_algebra := ring_quot (exterior_algebra.rel R M)

namespace exterior_algebra

instance : ring (exterior_algebra S N) := algebra.semiring_to_ring S

/--
The canonical quotient map `tensor_algebra R M → exterior_algebra R M`.
-/
protected def quot : tensor_algebra R M →ₐ[R] exterior_algebra R M :=
  ring_quot.mk_alg_hom R _

variables {M}

/--
The canonical linear map `M →ₗ[R] exterior_algebra R M`.
-/
def ι : M →ₗ[R] exterior_algebra R M :=
(ring_quot.mk_alg_hom R _).to_linear_map.comp (tensor_algebra.ι R)


variables {R}

/-- As well as being linear, `ι m` squares to zero -/
@[simp]
theorem ι_square_zero (m : M) : (ι R m) * (ι R m) = 0 :=
begin
  erw [←alg_hom.map_mul, ring_quot.mk_alg_hom_rel R (rel.of m), alg_hom.map_zero _],
end

variables {A : Type*} [semiring A] [algebra R A]

@[simp]
theorem comp_ι_square_zero (g : exterior_algebra R M →ₐ[R] A)
  (m : M) : g (ι R m) * g (ι R m) = 0 :=
by rw [←alg_hom.map_mul, ι_square_zero, alg_hom.map_zero]

variables (R)

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `exterior_algebra R M` to `A`.
-/
@[simps symm_apply]
def lift : {f : M →ₗ[R] A // ∀ m, f m * f m = 0} ≃ (exterior_algebra R M →ₐ[R] A) :=
{ to_fun := λ f,
  ring_quot.lift_alg_hom R ⟨tensor_algebra.lift R (f : M →ₗ[R] A),
    λ x y (h : rel R M x y), by {
      induction h,
      rw [alg_hom.map_zero, alg_hom.map_mul, tensor_algebra.lift_ι_apply, f.prop] }⟩,
  inv_fun := λ F, ⟨F.to_linear_map.comp (ι R), λ m, by rw [
    linear_map.comp_apply, alg_hom.to_linear_map_apply, comp_ι_square_zero]⟩,
  left_inv := λ f, by { ext, simp [ι] },
  right_inv := λ F, by { ext, simp [ι] } }

@[simp]
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) :
  (lift R ⟨f, cond⟩).to_linear_map.comp (ι R) = f :=
(subtype.mk_eq_mk.mp $ (lift R).symm_apply_apply ⟨f, cond⟩)

@[simp]
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (x) :
  lift R ⟨f, cond⟩ (ι R x) = f x :=
(linear_map.ext_iff.mp $ ι_comp_lift R f cond) x

@[simp]
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0)
  (g : exterior_algebra R M →ₐ[R] A) : g.to_linear_map.comp (ι R) = f ↔ g = lift R ⟨f, cond⟩ :=
begin
  convert (lift R).symm_apply_eq,
  rw lift_symm_apply,
  simp only,
end

attribute [irreducible] ι lift
-- Marking `exterior_algebra` irreducible makes our `ring` instances inaccessible.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241
-- For now, we avoid this by not marking it irreducible.

variables {R M}

@[simp]
theorem lift_comp_ι (g : exterior_algebra R M →ₐ[R] A) :
  lift R ⟨g.to_linear_map.comp (ι R), comp_ι_square_zero _⟩ = g :=
begin
  convert (lift R).apply_symm_apply g,
  rw lift_symm_apply,
  refl,
end

@[ext]
theorem hom_ext {f g : exterior_algebra R M →ₐ[R] A}
  (h : f.to_linear_map.comp (ι R) = g.to_linear_map.comp (ι R)) : f = g :=
begin
  apply (lift R).symm.injective,
  rw [lift_symm_apply, lift_symm_apply],
  simp only [h],
end

lemma ι_add_mul (x y z : M) : ι R (x + y) * ι R z = ι R x * ι R z + ι R y * ι R z :=
by rw [linear_map.map_add, right_distrib]

lemma ι_mul_add (x y z : M) : ι R x * ι R (y + z) = ι R x * ι R y + ι R x * ι R z :=
by rw [linear_map.map_add, left_distrib]

@[simp]
lemma ι_add_swap (x y : M) : ι R x * ι R y + ι R y * ι R x = 0 :=
let ι := (ι R : M →ₗ[R] _) in calc ι x * ι y + ι y * ι x
  = ι x * ι y + ι y * ι y + ι y * ι x :
    by rw [ι_square_zero, add_zero]
  ...= ι x * ι y + ι y * ι y + ι y * ι x + ι x * ι x :
    by rw [ι_square_zero x, add_zero]
  ...= ι (x + y) * ι y + ι y * ι x + ι x * ι x :
    by rw ι_add_mul
  ...= ι (x + y) * ι y + ι (x + y) * ι x :
    by rw [ι_add_mul x y x, ι_square_zero, zero_add, add_zero]
  ...= ι (x + y) * ι (x + y) :
    by rw [ι_mul_add (x + y) x y, add_comm]
  ...= 0 :
    by rw ι_square_zero

variables (R M)

/--
The canonical multilinear map from `fin q → M` into `exterior_algebra R M`.
-/
def wedge : multilinear_map R (λ i : fin q, M) (exterior_algebra R M) :=
{ to_fun := λ ν : fin q → M , exterior_algebra.quot R M (tensor_algebra.mk R M ν),
  map_add' := λ _ _ _ _, by simp,
  map_smul' := λ _ _ _ _, by simp }

variables {R M}


section

-- TODO: we should not be relying on these definitions
local attribute [semireducible] exterior_algebra ι

lemma wedge_split (ν : fin q.succ → M) :
wedge R M ν = ι R (ν 0) * wedge R M (λ i : fin q, ν i.succ) :=
begin
  change exterior_algebra.quot R M _ = _,
  rw tensor_algebra.mk_split,
  simp only [exterior_algebra.quot, alg_hom.map_mul],
  refl,
end

end

/--
Auxiliary lemma used to prove `wedge_self_adj`.
-/
lemma wedge_self_adj_aux (ν : fin q.succ → M) {j : fin q.succ} (hj : j.val = 1) (hv : ν 0 = ν j):
ι R (ν 0) * wedge R M (λ i : fin q, ν i.succ) = 0 :=
begin
  induction q with q hq,
  --Base case (we get a contradiction)
  exfalso,
  exact not_lt_of_le (le_of_eq (eq_comm.mp hj)) j.2,
  --Inductive step
  rw wedge_split,
  have hj1 : j = 1, by {ext, exact hj},
  have fact : ν (0 : fin q.succ).succ = ν 1, by congr,
  rw hj1 at hv,
  rw [fact, hv, ←mul_assoc, ι_square_zero, zero_mul],
end


lemma wedge_self_adj (ν : fin q → M) (i j : fin q) (hij : ↑i + 1 = ↑j) (hv : ν i = ν j) :
wedge R M ν = 0 :=
begin
  induction q with q hq,
  --Base case (there is nothing to show)
  exfalso, exact nat.not_lt_zero ↑i i.property,
  --Inductive step
  rw wedge_split,
  cases classical.em (i = 0) with hem hem,
  --case i = 0
  rw hem at hv,
  rw hem at hij, norm_num at hij, rw eq_comm at hij,
  exact wedge_self_adj_aux ν hij hv,
  --case i ≠ 0
  have hj : j ≠ 0 :=
  begin
    intro cj, rw cj at hij, simp at hij, assumption,
  end,
  have hij1 : ↑(i.pred hem) + 1 = ↑(j.pred hj) :=
    by rw [←fin.coe_succ, fin.succ_pred, fin.coe_pred, ←hij, nat.add_sub_cancel],
  have hv1 : (ν ∘ fin.succ) (i.pred hem) = (ν ∘ fin.succ) (j.pred hj) := by simp [hv],
  rw hq (ν ∘ fin.succ) (i.pred hem) (j.pred hj) hij1 hv1,
  rw mul_zero,
end



lemma wedge_add_swap_adj (ν : fin q → M) {i j : fin q} (hij : i.val + 1 = j.val) :
wedge R M ν + wedge R M (ν ∘ equiv.swap i j) = 0 :=
begin
  have hij1 : i ≠ j :=
  begin
    intro h,
    rw h at hij, exact nat.succ_ne_self j.val hij,
  end,
  have key : wedge R M (function.update (function.update ν i (ν i + ν j)) j (ν i + ν j)) = 0 :=
    by rw wedge_self_adj (function.update (function.update ν i (ν i + ν j)) j (ν i + ν j)) i j hij
    begin
      rw [function.update_same, function.update_noteq hij1,  function.update_same],
    end,
  rw multilinear_map.map_add at key,
  rw [function.update_comm hij1 (ν i + ν j) (ν i) ν, multilinear_map.map_add] at key,
  rw wedge_self_adj (function.update (function.update ν j (ν i)) i (ν i)) i j hij
    begin
      rw function.update_same,
      rw function.update_comm (ne_comm.mp hij1) (ν i) (ν i) ν,
      rw function.update_same,
    end at key,
  rw zero_add at key,
  rw [function.update_comm hij1 (ν i + ν j) (ν j) ν, multilinear_map.map_add] at key,
  rw wedge_self_adj (function.update (function.update ν j (ν j)) i (ν j)) i j hij
  begin
    rw function.update_same,
    rw function.update_comm (ne_comm.mp hij1) (ν j) (ν j) ν,
    rw function.update_same,
  end at key,
  rw [add_zero, add_comm] at key,
  convert key,
  simp,
  ext x,
    cases classical.em (x = i) with hx hx,
    --case x = i
    rw hx,
    simp only [equiv.swap_apply_left, function.comp_app],
    rw function.update_same,
    --case x ≠ i
    cases classical.em (x = j) with hx1 hx1,
    rw hx1,
    simp only [equiv.swap_apply_left, function.comp_app],
    rw function.update_noteq (ne_comm.mp hij1),
    simp,
    --case x ≠ i, x ≠ j,
    simp only [hx, hx1, function.comp_app, function.update_noteq, ne.def, not_false_iff],
    rw equiv.swap_apply_of_ne_of_ne hx hx1,
end



lemma wedge_swap_adj (ν : fin q → N) {i j : fin q} (hij : i.val + 1 = j.val) :
wedge S N (ν ∘ equiv.swap i j) = - wedge S N ν  :=
begin
  apply eq_neg_of_add_eq_zero,
  rw add_comm,
  exact wedge_add_swap_adj ν hij,
end


lemma wedge_perm (ν : fin q → N) (σ : equiv.perm (fin q)) :
wedge S N ν = (equiv.perm.sign σ) • wedge S N (ν ∘ σ) :=
begin
  apply equiv.perm.swap_adj_induction_on' σ,
  --Base case
  rw [equiv.perm.sign_one, one_smul], congr,
  --Inductive step
  intros f x y hxy hI,
  have hxy1 : x ≠ y :=
  begin
    intro h, rw h at hxy, exact (nat.succ_ne_self y.val) hxy,
  end,
  have assoc : ν ∘ (f * equiv.swap x y : equiv.perm (fin q)) = (ν ∘ f ∘ equiv.swap x y) := rfl,
  rw [assoc, wedge_swap_adj (ν ∘ f) hxy, ←neg_one_smul ℤ (wedge S N (ν ∘ f))],
  have h1 : (-1 : ℤ) = equiv.perm.sign (equiv.swap x y) := by simp [hxy1],
  rw h1,
  have hack : ∀ z : exterior_algebra S N,
  (equiv.perm.sign (f * equiv.swap x y) : units ℤ) • z =
  (equiv.perm.sign (f * equiv.swap x y) : ℤ) • z := λ z, rfl,
  rw hack,
  rw [smul_smul, ←units.coe_mul, ←equiv.perm.sign_mul, mul_assoc, equiv.swap_mul_self, mul_one],
  assumption,
end

end exterior_algebra
