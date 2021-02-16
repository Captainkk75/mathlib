/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.pi_tensor_product
import data.equiv.fin

/-!
# Tensor power of a semimodule over a commutative semirings

We define the `n`th tensor power of `M` as the n-ary tensor product indexed by `fin n` of `M`,
`⨂[R] (i : fin n), M`. This is a special case of `pi_tensor_product`
-/

open_locale tensor_product

/-- Homogenous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for
`⨂[R] (i : fin n), M`. -/
protected abbreviation tensor_power (R : Type*) (n : ℕ) (M : Type*)
  [comm_semiring R] [add_comm_monoid M] [semimodule R M] : Type* :=
⨂[R] (i : fin n), M

variables {R : Type*} {M : Type*} [comm_semiring R] [add_comm_monoid M] [semimodule R M]

localized "notation `⨂[`:100 R `]^`:80 n:max := tensor_power R n"
  in tensor_product

namespace tensor_power
open_locale tensor_product
open pi_tensor_product

/-- The canonical map from `R` to `⨂[R]^0 M` corresponding to the algebra_map of the tensor
algebra. -/
def algebra_map : R ≃ₗ[R] ⨂[R]^0 M :=
((reindex R M fin_zero_equiv').trans pempty_equiv).symm

lemma algebra_map_eq_smul_tprod (r : R) :
  algebra_map r = r • tprod R (λ i : fin 0, (i.elim0 : M)) :=
begin
  simp [algebra_map],
  congr,
end

def one : ⨂[R]^0 M := algebra_map 1

-- TODO: remove after #6243 is merged
instance {α : pempty → Type*} : unique (Π x, α x) :=
⟨⟨λ x, pempty.elim x⟩, λ f, funext $ λ x, pempty.elim x ⟩

/---/
def mul_equiv {n m : ℕ} : (⨂[R]^n M) ⊗[R] (⨂[R]^m M) ≃ₗ[R] ⨂[R]^(n + m) M :=
(tmul_equiv R M).trans (reindex R M sum_fin_sum_equiv)

def mul {n m : ℕ} : (⨂[R]^n M) →ₗ[R] (⨂[R]^m M) →ₗ[R] ⨂[R]^(n + m) M :=
begin
  refine linear_map.compr₂ _ _,
  rotate 3,
  refine tensor_product.mk R _ _,
  apply linear_equiv.to_linear_map,
  exact mul_equiv,
end
-- linear_map.compr₂ mul_equiv.to_linear_map (tensor_product.mk R (⨂[R]^n M) (⨂[R]^m M) )


lemma one_mul {n} (a : ⨂[R]^n M) : reindex R M (equiv.cast $ by rw zero_add) (mul one a) = a :=
begin
  rw ←linear_equiv.coe_coe _,
  rw ←linear_map.compr₂_apply,
  refine linear_map.congr_fun (_ : _ = linear_map.id) a,
  clear a,
  ext a,
  simp [mul, one, mul_equiv, linear_equiv.trans_apply],
  -- change (reindex R M _).to_linear_map.compr₂ mul one a = a,
  -- unfold mul one mul_equiv,
  -- rw [algebra_map_eq_smul_tprod, one_smul],
  -- apply pi_tensor_product.induction_on a,
  -- { intros r a',
  --   simp only [linear_equiv.map_smul,
  --     tensor_product.tmul_smul,
  --     linear_equiv.trans_apply,
  --     tmul_equiv_apply,
  --     reindex_tprod],
  --   congr',
  --   ext,
  --   simp [sum_fin_sum_equiv, equiv.cast], },
  -- { rintros a' b' ha hb,
  --   simp only [linear_equiv.map_add,
  --     tensor_product.tmul_add,
  --     linear_equiv.trans_apply,
  --     tmul_equiv_apply,
  --     reindex_tprod] at *,
  --   rw [ha, hb], },
end

lemma mul_one {n} (a : ⨂[R]^n M) : reindex R M (equiv.cast $ by rw add_zero) (mul a one) = a :=
begin
  unfold mul one mul_equiv,
  rw [algebra_map_eq_smul_tprod, one_smul],
  apply pi_tensor_product.induction_on a,
  { intros r a',
    simp only [linear_equiv.map_smul,
      ←tensor_product.smul_tmul',
      linear_equiv.trans_apply,
      tmul_equiv_apply,
      reindex_tprod,
      reindex_trans],
    congr',
    ext,
    generalize_proofs p,
    dsimp only [p],
    cases h : (sum_fin_sum_equiv.symm) x,
    simp [equiv.cast], sorry },
  { rintros a' b' ha hb,
    simp only [linear_equiv.map_add,
      tensor_product.add_tmul,
      linear_equiv.trans_apply,
      tmul_equiv_apply,
      reindex_tprod] at *,
    rw [ha, hb], },
end

lemma mul_assoc {na nb nc} (a : ⨂[R]^na M) (b : ⨂[R]^nb M)  (c : ⨂[R]^nc M) :
  reindex R M (equiv.cast $ by rw add_assoc) (mul (mul a b) c) = (mul a $ mul b c) :=
begin
  unfold mul mul_equiv,
  apply pi_tensor_product.induction_on a,
end

#check sum.elim


end tensor_power
