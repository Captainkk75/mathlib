/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Jeremy Avigad, Johan Commelin
-/
import linear_algebra.matrix.symmetric
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def

/-! # Schur complement

This file proves properties of the Schur complement `D - C A⁻¹ B` of a block matrix `[A B; C D]`.

## Main result

 * `matrix.schur_complement_pos_semidef_iff` :
  If a matrix `A` is positive definite, then
  `[A B; Bᴴ D]` is postive semidefinite if and only if `D - Bᴴ A⁻¹ B` is postive semidefinite.

-/

namespace matrix

open_locale matrix
variables {n : Type*} {R : Type*} [comm_ring R] [star_ring R]

variables (A B C D : matrix n n R) (x y u v: n → R)

localized "infix ` ⊕ᵥ `:65 := sum.elim" in matrix

lemma schur_complement_eq [fintype n] [decidable_eq n] {A : matrix n n R} [invertible A]
  (hA : A.is_hermitian) :
vec_mul (star (x ⊕ᵥ y)) (from_blocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
  vec_mul (star (x + (A⁻¹ ⬝ B).mul_vec y)) A ⬝ᵥ (x + (A⁻¹ ⬝ B).mul_vec y) +
    vec_mul (star y) (D - Bᴴ ⬝ A⁻¹ ⬝ B) ⬝ᵥ y :=
begin
  simp [star_sum_elim, from_blocks_mul_vec, vec_mul_from_blocks, add_vec_mul, dot_product_mul_vec,
    vec_mul_sub, matrix.mul_assoc, vec_mul_mul_vec, hA.eq, conj_transpose_nonsing_inv,
    star_mul_vec],
  abel
end

end matrix

namespace matrix

open_locale matrix
variables {n : Type*} [fintype n] {R : Type*} [ordered_comm_ring R] [star_ring R]

variables {A : matrix n n R} (B C D : matrix n n R) (x y u v: n → R)

lemma is_hermitian.from_blocks₁₁ [decidable_eq n] (hA : A.is_hermitian) :
  (from_blocks A B Bᴴ D).is_hermitian ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).is_hermitian :=
begin
  have hBAB : (Bᴴ ⬝ A⁻¹ ⬝ B).is_hermitian,
  { apply is_hermitian_mul_mul,
    apply is_hermitian_nonsingular_inv hA },
  rw [is_hermitian_from_blocks_iff],
  split,
  { intro h,
    apply is_hermitian.sub h.2.2.2 hBAB },
  { intro h,
    refine ⟨hA, rfl, conj_transpose_conj_transpose B, _⟩,
    rw ← sub_add_cancel D,
    apply is_hermitian.add h hBAB }
end

lemma pos_semidef.from_blocks₁₁ [decidable_eq n] [invertible A] (hA : A.pos_def) :
  (from_blocks A B Bᴴ D).pos_semidef ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).pos_semidef :=
begin
  rw [pos_semidef, is_hermitian.from_blocks₁₁ _ _ hA.1],
  split,
  { refine λ h, ⟨h.1, λ x, _⟩,
    have := h.2 (- ((A⁻¹ ⬝ B).mul_vec x) ⊕ᵥ x),
    rw [dot_product_mul_vec, schur_complement_eq B D _ _ hA.1, neg_add_self,
      dot_product_zero, zero_add] at this,
    rw [dot_product_mul_vec], exact this },
  { refine λ h, ⟨h.1, λ x, _⟩,
    rw [dot_product_mul_vec, ← sum.elim_comp_inl_inr x, schur_complement_eq B D _ _ hA.1],
    apply le_add_of_nonneg_of_le,
    { rw ← dot_product_mul_vec,
      apply hA.pos_semidef.2, },
    { rw ← dot_product_mul_vec, apply h.2 } }
end

end matrix
