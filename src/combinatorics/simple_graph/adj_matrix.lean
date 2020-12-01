/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark.
-/
import linear_algebra.matrix
import data.rel
import combinatorics.simple_graph.basic

/-!
# Adjacency Matrices

This module defines the adjacency matrix of a graph, and provides theorems connecting graph
properties to computational properties of the matrix.

## Main definitions

* `adj_matrix` is the adjacency matrix of a `simple_graph` with coefficients in a given semiring.

-/

open_locale big_operators matrix
open finset matrix simple_graph

universes u v
variables (R : Type v) [semiring R]

namespace simple_graph

variables (G : simple_graph) (R) [decidable_rel G.adj] [fintype G.V]

/-- `adj_matrix G R` is the matrix `A` such that `A i j = (1 : R)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adj_matrix : matrix (V G) (V G) R
| i j := if (i ~g j) then 1 else 0

variable {R}

@[simp]
lemma adj_matrix_apply (v w : V G) : G.adj_matrix R v w = if (G.adj v w) then 1 else 0 := rfl

@[simp]
theorem transpose_adj_matrix : (G.adj_matrix R)ᵀ = G.adj_matrix R :=
by { ext, simp [adj_symm] }

@[simp]
lemma adj_matrix_dot_product (v : V G) (vec : V G → R) :
  dot_product (G.adj_matrix R v) vec = ∑ u in neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter]

@[simp]
lemma dot_product_adj_matrix (v : V G) (vec : V G → R) :
  dot_product vec (G.adj_matrix R v) = ∑ u in neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter, sum_apply]

@[simp]
lemma adj_matrix_mul_vec_apply (v : V G) (vec : V G → R) :
  ((G.adj_matrix R).mul_vec vec) v = ∑ u in neighbor_finset v, vec u :=
by rw [mul_vec, adj_matrix_dot_product]

@[simp]
lemma adj_matrix_vec_mul_apply (v : V G) (vec : V G → R) :
  ((G.adj_matrix R).vec_mul vec) v = ∑ u in neighbor_finset v, vec u :=
begin
  rw [← dot_product_adj_matrix, vec_mul],
  refine congr rfl _, ext,
  rw [← transpose_apply (adj_matrix R G) x v, transpose_adj_matrix],
end

@[simp]
lemma adj_matrix_mul_apply (M : matrix (V G) (V G) R) (v w : V G) :
  (G.adj_matrix R ⬝ M) v w = ∑ u in neighbor_finset v, M u w :=
by simp [mul_apply, neighbor_finset_eq_filter, sum_filter]

@[simp]
lemma mul_adj_matrix_apply (M : matrix (V G) (V G) R) (v w : V G) :
  (M ⬝ G.adj_matrix R) v w = ∑ u in neighbor_finset w, M v u :=
by simp [mul_apply, neighbor_finset_eq_filter, sum_filter, adj_symm]

variable (R)
theorem trace_adj_matrix : matrix.trace (V G) R R (G.adj_matrix R) = 0 := by simp
variable {R}

theorem adj_matrix_mul_self_apply_self (i : V G) :
  ((G.adj_matrix R) ⬝ (G.adj_matrix R)) i i = degree i :=
by simp [degree]

variable {G}

@[simp]
lemma adj_matrix_mul_vec_const_apply {r : R} {v : V G} :
  (G.adj_matrix R).mul_vec (function.const _ r) v = degree v * r :=
by simp [degree]

lemma adj_matrix_mul_vec_const_apply_of_regular {d : ℕ} {r : R} (hd : G.is_regular_of_degree d)
  {v : V G} :
  (G.adj_matrix R).mul_vec (function.const _ r) v = (d * r) :=
by simp [hd v]

end simple_graph
