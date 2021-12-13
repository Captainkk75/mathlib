/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.pure
import combinatorics.simplicial_complex.subdivision

/-!
# Pyramid of a simplicial complex
-/

namespace affine

open_locale classical affine big_operators
open set
variables {𝕜 E : Type*} [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] {n : ℕ}
  {S S₁ S₂ : simplicial_complex 𝕜 E} {v : E}

/-- The pyramid of a vertex `v` with respect to a simplicial complex `S` is the surcomplex
consisting of all faces of `S` along with all faces of `S` with `v` added. Defined to be `S` itself
if some face of S is already full dimensional or if `v` belongs to the convex hull of the space of
`S`. -/
noncomputable def simplicial_complex.pyramid (S : simplicial_complex 𝕜 E) (v : E) :
  simplicial_complex 𝕜 E :=
if v ∈ convex_hull 𝕜 S.space ∨
  ∃ X ∈ S.faces, (X : finset E).card = finite_dimensional.finrank 𝕜 E + 1 then S else
{ faces := {X' | ∃ X ∈ S.faces, X' ⊆ X ∪ {v}},
  indep := begin
    rintro X' ⟨X, hX, hX'X⟩,
    sorry
  end,
  down_closed := λ X' Y ⟨X, hX, hX'X⟩ hYX', ⟨X, hX, subset.trans hYX' hX'X⟩,
  disjoint := begin
    rintro X' Y' ⟨X, hX, hX'X⟩ ⟨Y, hY, hY'Y⟩,
    sorry
  end }

lemma subcomplex_pyramid :
  S.faces ⊆ (S.pyramid v).faces :=
begin
  by_cases v ∈ convex_hull 𝕜 S.space ∨ ∃ X ∈ S.faces,
    (X : finset E).card = finite_dimensional.finrank 𝕜 E + 1,
  { sorry
  },
  sorry
  --exact λ X hX, ⟨X, hX, finset.subset_union_left X {v}⟩
end

lemma pyramid_mono (hS : S₁ ≤ S₂) :
   S₁.pyramid v ≤ S₂.pyramid v :=
begin
  by_cases v ∈ convex_hull 𝕜 S₁.space ∨ ∃ X ∈ S₁.faces,
    (X : finset E).card = finite_dimensional.finrank 𝕜 E  + 1,
  { sorry --easy case
  },
  split,
  { sorry
  },
  { sorry
    /-rintro X ⟨Y, hY, hXYv⟩,
    obtain ⟨Z, hZ, hYZhull⟩ := h.2 hY,
    use Z ∪ {v},
    split,
    {   exact ⟨Z, hZ, subset.refl _⟩,
    },
    have hXYvhull : convex_hull 𝕜 ↑X ⊆ convex_hull 𝕜 ↑(Y ∪ {v}) := convex_hull_mono hXYv,
    have hYvZvhull : convex_hull 𝕜 ↑(Y ∪ {v}) ⊆ convex_hull 𝕜 ↑(Z ∪ {v}),
    {   sorry
    },
    exact subset.trans hXYvhull hYvZvhull,-/
  }
end

lemma pure_pyramid_of_pure [finite_dimensional 𝕜 E] (hn : n ≤ finite_dimensional.finrank 𝕜 E)
  (hv : v ∉ convex_hull 𝕜 S.space) (hS : S.pure_of n) :
  (S.pyramid v).pure_of (n + 1) :=
begin
  sorry
end

end affine
