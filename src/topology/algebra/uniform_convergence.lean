/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.uniform_convergence_topology
import topology.algebra.module.basic
import analysis.locally_convex.bounded

/-!
# Algebraic facts about the topology of uniform convergence

This file contaains algrebraic compatibility results about the uniform structure of uniform
convergence / `𝔖`-convergence. They will mostly be useful for defining strong topologies on the
space of continuous linear maps between two topological vector spaces.

## Main statements

* `uniform_convergence.uniform_group` : if `G` is a uniform group, then the uniform structure of
  uniform convergence makes `α → G` an uniform group
* `uniform_convergence_on.uniform_group` : if `G` is a uniform group, then the uniform structure of
  `𝔖`-convergence, for any `𝔖 : set (set α)`, makes `α → G` an uniform group

## TODO

* Let `E` be a TVS, `𝔖 : set (set α)` and `H` a submodule of `α → E`. If the image of any `S ∈ 𝔖`
  by any `u ∈ H` is bounded (in the sense of `bornology.is_vonN_bounded`), then `H`, equipped with
  the topology of `𝔖`-convergence, is a TVS.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]

## Tags

uniform convergence, strong dual

-/

section group

variables {α G : Type*} [group G] [uniform_space G] [uniform_group G] {𝔖 : set $ set α}

local attribute [-instance] Pi.uniform_space
local attribute [-instance] Pi.topological_space
local attribute [instance] uniform_convergence.uniform_space

@[to_additive]
protected lemma uniform_convergence.uniform_group :
  uniform_group (α → G) :=
⟨(uniform_convergence.postcomp_uniform_continuous uniform_continuous_div).comp
  uniform_convergence.uniform_equiv_prod_arrow.symm.uniform_continuous⟩

local attribute [-instance] uniform_convergence.uniform_space

@[to_additive]
protected lemma uniform_convergence_on.uniform_group :
  @uniform_group (α → G) (uniform_convergence_on.uniform_space α G 𝔖) _ :=
begin
  letI : uniform_space (α → G) := uniform_convergence_on.uniform_space α G 𝔖,
  letI : uniform_space (α → G × G) := uniform_convergence_on.uniform_space α (G × G) 𝔖,
  exact ⟨(uniform_convergence_on.postcomp_uniform_continuous uniform_continuous_div).comp
          uniform_convergence_on.uniform_equiv_prod_arrow.symm.uniform_continuous⟩
end

end group

section module

variables {α 𝕜 E : Type*} [semi_normed_ring 𝕜] [add_comm_group E] [module 𝕜 E]
  [topological_space E] [topological_add_group E] [has_continuous_smul 𝕜 E] {𝔖 : set $ set α}
  (H : submodule 𝕜 (α → E))

local attribute [-instance] Pi.uniform_space
local attribute [-instance] Pi.topological_space

lemma goal (h : ∀ u ∈ H, ∀ s ∈ 𝔖, bornology.is_vonN_bounded 𝕜 (u '' s)) :
  @has_continuous_smul 𝕜 H _ _
  ((@uniform_convergence_on.topological_space α E (topological_add_group.to_uniform_space E) 𝔖)
    .induced (coe : H → α → E)) :=
begin

end

end module
