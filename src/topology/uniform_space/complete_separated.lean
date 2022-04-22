/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.uniform_space.cauchy
import topology.uniform_space.separation
import topology.dense_embedding

/-!
# Theory of complete separated uniform spaces.

This file is for elementary lemmas that depend on both Cauchy filters and separation.
-/

open filter
open_locale topological_space filter

variables {α : Type*}

/-In a separated space, a complete set is closed -/
lemma is_complete.is_closed  [uniform_space α] [t2_space α] {s : set α} (h : is_complete s) :
  is_closed s :=
is_closed_iff_cluster_pt.2 $ λ a ha, begin
  let f := 𝓝[s] a,
  have : cauchy f := cauchy_nhds.mono' ha inf_le_left,
  rcases h f this (inf_le_right) with ⟨y, ys, fy⟩,
  rwa (tendsto_nhds_unique' ha inf_le_left fy : a = y)
end

namespace dense_inducing
open filter
variables [topological_space α] {β : Type*} [topological_space β]
variables {γ : Type*} [uniform_space γ] [complete_space γ] [t2_space γ]

lemma continuous_extend_of_cauchy {e : α → β} {f : α → γ}
  (de : dense_inducing e) (h : ∀ b : β, cauchy (map f (comap e $ 𝓝 b))) :
  continuous (de.extend f) :=
begin
  letI : regular_space γ := uniform_space.regular_of_t2,
  exact de.continuous_extend (λ b, complete_space.complete (h b))
end

end dense_inducing
