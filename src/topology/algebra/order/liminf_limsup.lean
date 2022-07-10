/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import order.liminf_limsup
import topology.algebra.order.basic

/-!
# Lemmas about liminf and limsup in an order topology.
-/

open filter
open_locale topological_space classical

universes u v
variables {α : Type u} {β : Type v}

section liminf_limsup

section order_closed_topology
variables [semilattice_sup α] [topological_space α] [order_topology α]

lemma is_bounded_le_nhds (a : α) : (𝓝 a).is_bounded (≤) :=
(is_top_or_exists_gt a).elim (λ h, ⟨a, eventually_of_forall h⟩) (λ ⟨b, hb⟩, ⟨b, ge_mem_nhds hb⟩)

lemma filter.tendsto.is_bounded_under_le {f : filter β} {u : β → α} {a : α}
  (h : tendsto u f (𝓝 a)) : f.is_bounded_under (≤) u :=
(is_bounded_le_nhds a).mono h

lemma filter.tendsto.bdd_above_range_of_cofinite {u : β → α} {a : α}
  (h : tendsto u cofinite (𝓝 a)) : bdd_above (set.range u) :=
h.is_bounded_under_le.bdd_above_range_of_cofinite

lemma filter.tendsto.bdd_above_range {u : ℕ → α} {a : α}
  (h : tendsto u at_top (𝓝 a)) : bdd_above (set.range u) :=
h.is_bounded_under_le.bdd_above_range

lemma is_cobounded_ge_nhds (a : α) : (𝓝 a).is_cobounded (≥) :=
(is_bounded_le_nhds a).is_cobounded_flip

lemma filter.tendsto.is_cobounded_under_ge {f : filter β} {u : β → α} {a : α}
  [ne_bot f] (h : tendsto u f (𝓝 a)) : f.is_cobounded_under (≥) u :=
h.is_bounded_under_le.is_cobounded_flip

end order_closed_topology

section order_closed_topology
variables [semilattice_inf α] [topological_space α] [order_topology α]

lemma is_bounded_ge_nhds (a : α) : (𝓝 a).is_bounded (≥) := @is_bounded_le_nhds αᵒᵈ _ _ _ a

lemma filter.tendsto.is_bounded_under_ge {f : filter β} {u : β → α} {a : α}
  (h : tendsto u f (𝓝 a)) : f.is_bounded_under (≥) u :=
(is_bounded_ge_nhds a).mono h

lemma filter.tendsto.bdd_below_range_of_cofinite {u : β → α} {a : α}
  (h : tendsto u cofinite (𝓝 a)) : bdd_below (set.range u) :=
h.is_bounded_under_ge.bdd_below_range_of_cofinite

lemma filter.tendsto.bdd_below_range {u : ℕ → α} {a : α}
  (h : tendsto u at_top (𝓝 a)) : bdd_below (set.range u) :=
h.is_bounded_under_ge.bdd_below_range

lemma is_cobounded_le_nhds (a : α) : (𝓝 a).is_cobounded (≤) :=
(is_bounded_ge_nhds a).is_cobounded_flip

lemma filter.tendsto.is_cobounded_under_le {f : filter β} {u : β → α} {a : α}
  [ne_bot f] (h : tendsto u f (𝓝 a)) : f.is_cobounded_under (≤) u :=
h.is_bounded_under_ge.is_cobounded_flip

end order_closed_topology

section conditionally_complete_linear_order
variables [conditionally_complete_linear_order α]

theorem lt_mem_sets_of_Limsup_lt {f : filter α} {b} (h : f.is_bounded (≤)) (l : f.Limsup < b) :
  ∀ᶠ a in f, a < b :=
let ⟨c, (h : ∀ᶠ a in f, a ≤ c), hcb⟩ := exists_lt_of_cInf_lt h l in
mem_of_superset h $ assume a hac, lt_of_le_of_lt hac hcb

theorem gt_mem_sets_of_Liminf_gt : ∀ {f : filter α} {b}, f.is_bounded (≥) → b < f.Liminf →
  ∀ᶠ a in f, b < a :=
@lt_mem_sets_of_Limsup_lt αᵒᵈ _

variables [topological_space α] [order_topology α]

/-- If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below. -/
theorem le_nhds_of_Limsup_eq_Liminf {f : filter α} {a : α}
  (hl : f.is_bounded (≤)) (hg : f.is_bounded (≥)) (hs : f.Limsup = a) (hi : f.Liminf = a) :
  f ≤ 𝓝 a :=
tendsto_order.2 $ and.intro
  (assume b hb, gt_mem_sets_of_Liminf_gt hg $ hi.symm ▸ hb)
  (assume b hb, lt_mem_sets_of_Limsup_lt hl $ hs.symm ▸ hb)

theorem Limsup_nhds (a : α) : Limsup (𝓝 a) = a :=
cInf_eq_of_forall_ge_of_forall_gt_exists_lt (is_bounded_le_nhds a)
  (assume a' (h : {n : α | n ≤ a'} ∈ 𝓝 a), show a ≤ a', from @mem_of_mem_nhds α _ a _ h)
  (assume b (hba : a < b), show ∃c (h : {n : α | n ≤ c} ∈ 𝓝 a), c < b, from
    match dense_or_discrete a b with
    | or.inl ⟨c, hac, hcb⟩ := ⟨c, ge_mem_nhds hac, hcb⟩
    | or.inr ⟨_, h⟩        := ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩
    end)

theorem Liminf_nhds : ∀ (a : α), Liminf (𝓝 a) = a := @Limsup_nhds αᵒᵈ _ _ _

/-- If a filter is converging, its limsup coincides with its limit. -/
theorem Liminf_eq_of_le_nhds {f : filter α} {a : α} [ne_bot f] (h : f ≤ 𝓝 a) : f.Liminf = a :=
have hb_ge : is_bounded (≥) f, from (is_bounded_ge_nhds a).mono h,
have hb_le : is_bounded (≤) f, from (is_bounded_le_nhds a).mono h,
le_antisymm
  (calc f.Liminf ≤ f.Limsup : Liminf_le_Limsup hb_le hb_ge
    ... ≤ (𝓝 a).Limsup :
      Limsup_le_Limsup_of_le h hb_ge.is_cobounded_flip (is_bounded_le_nhds a)
    ... = a : Limsup_nhds a)
  (calc a = (𝓝 a).Liminf : (Liminf_nhds a).symm
    ... ≤ f.Liminf :
      Liminf_le_Liminf_of_le h (is_bounded_ge_nhds a) hb_le.is_cobounded_flip)

/-- If a filter is converging, its liminf coincides with its limit. -/
theorem Limsup_eq_of_le_nhds : ∀ {f : filter α} {a : α} [ne_bot f], f ≤ 𝓝 a → f.Limsup = a :=
@Liminf_eq_of_le_nhds αᵒᵈ _ _ _

/-- If a function has a limit, then its limsup coincides with its limit. -/
theorem filter.tendsto.limsup_eq {f : filter β} {u : β → α} {a : α} [ne_bot f]
  (h : tendsto u f (𝓝 a)) : limsup f u = a :=
Limsup_eq_of_le_nhds h

/-- If a function has a limit, then its liminf coincides with its limit. -/
theorem filter.tendsto.liminf_eq {f : filter β} {u : β → α} {a : α} [ne_bot f]
  (h : tendsto u f (𝓝 a)) : liminf f u = a :=
Liminf_eq_of_le_nhds h

/-- If the liminf and the limsup of a function coincide, then the limit of the function
exists and has the same value -/
theorem tendsto_of_liminf_eq_limsup {f : filter β} {u : β → α} {a : α}
  (hinf : liminf f u = a) (hsup : limsup f u = a)
  (h : f.is_bounded_under (≤) u . is_bounded_default)
  (h' : f.is_bounded_under (≥) u . is_bounded_default) :
  tendsto u f (𝓝 a) :=
le_nhds_of_Limsup_eq_Liminf h h' hsup hinf

/-- If a number `a` is less than or equal to the `liminf` of a function `f` at some filter
and is greater than or equal to the `limsup` of `f`, then `f` tends to `a` along this filter. -/
theorem tendsto_of_le_liminf_of_limsup_le {f : filter β} {u : β → α} {a : α}
  (hinf : a ≤ liminf f u) (hsup : limsup f u ≤ a)
  (h : f.is_bounded_under (≤) u . is_bounded_default)
  (h' : f.is_bounded_under (≥) u . is_bounded_default) :
  tendsto u f (𝓝 a) :=
if hf : f = ⊥ then hf.symm ▸ tendsto_bot
else by haveI : ne_bot f := ⟨hf⟩; exact tendsto_of_liminf_eq_limsup
  (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf)
  (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h'

/-- Assume that, for any `a < b`, a sequence can not be infinitely many times below `a` and
above `b`. If it is also ultimately bounded above and below, then it has to converge. This even
works if `a` and `b` are restricted to a dense subset.
-/
lemma tendsto_of_no_upcrossings [densely_ordered α]
  {f : filter β} {u : β → α} {s : set α} (hs : dense s)
  (H : ∀ (a ∈ s) (b ∈ s), a < b → ¬((∃ᶠ n in f, u n < a) ∧ (∃ᶠ n in f, b < u n)))
  (h : f.is_bounded_under (≤) u . is_bounded_default)
  (h' : f.is_bounded_under (≥) u . is_bounded_default) :
  ∃ (c : α), tendsto u f (𝓝 c) :=
begin
  by_cases hbot : f = ⊥, { rw hbot, exact ⟨Inf ∅, tendsto_bot⟩ },
  haveI : ne_bot f := ⟨hbot⟩,
  refine ⟨limsup f u, _⟩,
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h',
  by_contra' hlt,
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : ∃ a, (f.liminf u < a ∧ a < f.limsup u) ∧ a ∈ s :=
    dense_iff_inter_open.1 hs (set.Ioo (f.liminf u) (f.limsup u)) is_open_Ioo
    (set.nonempty_Ioo.2 hlt),
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : ∃ b, (a < b ∧ b < f.limsup u) ∧ b ∈ s :=
    dense_iff_inter_open.1 hs (set.Ioo a (f.limsup u)) is_open_Ioo
    (set.nonempty_Ioo.2 au),
  have A : ∃ᶠ n in f, u n < a :=
    frequently_lt_of_liminf_lt (is_bounded.is_cobounded_ge h) la,
  have B : ∃ᶠ n in f, b < u n :=
    frequently_lt_of_lt_limsup (is_bounded.is_cobounded_le h') bu,
  exact H a as b bs ab ⟨A, B⟩,
end

end conditionally_complete_linear_order

end liminf_limsup

section monotone

open set

lemma monotone.Sup_image_le {R S : Type*} [complete_lattice R] [complete_linear_order S]
  {f : R → S} (f_incr : monotone f) (A : set R) :
  Sup (f '' A) ≤ f (Sup A) :=
begin
  refine Sup_le _,
  intros x x_in_fA,
  rcases (mem_image f A x).mp x_in_fA with ⟨z, ⟨z_in_A, fz_eq_x⟩⟩,
  by_contra b_gt,
  have key := (f_incr (le_Sup z_in_A)),
  rw fz_eq_x at key,
  exact (lt_self_iff_false x).mp (lt_of_le_of_lt key (not_le.mp b_gt)),
end

lemma monotone.le_Inf_image {R S : Type*} [complete_semilattice_Inf R] [complete_linear_order S]
  {f : R → S} (f_incr : monotone f) (A : set R) :
  f (Inf A) ≤ Inf (f '' A) :=
begin
  have := f_incr.dual,
  refine le_Inf _,
  intros x x_in_fA,
  rcases (mem_image f A x).mp x_in_fA with ⟨z, ⟨z_in_A, fz_eq_x⟩⟩,
  by_contra b_gt,
  have key := (f_incr (Inf_le z_in_A)),
  rw fz_eq_x at key,
  exact (lt_self_iff_false x).mp (lt_of_lt_of_le (not_le.mp b_gt) key),
end

lemma antitone.Sup_image_le {R S : Type*} [complete_semilattice_Inf R] [complete_linear_order S]
  {f : R → S} (f_decr : antitone f) (A : set R) :
  Sup (f '' A) ≤ f (Inf A) :=
begin
  refine Sup_le _,
  intros x x_in_fA,
  rcases (mem_image f A x).mp x_in_fA with ⟨z, ⟨z_in_A, fz_eq_x⟩⟩,
  by_contra b_gt,
  have key := (f_decr (Inf_le z_in_A)),
  rw fz_eq_x at key,
  exact (lt_self_iff_false x).mp (lt_of_le_of_lt key (not_le.mp b_gt)),
end

lemma antitone.le_Inf_image {R S : Type*} [complete_semilattice_Sup R] [complete_linear_order S]
  {f : R → S} (f_decr : antitone f) (A : set R) :
  f (Sup A) ≤ Inf (f '' A) :=
begin
  refine le_Inf _,
  intros x x_in_fA,
  rcases (mem_image f A x).mp x_in_fA with ⟨z, ⟨z_in_A, fz_eq_x⟩⟩,
  by_contra b_gt,
  have key := (f_decr (le_Sup z_in_A)),
  rw fz_eq_x at key,
  exact (lt_self_iff_false x).mp (lt_of_lt_of_le (not_le.mp b_gt) key),
end

private lemma continuous_Inf_le_Sup_continuous {R S : Type*}
  [complete_linear_order R] [topological_space R] [order_topology R]
  [complete_linear_order S] [topological_space S] [order_closed_topology S]
  {f : R → S} (f_cont : continuous f)
  (A : set R) (hA : A.nonempty):
  f (Inf A) ≤ Sup (f '' A) :=
begin
  refine le_Sup_iff.mpr _,
  intros b hb,
  have InfA_mem_clA : Inf A ∈ closure A, from Inf_mem_closure hA,
  have aux := @continuous.continuous_on _ _ _ _ f (closure A) f_cont,
  have key := (continuous_on.image_closure aux).trans (closure_mono (show f '' A ⊆ Iic b, from hb)),
  simpa [closure_Iic] using key (mem_image_of_mem f InfA_mem_clA),
end

lemma antitone.Sup_image_eq_apply_Inf {R S : Type*}
  [complete_linear_order R] [topological_space R] [order_topology R]
  [complete_linear_order S] [topological_space S] [order_closed_topology S]
  {f : R → S} (f_decr : antitone f) (f_cont : continuous f)
  (A : set R) (hA : A.nonempty):
  Sup (f '' A) = f (Inf A) :=
le_antisymm (f_decr.Sup_image_le A) (continuous_Inf_le_Sup_continuous f_cont A hA)

lemma antitone.Inf_image_eq_apply_Sup {R S : Type*}
  [complete_linear_order R] [topological_space R] [order_topology R]
  [complete_linear_order S] [topological_space S] [order_closed_topology S]
  {f : R → S} (f_decr : antitone f) (f_cont : continuous f)
  (A : set R) (hA : A.nonempty):
  Inf (f '' A) = f (Sup A) :=
f_decr.dual.Sup_image_eq_apply_Inf f_cont A hA

lemma monotone.Inf_image_eq_apply_Inf {R S : Type*}
  [complete_linear_order R] [topological_space R] [order_topology R]
  [complete_linear_order S] [topological_space S] [order_closed_topology S]
  {f : R → S} (f_incr : monotone f) (f_cont : continuous f)
  (A : set R) (hA : A.nonempty):
  Inf (f '' A) = f (Inf A) :=
f_incr.dual_left.Inf_image_eq_apply_Sup f_cont A hA

lemma Sup_mono_eq_mono_Sup {R S : Type*}
  [complete_linear_order R] [topological_space R] [order_topology R]
  [complete_linear_order S] [topological_space S] [order_closed_topology S]
  {f : R → S} (f_incr : monotone f) (f_cont : continuous f)
  (A : set R) (hA : A.nonempty):
  Sup (f '' A) = f (Sup A) :=
f_incr.dual.Inf_image_eq_apply_Inf f_cont A hA

lemma limsup_eq_Inf_Sup {ι R : Type*}
  [semilattice_sup ι] [nonempty ι]
  [complete_linear_order R] [topological_space R] [order_topology R]
  (a : ι → R) :
  at_top.limsup a = Inf ((λ i, Sup (a '' (Ici i))) '' univ) :=
begin
  refine le_antisymm _ _,
  { rw limsup_eq,
    apply Inf_le_Inf,
    intros x hx,
    simp only [image_univ, mem_range] at hx,
    rcases hx with ⟨j, hj⟩,
    filter_upwards [Ici_mem_at_top j],
    intros i hij,
    rw ← hj,
    exact le_Sup (mem_image_of_mem _ hij), },
  { rw limsup_eq,
    apply le_Inf_iff.mpr,
    intros b hb,
    simp only [mem_set_of_eq, eventually_at_top] at hb,
    rcases hb with ⟨j, hj⟩,
    apply Inf_le_of_le (mem_image_of_mem _ (mem_univ j)),
    apply Sup_le,
    intros x hx,
    simp at hx,
    rcases hx with ⟨k, j_le_k, ak_eq_x⟩,
    rw ← ak_eq_x,
    exact hj k j_le_k, },
end

lemma liminf_eq_Sup_Inf {ι R : Type*}
  [semilattice_sup ι] [nonempty ι]
  [complete_linear_order R] [topological_space R] [order_topology R]
  (a : ι → R) :
  at_top.liminf a = Sup ((λ i, Inf (a '' (Ici i))) '' univ) :=
@limsup_eq_Inf_Sup ι (order_dual R) _ _ _ _ _ a

lemma antitone.liminf_comp_eq_apply_limsup_of_continuous
  {ι R : Type*} [semilattice_sup ι] [nonempty ι]
  [complete_linear_order R] [topological_space R] [order_topology R]
  (a : ι → R) {f : R → R} (f_decr : antitone f) (f_cont : continuous f) :
  at_top.liminf (f ∘ a) = f (at_top.limsup a) :=
begin
  rw [limsup_eq_Inf_Sup, liminf_eq_Sup_Inf,
      ←f_decr.Sup_image_eq_apply_Inf f_cont _ (nonempty_image_iff.mpr (@univ_nonempty ι _))],
  apply congr_arg,
  simp_rw [image_image, function.comp_app, image_univ],
  apply congr_arg,
  funext n,
  rw ← f_decr.Inf_image_eq_apply_Sup f_cont _ (nonempty_image_iff.mpr nonempty_Ici),
  simp_rw image_image,
end

lemma antitone.limsup_comp_eq_apply_liminf_of_continuous
  {ι R : Type*} [semilattice_sup ι] [nonempty ι]
  [complete_linear_order R] [topological_space R] [order_topology R]
  (a : ι → R) {f : R → R} (f_decr : antitone f) (f_cont : continuous f) :
  at_top.limsup (f ∘ a) = f (at_top.liminf a) :=
@antitone.liminf_comp_eq_apply_limsup_of_continuous ι (order_dual R) _ _ _ _ _
  a f f_decr.dual f_cont

end monotone
