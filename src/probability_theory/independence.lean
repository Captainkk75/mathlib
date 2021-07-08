/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.measure_space
import measure_theory.pi_system
import algebra.big_operators.intervals
import data.finset.intervals

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → set (set α)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → measurable_space α` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `measurable_space.comap f m`.

## Main statements

* TODO: `Indep_of_Indep_sets`: if π-systems are independent as sets of sets, then the
measurable space structures they generate are independent.
* `indep_of_indep_sets`: variant with two π-systems.

## Implementation notes

We provide one main definition of independence:
* `Indep_sets`: independence of a family of sets of sets `pi : ι → set (set α)`.
Three other independence notions are defined using `Indep_sets`:
* `Indep`: independence of a family of measurable space structures `m : ι → measurable_space α`,
* `Indep_set`: independence of a family of sets `s : ι → set α`,
* `Indep_fun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), measurable_space (β i)`, we consider functions `f : Π (i : ι), α → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without a capital letter, for example `indep_fun` is the version of `Indep_fun`
for two functions.

The definition of independence for `Indep_sets` uses finite sets (`finset`). An alternative and
equivalent way of defining independence would have been to use countable sets.
TODO: prove that equivalence.

Most of the definitions and lemma in this file list all variables instead of using the `variables`
keyword at the beginning of a section, for example
`lemma indep.symm {α} {m₁ m₂ : measurable_space α} [measurable_space α] {μ : measure α} ...` .
This is intentional, to be able to control the order of the `measurable_space` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`[measurable_space α]`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/

open measure_theory measurable_space
open_locale big_operators classical

namespace probability_theory

section definitions

/-- A family of sets of sets `π : ι → set (set α)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def Indep_sets {α ι} [measurable_space α] (π : ι → set (set α)) (μ : measure α . volume_tac) :
  Prop :=
∀ (s : finset ι) {f : ι → set α} (H : ∀ i, i ∈ s → f i ∈ π i), μ (⋂ i ∈ s, f i) = ∏ i in s, μ (f i)

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep_sets {α} [measurable_space α] (s1 s2 : set (set α)) (μ : measure α . volume_tac) : Prop :=
∀ t1 t2 : set α, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1 * μ t2

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space α` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def Indep {α ι} (m : ι → measurable_space α) [measurable_space α] (μ : measure α . volume_tac) :
  Prop :=
Indep_sets (λ x, (m x).measurable_set') μ

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep {α} (m₁ m₂ : measurable_space α) [measurable_space α] (μ : measure α . volume_tac) :
  Prop :=
indep_sets (m₁.measurable_set') (m₂.measurable_set') μ

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def Indep_set {α ι} [measurable_space α] (s : ι → set α) (μ : measure α . volume_tac) : Prop :=
Indep (λ i, generate_from {s i}) μ

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def indep_set {α} [measurable_space α] (s t : set α) (μ : measure α . volume_tac) : Prop :=
indep (generate_from {s}) (generate_from {t}) μ

/-- A family of functions defined on the same space `α` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `α` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def Indep_fun {α ι} [measurable_space α] {β : ι → Type*} (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), α → β x) (μ : measure α . volume_tac) : Prop :=
Indep (λ x, measurable_space.comap (f x) (m x)) μ

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def indep_fun {α β γ} [measurable_space α] (mβ : measurable_space β) (mγ : measurable_space γ)
  (f : α → β) (g : α → γ) (μ : measure α . volume_tac) : Prop :=
indep (measurable_space.comap f mβ) (measurable_space.comap g mγ) μ

end definitions

section indep

lemma indep_sets.symm {α} {s₁ s₂ : set (set α)} [measurable_space α] {μ : measure α}
  (h : indep_sets s₁ s₂ μ) :
  indep_sets s₂ s₁ μ :=
by { intros t1 t2 ht1 ht2, rw [set.inter_comm, mul_comm], exact h t2 t1 ht2 ht1, }

lemma indep.symm {α} {m₁ m₂ : measurable_space α} [measurable_space α] {μ : measure α}
  (h : indep m₁ m₂ μ) :
  indep m₂ m₁ μ :=
indep_sets.symm h

lemma indep_sets_of_indep_sets_of_le_left {α} {s₁ s₂ s₃: set (set α)} [measurable_space α]
  {μ : measure α} (h_indep : indep_sets s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
  indep_sets s₃ s₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (set.mem_of_subset_of_mem h31 ht1) ht2

lemma indep_sets_of_indep_sets_of_le_right {α} {s₁ s₂ s₃: set (set α)} [measurable_space α]
  {μ : measure α} (h_indep : indep_sets s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
  indep_sets s₁ s₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (set.mem_of_subset_of_mem h32 ht2)

lemma indep_of_indep_of_le_left {α} {m₁ m₂ m₃: measurable_space α} [measurable_space α]
  {μ : measure α} (h_indep : indep m₁ m₂ μ) (h31 : m₃ ≤ m₁) :
  indep m₃ m₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (h31 _ ht1) ht2

lemma indep_of_indep_of_le_right {α} {m₁ m₂ m₃: measurable_space α} [measurable_space α]
  {μ : measure α} (h_indep : indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) :
  indep m₁ m₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (h32 _ ht2)

lemma indep_sets.union {α} [measurable_space α] {s₁ s₂ s' : set (set α)} {μ : measure α}
  (h₁ : indep_sets s₁ s' μ) (h₂ : indep_sets s₂ s' μ) :
  indep_sets (s₁ ∪ s₂) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  cases (set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂,
  { exact h₁ t1 t2 ht1₁ ht2, },
  { exact h₂ t1 t2 ht1₂ ht2, },
end

@[simp] lemma indep_sets.union_iff {α} [measurable_space α] {s₁ s₂ s' : set (set α)}
  {μ : measure α} :
  indep_sets (s₁ ∪ s₂) s' μ ↔ indep_sets s₁ s' μ ∧ indep_sets s₂ s' μ :=
⟨λ h, ⟨indep_sets_of_indep_sets_of_le_left h (set.subset_union_left s₁ s₂),
    indep_sets_of_indep_sets_of_le_left h (set.subset_union_right s₁ s₂)⟩,
  λ h, indep_sets.union h.left h.right⟩

lemma indep_sets.Union {α ι} [measurable_space α] {s : ι → set (set α)} {s' : set (set α)}
  {μ : measure α} (hyp : ∀ n, indep_sets (s n) s' μ) :
  indep_sets (⋃ n, s n) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  rw set.mem_Union at ht1,
  cases ht1 with n ht1,
  exact hyp n t1 t2 ht1 ht2,
end

lemma indep_sets.inter {α} [measurable_space α] {s₁ s' : set (set α)} (s₂ : set (set α))
  {μ : measure α} (h₁ : indep_sets s₁ s' μ) :
  indep_sets (s₁ ∩ s₂) s' μ :=
λ t1 t2 ht1 ht2, h₁ t1 t2 ((set.mem_inter_iff _ _ _).mp ht1).left ht2

lemma indep_sets.Inter {α ι} [measurable_space α] {s : ι → set (set α)} {s' : set (set α)}
  {μ : measure α} (h : ∃ n, indep_sets (s n) s' μ) :
  indep_sets (⋂ n, s n) s' μ :=
by {intros t1 t2 ht1 ht2, cases h with n h, exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2 }

lemma indep_sets_singleton_iff {α} [measurable_space α] {s t : set α} {μ : measure α} :
  indep_sets {s} {t} μ ↔ μ (s ∩ t) = μ s * μ t :=
⟨λ h, h s t rfl rfl,
  λ h s1 t1 hs1 ht1, by rwa [set.mem_singleton_iff.mp hs1, set.mem_singleton_iff.mp ht1]⟩

end indep

/-! ### Deducing `indep` from `Indep` -/
section from_Indep_to_indep

lemma Indep_sets.indep_sets {α ι} {s : ι → set (set α)} [measurable_space α] {μ : measure α}
  (h_indep : Indep_sets s μ) {i j : ι} (hij : i ≠ j) :
  indep_sets (s i) (s j) μ :=
begin
  intros t₁ t₂ ht₁ ht₂,
  have hf_m : ∀ (x : ι), x ∈ {i, j} → (ite (x=i) t₁ t₂) ∈ s x,
  { intros x hx,
    cases finset.mem_insert.mp hx with hx hx,
    { simp [hx, ht₁], },
    { simp [finset.mem_singleton.mp hx, hij.symm, ht₂], }, },
  have h1 : t₁ = ite (i = i) t₁ t₂, by simp only [if_true, eq_self_iff_true],
  have h2 : t₂ = ite (j = i) t₁ t₂, by simp only [hij.symm, if_false],
  have h_inter : (⋂ (t : ι) (H : t ∈ ({i, j} : finset ι)), ite (t = i) t₁ t₂)
      = (ite (i = i) t₁ t₂) ∩ (ite (j = i) t₁ t₂),
    by simp only [finset.set_bInter_singleton, finset.set_bInter_insert],
  have h_prod : (∏ (t : ι) in ({i, j} : finset ι), μ (ite (t = i) t₁ t₂))
      = μ (ite (i = i) t₁ t₂) * μ (ite (j = i) t₁ t₂),
    by simp only [hij, finset.prod_singleton, finset.prod_insert, not_false_iff,
      finset.mem_singleton],
  rw h1,
  nth_rewrite 1 h2,
  nth_rewrite 3 h2,
  rw [←h_inter, ←h_prod, h_indep {i, j} hf_m],
end

lemma Indep.indep {α ι} {m : ι → measurable_space α} [measurable_space α] {μ : measure α}
  (h_indep : Indep m μ) {i j : ι} (hij : i ≠ j) :
  indep (m i) (m j) μ :=
begin
  change indep_sets ((λ x, (m x).measurable_set') i) ((λ x, (m x).measurable_set') j) μ,
  exact Indep_sets.indep_sets h_indep hij,
end

end from_Indep_to_indep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/

section from_measurable_spaces_to_sets_of_sets
/-! ### Independence of measurable space structures implies independence of generating π-systems -/

lemma Indep.Indep_sets {α ι} [measurable_space α] {μ : measure α} {m : ι → measurable_space α}
  {s : ι → set (set α)} (hms : ∀ n, m n = measurable_space.generate_from (s n))
  (h_indep : Indep m μ) :
  Indep_sets s μ :=
begin
  refine (λ S f hfs, h_indep S (λ x hxS, _)),
  simp_rw hms x,
  exact measurable_set_generate_from (hfs x hxS),
end

lemma indep.indep_sets {α} [measurable_space α] {μ : measure α} {s1 s2 : set (set α)}
  (h_indep : indep (generate_from s1) (generate_from s2) μ) :
  indep_sets s1 s2 μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (measurable_set_generate_from ht1) (measurable_set_generate_from ht2)

end from_measurable_spaces_to_sets_of_sets

section from_pi_systems_to_measurable_spaces
/-! ### Independence of generating π-systems implies independence of measurable space structures -/

private lemma indep_sets.indep_aux {α} {m2 : measurable_space α}
  {m : measurable_space α} {μ : measure α} [probability_measure μ] {p1 p2 : set (set α)}
  (h2 : m2 ≤ m) (hp2 : is_pi_system p2) (hpm2 : m2 = generate_from p2)
  (hyp : indep_sets p1 p2 μ) {t1 t2 : set α} (ht1 : t1 ∈ p1) (ht2m : m2.measurable_set' t2) :
  μ (t1 ∩ t2) = μ t1 * μ t2 :=
begin
  let μ_inter := μ.restrict t1,
  let ν := (μ t1) • μ,
  have h_univ : μ_inter set.univ = ν set.univ,
  by rw [measure.restrict_apply_univ, measure.smul_apply, measure_univ, mul_one],
  haveI : finite_measure μ_inter := @restrict.finite_measure α _ t1 μ ⟨measure_lt_top μ t1⟩,
  rw [set.inter_comm, ←@measure.restrict_apply α _ μ t1 t2 (h2 t2 ht2m)],
  refine ext_on_measurable_space_of_generate_finite m p2 (λ t ht, _) h2 hpm2 hp2 h_univ ht2m,
  have ht2 : m.measurable_set' t,
  { refine h2 _ _,
    rw hpm2,
    exact measurable_set_generate_from ht, },
  rw [measure.restrict_apply ht2, measure.smul_apply, set.inter_comm],
  exact hyp t1 t ht1 ht,
end

lemma indep_sets.indep {α} {m1 m2 : measurable_space α} {m : measurable_space α}
  {μ : measure α} [probability_measure μ] {p1 p2 : set (set α)} (h1 : m1 ≤ m) (h2 : m2 ≤ m)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hpm1 : m1 = generate_from p1)
  (hpm2 : m2 = generate_from p2) (hyp : indep_sets p1 p2 μ) :
  indep m1 m2 μ :=
begin
  intros t1 t2 ht1 ht2,
  let μ_inter := μ.restrict t2,
  let ν := (μ t2) • μ,
  have h_univ : μ_inter set.univ = ν set.univ,
  by rw [measure.restrict_apply_univ, measure.smul_apply, measure_univ, mul_one],
  haveI : finite_measure μ_inter := @restrict.finite_measure α _ t2 μ ⟨measure_lt_top μ t2⟩,
  rw [mul_comm, ←@measure.restrict_apply α _ μ t2 t1 (h1 t1 ht1)],
  refine ext_on_measurable_space_of_generate_finite m p1 (λ t ht, _) h1 hpm1 hp1 h_univ ht1,
  have ht1 : m.measurable_set' t,
  { refine h1 _ _,
    rw hpm1,
    exact measurable_set_generate_from ht, },
  rw [measure.restrict_apply ht1, measure.smul_apply, mul_comm],
  exact indep_sets.indep_aux h2 hp2 hpm2 hyp ht ht2,
end

end from_pi_systems_to_measurable_spaces

section indep_set
/-! ### Independence of measurable sets

We prove the following equivalences on `indep_set`, for measurable sets `s, t`.
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ indep_sets {s} {t} μ`.
-/

variables {α : Type*} [measurable_space α] {s t : set α} (S T : set (set α))

lemma indep_set_iff_indep_sets_singleton (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  (μ : measure α . volume_tac) [probability_measure μ] :
  indep_set s t μ ↔ indep_sets {s} {t} μ :=
⟨indep.indep_sets,  λ h, indep_sets.indep
  (generate_from_le (λ u hu, by rwa set.mem_singleton_iff.mp hu))
  (generate_from_le (λ u hu, by rwa set.mem_singleton_iff.mp hu)) (is_pi_system.singleton s)
  (is_pi_system.singleton t) rfl rfl h⟩

lemma indep_set_iff_measure_inter_eq_mul (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  (μ : measure α . volume_tac) [probability_measure μ] :
  indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t :=
(indep_set_iff_indep_sets_singleton hs_meas ht_meas μ).trans indep_sets_singleton_iff

lemma indep_sets.indep_set_of_mem (hs : s ∈ S) (ht : t ∈ T) (hs_meas : measurable_set s)
  (ht_meas : measurable_set t) (μ : measure α . volume_tac) [probability_measure μ]
  (h_indep : indep_sets S T μ) :
  indep_set s t μ :=
(indep_set_iff_measure_inter_eq_mul hs_meas ht_meas μ).mpr (h_indep s t hs ht)

end indep_set

section pi_systems

/-- From a set of finsets `S` and a family of sets of sets `π`, define the set of sets `s` that can
be written as `s = ⋂ x ∈ t, f x` for some `t` in `S` and sets `f x ∈ π x`.
If `S` is union-closed and `π` is a family of π-systems, then it is a π-system.
The name expresses that it is the union over `t ∈ S` of sets that are written as intersections.
The π-systems used to prove Komogorov's 0-1 law are of that form. -/
def pi_Union_Inter {α ι} (π : ι → set (set α)) (S : set (finset ι)) : set (set α) :=
{s : set α | ∃ (t : finset ι) (htS : t ∈ S) (f : ι → set α) (hf : ∀ x, x ∈ t → f x ∈ π x),
  s = ⋂ x (hxt : x ∈ t), f x}

lemma sup_closed_tail_finset_set (N : ℕ) :
  sup_closed {s : finset ℕ | ∃ r : ℕ, s = finset.Ico N (N+r+1)} :=
begin
  refine sup_closed_of_totally_ordered _ _,
  rintros s1 s2 ⟨r1, hs1⟩ ⟨r2, hs2⟩,
  rw [hs1, hs2],
  cases le_total r1 r2,
  { exact or.inr (finset.Ico.subset (le_refl N) (by simp [h])), },
  { exact or.inl (finset.Ico.subset (le_refl N) (by simp [h])), },
end

lemma finset.Inter_inter_Inter_eq_Inter_union_if {α ι} (s1 s2 : finset ι) (f1 f2 : ι → set α) :
  (⋂ i (hp : i ∈ s1), f1 i) ∩ (⋂ i (hp : i ∈ s2), f2 i)
    = ⋂ i (hp : i ∈ s1 ∪ s2),
      (if i ∈ s1 then f1 i else set.univ) ∩ (if i ∈ s2 then f2 i else set.univ) :=
begin
  simp_rw ←set.inf_eq_inter,
  rw binfi_inf_binfi_eq_binfi_union_if (λ i:ι, i ∈ s1) (λ i:ι, i ∈ s2) f1 f2,
  simp_rw [set.top_eq_univ, set.inf_eq_inter, set.Inter],
  simp [heq_iff_eq],
end

lemma is_pi_system_pi_Union_Inter {α ι} (pi : ι → set (set α))
  (hpi : ∀ x, is_pi_system (pi x)) (S : set (finset ι)) (h_sup : sup_closed S) :
  is_pi_system (pi_Union_Inter pi S) :=
begin
  rintros t1 t2 ⟨p1, hp1S, f1, hf1m, ht1_eq⟩ ⟨p2, hp2S, f2, hf2m, ht2_eq⟩ h_nonempty,
  simp_rw [pi_Union_Inter, set.mem_set_of_eq],
  let g := λ n, (ite (n ∈ p1) (f1 n) set.univ) ∩ (ite (n ∈ p2) (f2 n) set.univ),
  use [p1 ∪ p2, h_sup p1 p2 hp1S hp2S, g],
  have h_inter_eq : t1 ∩ t2 = ⋂ (i : ι) (hp : i ∈ p1 ∪ p2), g i,
  { rw [ht1_eq, ht2_eq],
    exact finset.Inter_inter_Inter_eq_Inter_union_if p1 p2 f1 f2, },
  refine ⟨λ n hn, _, h_inter_eq⟩,
  simp_rw g,
  split_ifs with hn1 hn2,
  { refine hpi n (f1 n) (f2 n) (hf1m n hn1) (hf2m n hn2) _,
    rw h_inter_eq at h_nonempty,
    by_contra h,
    rw set.not_nonempty_iff_eq_empty at h,
    have h_empty :(⋂ (i : ι) (hp : i ∈ p1 ∪ p2), g i) = ∅,
    { refine le_antisymm (set.Inter_subset_of_subset n _) (set.empty_subset _),
      refine set.Inter_subset_of_subset hn _,
      have h_gn_eq : g n = f1 n ∩ f2 n,
      { change (ite (n ∈ p1) (f1 n) set.univ) ∩ (ite (n ∈ p2) (f2 n) set.univ) = f1 n ∩ f2 n,
        simp only [if_true, hn1, hn2], },
      rw [h_gn_eq, h], },
    exact (set.not_nonempty_iff_eq_empty.mpr h_empty) h_nonempty, },
  { simp [hf1m n hn1], },
  { simp [hf2m n h], },
  { exact absurd hn (by simp [hn1, h]), },
end

lemma generate_from_pi_Union_Inter_le {α ι} {m : measurable_space α}
  {s : ι → measurable_space α} (h : ∀ n, s n ≤ m) (pi : ι → set (set α)) (S : set (finset ι))
  (hpis : ∀ n, s n = generate_from (pi n)) :
  generate_from (pi_Union_Inter pi S) ≤ m :=
begin
  refine generate_from_le (λ t ht, _),
  rcases ht with ⟨ht_p, ht_p_mem, ft, hft_mem_pi, ht_eq⟩,
  rw ht_eq,
  refine finset.measurable_set_bInter _ (λ x hx_mem, (h x) _ _),
  rw hpis x,
  exact measurable_set_generate_from (hft_mem_pi x hx_mem),
end

lemma subset_pi_Union_Inter {α ι} {pi : ι → set (set α)} {S : set (finset ι)}
  (h_univ : ∀ i, set.univ ∈ (pi i)) {i : ι} {s : finset ι} (hsS : s ∈ S) (his : i ∈ s) :
  pi i ⊆ pi_Union_Inter pi S :=
begin
  refine λ t ht_pii, ⟨s, hsS, (λ j, ite (j = i) t set.univ), _⟩,
  split,
  { intros m h_pm,
    split_ifs,
    { rwa h, },
    { exact h_univ m,}, },
  { ext,
    simp_rw set.mem_Inter,
    split; intro hx1,
    { intros i h_p_i,
      split_ifs,
      { exact hx1, },
      { exact set.mem_univ _, }, },
    { simpa using hx1 i his, }, },
end

lemma le_generate_from_pi_Union_Inter {α ι} {m : measurable_space α}
  {pi : ι → set (set α)} (S : set (finset ι)) (h_univ : ∀ n, set.univ ∈ (pi n)) {x : ι}
  {t : finset ι} (htS : t ∈ S) (hxt : x ∈ t) (hpix : m = measurable_space.generate_from (pi x)) :
  m ≤ generate_from (pi_Union_Inter pi S) :=
by { rw hpix, exact generate_from_le_generate_from (subset_pi_Union_Inter h_univ htS hxt) }

lemma measurable_subset_pi_Union_Inter {α ι} (m : ι → measurable_space α)
  {S : set (finset ι)} {i : ι} {p : finset ι} (hpS : p ∈ S) (hpi : i ∈ p) :
  set_of (m i).measurable_set' ⊆ pi_Union_Inter (λ n, (m n).measurable_set') S :=
begin
  intros t ht,
  let g := λ n, ite (n=i) t set.univ,
  use [p, hpS, g],
  split,
  { intros j hj,
    change (m j).measurable_set' (ite (j=i) t set.univ),
    split_ifs with hji,
    { rwa hji, },
    { exact @measurable_set.univ α (m j), }, },
  { ext,
    simp_rw [set.mem_Inter, g],
    split; intro hx,
    { intros j hj,
      split_ifs; simp [hx], },
    { simpa using (hx i hpi), }, },
end

lemma pi_Union_Inter_subset_measurable {α ι} (m : ι → measurable_space α) (S : set (finset ι)) :
  pi_Union_Inter (λ n, (m n).measurable_set') S
    ⊆ (⨆ (i : ι) (hi : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p), m i).measurable_set' :=
begin
  intros t ht,
  rw [pi_Union_Inter, set.mem_set_of_eq] at ht,
  rcases ht with ⟨pt, hpt, ft, ht_m, ht_eq⟩,
  have h_i : ∀ i, i ∈ pt
    → (⨆ (i : ι) (hi : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p), m i).measurable_set' (ft i),
  { intros i hi,
    have h_le : m i ≤ (⨆ (i : ι) (hi : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p), m i),
    { have hi' : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p,
      { use pt,
        exact ⟨hpt, hi⟩, },
      exact le_bsupr i hi', },
    exact h_le (ft i) (ht_m i hi), },
  subst ht_eq,
  exact @finset.measurable_set_bInter _ _
    ((⨆ (i : ι) (hi : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p), m i)) _ pt (λ i hipt, h_i i hipt),
end

lemma bsupr_measurable_space_eq_generate_from_pi_Union_Inter {α ι} (m : ι → measurable_space α)
  (S : set (finset ι)) :
  (⨆ (i : ι) (hi : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p), m i) = measurable_space.generate_from
    (pi_Union_Inter (λ n, (m n).measurable_set') S) :=
begin
  refine le_antisymm _ _,
  { refine bsupr_le (λ i hi, _),
    rcases hi with ⟨p, hpS, hpi⟩,
    rw ← @generate_from_measurable_set α (m i),
    exact generate_from_le_generate_from (measurable_subset_pi_Union_Inter m hpS hpi), },
  { rw ← @generate_from_measurable_set α
      (⨆ (i : ι) (hi : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p), m i),
    exact generate_from_le_generate_from (pi_Union_Inter_subset_measurable m S), },
end

end pi_systems

section indep_of_indep_sets_of_pi_system

lemma pi_system_indep_insert {α ι} [measurable_space α] {μ : measure α} {pi : ι → set (set α)}
  (hp_ind : Indep_sets pi μ) {a : ι} {S : finset ι} (haS : a ∉ S) :
  indep_sets (pi_Union_Inter pi {S}) (pi a) μ :=
begin
  rintros t1 t2 ⟨s, hs_mem, ft1, hft1_mem, ht1_eq⟩ ht2_mem_pia,
  rw set.mem_singleton_iff at hs_mem,
  simp_rw hs_mem at hft1_mem,
  let f1 := λ n, ite (n=a) t2 (ite (n ∈ S) (ft1 n) set.univ),
  have h_f1_mem : ∀ n, n ∈ insert a S → f1 n ∈ pi n,
  { intros n hn_mem,
    simp_rw [f1],
    cases (finset.mem_insert.mp hn_mem) with hn_mem hn_mem,
    { simp [hn_mem, ht2_mem_pia], },
    { have hn_ne_a : n ≠ a, from λ hna, by { rw hna at hn_mem, exact haS hn_mem, },
      simp [hn_ne_a, hn_mem, hft1_mem n hn_mem], }, },
  have h_f1_mem_S : ∀ n, n ∈ S → f1 n ∈ pi n, from λ x hxS, h_f1_mem x (by simp [hxS]),
  have h_t1 : t1 = ⋂ (n : ι) (h : n ∈ S), f1 n,
  { suffices h_forall : ∀ n (h : n ∈ S), f1 n = ft1 n,
    { rw ht1_eq,
      congr' with n,
      congr' with hnS,
      congr',
      intros hns hnS _,
      simp only [(h_forall n hnS).symm], },
    intros n hnS,
    have hn_ne_a : n ≠ a, from λ hna, by { rw hna at hnS, exact haS hnS, },
    simp_rw [f1],
    simp [hnS, hn_ne_a], },
  have h_μ_t1 : μ t1 = ∏ n in S, μ (f1 n), by rw [h_t1, ←hp_ind S h_f1_mem_S],
  have h_t2 : t2 = f1 a, by { simp_rw [f1], simp, },
  have h_μ_inter : μ (t1 ∩ t2) = ∏ n in insert a S, μ (f1 n),
  { have h_t1_inter_t2 : t1 ∩ t2 = ⋂ (n : ι) (h : n ∈ insert a S), f1 n,
      by rw [h_t1, h_t2, finset.set_bInter_insert, set.inter_comm],
    rw [h_t1_inter_t2, ←hp_ind (insert a S) h_f1_mem], },
  rw [h_μ_inter, finset.prod_insert haS, h_t2, mul_comm, h_μ_t1],
end

lemma Indep_sets.Indep {α ι} (m : measurable_space α) (s : ι → measurable_space α)
  (μ : @measure_theory.measure α m) [probability_measure μ] (h : ∀ n, s n ≤ m)
  (pi : ι → set (set α)) (h_pi : ∀ n, is_pi_system (pi n)) (hp_univ : ∀ n, set.univ ∈ pi n)
  (hps : ∀ n, s n = generate_from (pi n)) (hp_ind : Indep_sets pi μ) :
  Indep s μ :=
begin
  refine finset.induction (by simp [measure_univ]) _,
  intros a S ha_notin_S h_rec f hf_m,
  have hf_m_S : ∀ x, x ∈ S → (s x).measurable_set' (f x), from λ x hx, hf_m x (by simp [hx]),
  rw [finset.set_bInter_insert, finset.prod_insert ha_notin_S, ←h_rec hf_m_S],
  let p_ := pi_Union_Inter pi {S},
  set S_ := generate_from p_ with hS_eq_generate,
  have h_indep : indep S_ (s a) μ,
  { have hp_ : is_pi_system p_,
      from is_pi_system_pi_Union_Inter pi h_pi {S} (sup_closed_singleton S),
    have hS : S_ ≤ m, from generate_from_pi_Union_Inter_le h pi {S} hps,
    exact indep_sets.indep hS (h a) hp_ (h_pi a) hS_eq_generate (hps a)
      (pi_system_indep_insert hp_ind ha_notin_S), },
  refine h_indep.symm (f a) (⋂ (n : ι) (H : n ∈ S), f n) _ _,
  { exact hf_m a (by simp), },
  { have h_le : ∀ n : ι, n ∈ S → s n ≤ S_,
      from (λ n hn, le_generate_from_pi_Union_Inter {S} hp_univ (set.mem_singleton _) hn (hps n)),
    have h_S_f : ∀ i (hi : i ∈ S), S_.measurable_set' (f i),
      from λ i hi, (h_le i hi) (f i) (hf_m_S i hi),
    exact @finset.measurable_set_bInter α ι S_ f _ (λ i hi, h_S_f i hi), },
end

end indep_of_indep_sets_of_pi_system

end probability_theory
