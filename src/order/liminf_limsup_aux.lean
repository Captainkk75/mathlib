import order.liminf_limsup

-- TODO Figure out what we're keeping here and place in correct file(s). Probably
-- `order/liminf_limsup.lean`. Also add `bliminf` + basic API etc.

noncomputable theory

open set filter function

namespace filter

variables {α β : Type*} (f : filter β) (p q : β → Prop) (u : β → α)

/-- The `blimsup` of a function `u` along a filter `f`, bounded by a predicate `p`, is the infimum
of the `a` such that, eventually for `f`, `p x → u x ≤ a`. -/
def blimsup [conditionally_complete_lattice α] :=
Inf { a | ∀ᶠ x in f, p x → u x ≤ a }

-- Presumably this is true?
lemma blimsup_eq_infi_bsupr [complete_lattice α] :
  f.blimsup p u = ⨅ s ∈ f, ⨆ a (ha : p a ∧ a ∈ s), u a :=
begin
  sorry,
end

-- Is this true? We only need the obviously-true direction!
@[simp] lemma blimsup_or_eq_sup [complete_lattice α] :
  f.blimsup (λ x, p x ∨ q x) u = f.blimsup p u ⊔ f.blimsup q u :=
begin
  sorry,
end

end filter

/-- Do we want to keep this or just rely on `cofinite.blimsup`? -/
def inf_often {α ι : Type*} (p : ι → Prop) (s : ι → set α) : set α :=
{ x | { n | p n ∧ x ∈ s n }.infinite }

lemma inf_often_iff {α ι : Type*} (p : ι → Prop) (s : ι → set α) :
  inf_often p s = cofinite.blimsup p s :=
begin
  simp only [inf_often, filter.blimsup, le_eq_subset, eventually_cofinite, not_forall, exists_prop,
    Inf_eq_sInter],
  ext,
  change {i : ι | p i ∧ x ∈ s i}.infinite ↔ _,
  refine ⟨λ hx t ht, _, λ hx, _⟩,
  { contrapose! ht,
    exact hx.mono (λ i hi, ⟨hi.1, λ hit, ht (hit hi.2)⟩), },
  { contrapose! hx,
    rw not_infinite at hx,
    simp only [mem_sInter, mem_set_of_eq, not_forall, exists_prop],
    exact ⟨{x}ᶜ, by simpa, by simp⟩, },
end

lemma inf_often_mono {α ι : Type*} (p : ι → Prop)
  {s s' : ι → set α} (h : ∀ n, s n ≤ s' n) :
  inf_often p s ≤ inf_often p s' :=
λ x hx, hx.mono (λ n hn, ⟨hn.1, h _ (hn.2)⟩)
