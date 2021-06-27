import geometry.manifold.times_cont_mdiff_map
import geometry.manifold.instances.real

noncomputable theory

open set

def is_maximal {α : Type*} [partial_order α] (a : α) : Prop := ∀ b : α, b ≥ a → b = a

open_locale manifold

section

structure curve {E : Type*} [normed_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
  (M : Type*) [inhabited M] [topological_space M] [charted_space H M]
  [smooth_manifold_with_corners I M] (n : with_top ℕ) extends Cₗ^n⟮𝓘(ℝ), ℝ; I, M⟯ :=
(connected_source    : is_connected source)
(default_value       : ∀ x ∉ source, to_fun x = default M)

variables {E : Type*} [normed_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] {I : model_with_corners ℝ E H}
{M : Type*} [inhabited M] [topological_space M] [charted_space H M]
[smooth_manifold_with_corners I M] (n : with_top ℕ)

namespace curve

instance : has_coe_to_fun (curve I M n) := ⟨_, λ γ, γ.to_fun⟩

protected lemma times_cont_mdiff_on (γ : curve I M n) :
  times_cont_mdiff_on 𝓘(ℝ) I n γ γ.source := γ.times_cont_mdiff_on_to_fun

protected lemma smooth (γ : curve I M ∞) :
  smooth_on 𝓘(ℝ) I γ γ.source := γ.times_cont_mdiff_on_to_fun

@[ext] protected lemma ext {γ σ : curve I M n} (h_src : γ.source = σ.source)
  (h : ∀ x ∈ γ.source, γ x = σ x) : γ = σ :=
begin
  cases γ, cases σ,
  congr',
  ext,
  { exact iff_of_eq (congr_arg (has_mem.mem x) h_src), },
  { intro x,
    by_cases h1 : (x ∈ γ__to_times_cont_mdiff_on_map.source),
    { exact (h x) h1, },
    { have h2 := γ_default_value x h1,
      rw h_src at h1,
      have h3 := σ_default_value x h1,
      simp only [times_cont_mdiff_on_map.to_fun_eq_coe] at h2 h3,
      rw [h2, h3], } }
end

variables {I} {M} {n}

def speed (γ : curve I M n) (t : ℝ) : tangent_space I (γ t) :=
(deriv_within ((ext_chart_at I (γ t)) ∘ γ) γ.source t : E)

instance : has_lt (curve I M n) :=
⟨λ γ₁ γ₂, γ₁.source ⊂ γ₂.source ∧ ∀ x ∈ γ₁.source, γ₁ x = γ₂ x⟩

instance : has_le (curve I M n) :=
⟨λ γ₁ γ₂, γ₁.source ⊆ γ₂.source ∧ ∀ x ∈ γ₁.source, γ₁ x = γ₂ x⟩

instance : partial_order (curve I M n) :=
{ le_refl := λ γ, ⟨subset.rfl, λ x h, by refl⟩,
  le_trans := λ γ σ ρ, λ h1 h2, ⟨subset.trans h1.1 h2.1, λ x h, by rw [h1.2 x h, h2.2 x (h1.1 h)]⟩,
  le_antisymm := λ γ σ, λ h1 h2, by { ext1, exacts [subset.antisymm h1.1 h2.1, λ x hx, h1.2 x hx] },
  ..curve.has_le }

end curve

end
