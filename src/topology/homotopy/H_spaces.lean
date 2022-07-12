/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

-- import analysis.complex.circle
import topology.compact_open
import topology.homotopy.basic
import topology.homotopy.path

universe u

noncomputable theory

open path continuous_map

open_locale unit_interval

namespace path

variables (X : Type u) [topological_space X]

instance (x y : X) : has_coe (path x y) C(I, X) := ⟨λ γ, γ.1⟩

instance (x y : X) : topological_space (path x y) := topological_space.induced
  (coe : _ → C(I, X)) (by {apply_instance})

end path

namespace H_space

class H_space (X : Type u) [topological_space X]  :=
(Hmul : X × X → X)
(e : X)
(cont' : continuous Hmul)
(Hmul_e_e : Hmul (e, e) = e)
(left_Hmul_e : ∀ x : X,
  @continuous_map.homotopy_rel (X) (X) _ _
  ⟨(λ x : X, Hmul (e, x)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
  ⟨(λ x : X, Hmul (e, x)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
  {e})
(right_Hmul_e : ∀ x : X,
  @continuous_map.homotopy_rel (X) (X) _ _
  ⟨(λ x : X, Hmul (x, e)), (continuous.comp cont'(continuous_id'.prod_mk continuous_const))⟩
  ⟨(λ x : X, Hmul (x, e)), (continuous.comp cont'(continuous_id'.prod_mk continuous_const))⟩
  {e})

notation ` ∨ `:65 := H_space.Hmul

instance topological_group_H_space (G : Type u) [topological_space G] [group G]
  [topological_group G] : H_space G :=
{ Hmul := function.uncurry has_mul.mul,
  e := 1,
  cont' := continuous_mul,
  Hmul_e_e := by {simp only [function.uncurry_apply_pair, mul_one]},
  left_Hmul_e := λ _, continuous_map.homotopy_rel.refl _ _ ,
  right_Hmul_e := λ _, continuous_map.homotopy_rel.refl _ _ }

@[simp]
lemma Hmul_e {G : Type u} [topological_space G] [group G] [topological_group G] :
  (1 : G) = H_space.e := rfl

-- open circle

-- instance S0_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := infer_instance
-- instance S1_H_space : H_space circle := infer_instance
-- instance S3_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry
-- instance S7_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry

variables {X : Type u} [topological_space X]

def loop_space (x : X) : Type u := {f : C(I, X) // f 0 = x ∧ f 1 = x}

instance (x : X) : topological_space (loop_space x) := by {exact subtype.topological_space}

instance (x : X) : has_coe (loop_space x) C(I, X) := {coe := λ g, ⟨g.1⟩}

notation ` Ω ` := loop_space

variable (x : X)

example (Y Z : Type) [topological_space Y] [topological_space Z] [locally_compact_space Y]
[locally_compact_space Z] (g : Y → C(Z, X)) (hg : continuous g) : continuous (λ p : Y × Z, g p.fst p.snd) :=
begin
  let f:= continuous_map.uncurry ⟨g, hg⟩,
  exact f.2,
end

-- lemma continuous_to_loop_space_iff (Y : Type u) [topological_space Y] (g : Y → Ω x) :
--   continuous g ↔ continuous (λ y : Y, λ t : I, g y t) :=
-- begin
--   let g₁ : Y → C(I,X) := λ y, g y,
--   split,
--   { intro h,
--     have hg₁ : continuous g₁,
--     { convert h.subtype_coe,
--       ext t,
--       refl },
--     have H := continuous_uncurry_of_continuous ⟨g₁, hg₁⟩,
--     exact continuous_pi (λ _, continuous.comp H (continuous_id'.prod_mk continuous_const)), },
--   { intro h,

--     suffices hg₁ : continuous g₁,
--     sorry,
--     apply continuous_of_continuous_uncurry,
--     dsimp [function.uncurry],
--     -- exact continuous_pi (λ (t : I), continuous.comp h (continuous_id'.prod_mk continuous_const)),
--     -- suggest,
--     -- library_search,
--     -- continuity,
--     -- simp,
--     -- convert h using 0,
--   },
-- end

abbreviation new_loop_space (x : X) := path x x

instance (x : X) : topological_space (new_loop_space x) := infer_instance


lemma continuous_to_new_loop_space_iff {Y : Type u} [topological_space Y]
  {g : Y → new_loop_space x} : continuous g ↔ continuous (λ p : Y × I, g p.1 p.2) := sorry

example (Y Z : Type u) [topological_space Y] [topological_space Z] (f : Y → X) (hf : continuous f)
: continuous (λ p : Y × Z, f p.1) := continuous.fst' hf

example (Y Z : Type u) [topological_space Y] [topological_space Z] :
  (X × Y) × Z ≃ₜ X × (Y × Z) := homeomorph.prod_assoc X Y Z

def I₀ := {t : I | t.1 ≤ 1/2}

lemma univ_eq_union_halves (α : Type u) : (set.univ : set (α × I)) =
  ((set.univ : set α) ×ˢ I₀) ∪ ((set.univ : set α) ×ˢ I₀ᶜ) :=  by {ext, simp only [set.mem_union_eq,
   set.mem_prod, set.mem_univ, true_and, set.mem_compl_eq], tauto}

-- example (Y Z : Type u) [topological_space Y] [topological_space Z] (f : Y × Z → X)
-- (hY : ∀ z, continuous (λ y, f (y, z))) (hZ : ∀ y, continuous (λ z, f (y, z))) : continuous f :=
-- begin
--   -- have := is_open_p
--   -- suggest,
-- end

instance loop_space_is_H_space (x : X) : H_space (new_loop_space x) :=
{ Hmul := λ ρ, ρ.1.trans ρ.2,
  e := refl _,
  cont' :=
  begin
    sorry;{
    apply (continuous_to_new_loop_space_iff x).mpr,
    rw continuous_iff_continuous_at,
    intro w,
    rw ← continuous_within_at_univ,
    rw univ_eq_union_halves ((new_loop_space x) × (new_loop_space x)),
    -- rw h,
    apply continuous_within_at_union.mpr,
    split,
    {


      -- have H := @continuous_within_at_snd ((new_loop_space x) × (new_loop_space x)) I _ _
      --   (set.univ ×ˢ I₀) w,
      -- have := @continuous_within_at.comp ((new_loop_space x × new_loop_space x) × I) _ X _ _ _,
      -- let ψ := (λ p : ((new_loop_space x × new_loop_space x) × I), ((path.trans p.fst.fst p.fst.snd).1).1),
    -- { have := continuous_within_at.comp' continuous_within_at_snd _,
    --simp [path.trans],
      -- by_cases hw : w.2.1 ≤ 2⁻¹,
      -- simp_rw if_pos,

      -- apply

    },
  -- sorry,
    },
  end,
  Hmul_e_e := sorry,
  left_Hmul_e := sorry,
  right_Hmul_e := sorry}


end H_space
