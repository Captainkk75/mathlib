import category_theory.bicategory.natural_transformation
import category_theory.bicategory.coherence_tactic

namespace category_theory

open category bicategory
open_locale bicategory

universes w₁ w₂ v₁ v₂ u₁ u₂

variables {B : Type u₁} [bicategory.{w₁ v₁} B] {C : Type u₂} [bicategory.{w₂ v₂} C]
variables {F G H : oplax_functor B C}

namespace oplax_nat_trans

local attribute[-simp]
  whisker_right_naturality_comp
  whisker_right_naturality_comp_assoc
  whisker_left_naturality_comp
  whisker_left_naturality_comp_assoc
  naturality_comp
  naturality_comp_assoc

set_option profiler true
/-- Vertical composition of oplax natural transformations. -/
@[simps]
def vcomp' (η : oplax_nat_trans F G) (θ : oplax_nat_trans G H) : oplax_nat_trans F H :=
{ app := λ a, η.app a ≫ θ.app a,
  naturality := λ a b f,
    (α_ _ _ _).inv ≫ η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫
      η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv,
  naturality_id' := sorry,
  naturality_naturality' := sorry,
  naturality_comp' := λ a b c f g, by
  {
    calc _ = 𝟙 _  ⊗≫
    η.naturality (f ≫ g) ▷ θ.app c ⊗≫
      η.app a ◁ (θ.naturality (f ≫ g) ≫ _ ◁ H.map_comp f g) ⊗≫ 𝟙 _ : _
    ... = 𝟙 _ ⊗≫
    (η.naturality (f ≫ g) ≫ _ ◁ G.map_comp f g) ▷ θ.app c ⊗≫
      η.app a ◁ G.map f ◁ θ.naturality g ⊗≫
        η.app a ◁ θ.naturality f ▷ H.map g ⊗≫ 𝟙 _ : _
    ... =  𝟙 _ ⊗≫
     F.map_comp f g ▷ η.app c ▷ θ.app c ⊗≫
      F.map f ◁ η.naturality g ▷ θ.app c ⊗≫
        (η.naturality f ▷ _ ≫
          _ ◁ θ.naturality g) ⊗≫
            η.app a ◁ θ.naturality f ▷ H.map g ⊗≫ 𝟙 _  :  _
    ... =  _ : _,
    { assoc_simps, coherence },
    { rw naturality_comp, assoc_simps, coherence },
    { rw naturality_comp, assoc_simps, coherence },
    { rw ←whisker_exchange, assoc_simps, coherence }
  } }

end oplax_nat_trans

end category_theory
