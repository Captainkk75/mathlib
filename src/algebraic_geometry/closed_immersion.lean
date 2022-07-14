import topology.sheaves.presheaf
import algebraic_geometry.Scheme

universes w v u

/- Formalizing the equivalence of (2) and (4) in
   https://stacks.math.columbia.edu/tag/01QN -/

noncomputable theory

namespace algebraic_geometry

open category_theory
open topological_space
open opposite

section locally_surjective

/-! Let C be a concrete category, X a topological space. -/
variables {C : Type u} [category.{v} C] [concrete_category C] {X : Top.{w}}

/-! Let ℱ, 𝒢 : (opens X)ᵒᵖ -> C be C-valued presheaves on X. -/
variables {ℱ : X.presheaf C} {𝒢 : X.presheaf C}

/-! When U is an object of C, we introduce the notation "Γ_ ℱ U" for
the image under ℱ of the object U, viewed as an object of (opens X)ᵒᵖ. -/
def sections_of_presheaf_on_open
   (ℱ : X.presheaf C) (U : opens X) := (forget C).obj (ℱ.obj (op U))
local notation `Γ_` : 80 := sections_of_presheaf_on_open

/-! When i : V ⟶ U is an inclusion of an open set V into an open set U,
and s ∈ Γ_ ℱ U, we write s|_i for the restriction of s to V. -/
def restrict_along
   {ℱ : X.presheaf C} {U : opens X} {V : opens X}
   (s : Γ_ ℱ U) (i : V ⟶ U) : Γ_ ℱ V := (forget C).map (ℱ.map i.op) s
local infix `|_` : 80 := restrict_along

/-! When T : ℱ ⟶ 𝒢 is a natural transformation, and s ∈ Γ_ ℱ U, we
write T_* s for the image of s under the map T_U : Γ_ ℱ U ⟶ Γ_ 𝒢 U. -/
def map_on_sections {U : opens X} (T : ℱ ⟶ 𝒢) (s : Γ_ ℱ U) :
   Γ_ 𝒢 U := (forget C).map (T.app (op U)) s
local infix ` _* ` : 80 := map_on_sections

/-! A natural transformation T : ℱ ⟶ 𝒢 is **locally surjective** if for
any open set U, section t over U, and x ∈ U, there exists an open set
x ∈ V ⊆ U such that $T_*(s_V) = t|_V$. -/
def is_locally_surjective (T : ℱ ⟶ 𝒢) :=
   ∀ (U : opens X) (t : Γ_ 𝒢 U) (x : X) (hx : x ∈ U),
   ∃ (V : opens X) (ι : V ⟶ U) (hxV : x ∈ V) (s : Γ_ ℱ V),
   T _* s = t |_ ι

end locally_surjective

section closed_immersion

/-! A map between schemes is a closed immersion if the underlying map is a closed embedding of topological spaces, and the pullback natural transformation f_* is locally surjective.
   See item (4) in https://stacks.math.columbia.edu/tag/01QO. -/

variables {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

notation `𝒪_` := LocallyRingedSpace.presheaf
notation f `^#` : 80 := f.val.c

structure is_closed_immersion {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) : Prop :=
    (is_closed_embedding_base : closed_embedding f.val.base)
    (is_locally_surjective : is_locally_surjective (f ^#))

variables (U : opens Y)

-- U as a LocallyRingedSpace
def U_as_LRS : LocallyRingedSpace := Y.restrict U.open_embedding

-- The inclusion morphism U ⟶ Y as a map of LocallyRingedSpaces
def U_to_Y : U_as_LRS U ⟶ Y := Y.of_restrict U.open_embedding

def f_inv_U : opens X := (opens.map (f.val.base)).obj U

def f_inv_U_as_LRS : LocallyRingedSpace :=
   X.restrict (f_inv_U f U).open_embedding

def f_inv_U_to_X : (f_inv_U_as_LRS f U) ⟶ X :=
   X.of_restrict (f_inv_U f U).open_embedding

def f_inv_U_to_Y : (f_inv_U_as_LRS f U) ⟶ Y :=
   f_inv_U_to_X f U ≫ f

-- try using open_immersion.lift? f : X ⟶ Y 𝒪_Y ⟶ f_* 𝒪_X

example {X Y : Top.{v}} {f : X ⟶ Y} (U : opens Y) : opens X :=
begin
   exact f.comap U,
end

-- f⁻¹ U → U

def stuff : X ⟶ Y :=
{ val := _,
  property := _ }

-- how do we define the subscheme f⁻¹ U ⊆ X and the morphism f⁻¹ U ⟶ U?

-- idea: Use continuity of the map of spaces to produce f⁻¹ U as an open *subset*
-- then restrict X to f⁻¹ U the same way as above (might need some massaging using
-- the "open_nhds" predicate)
-- Then build the inclusion morphism f ⁻¹ U ⟶ X and compose with X ⟶ Y
-- idea (for the map): I think there is a coercion lemma that says, if
-- the image lands in an open subscheme, you can convert the map to have that
-- codomain.

-- lemma is_closed_immersion_of_locally
--    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
--    (h : ∀ (y : Y) (U : open_nhds y),
--       @is_closed_immersion _ (Y.restrict U.open_embedding)



end closed_immersion

end algebraic_geometry
