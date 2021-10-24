/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.category.Top
import category_theory.limits.concrete_category
import category_theory.limits.shapes.kernel_pair

/-!
# Gluing Topological spaces

Given a family of gluing data, consisting of
1. An index type `ι`
2. A topological space `U i` for each `i : ι`.
3. An open subset `V i j ⊆ U i` for each `i j : ι`.
4. A transition map `f i j : V i j ⟶ V j i` for each `i j : ι`.
such that
5. `V i i = U i`.
6. `f i i` is the identity.
7. `f i j x ∈ V j k` for all `x ∈ V i j ∩ V i k`.
8. `f i j ≫ f j k = f i k`.

We can then glue the topological spaces `U i` along `V i j`.

THe construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `Top.gluing_data`: A structure containing the family of gluing data.
* `Top.gluing_data.glued`: The glued topological space.
    This is defined as the coequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API can
    be used.
* `Top.gluing_data.imm`: The immersion `imm i : U i ⟶ glued` for each `i : ι`.
* `Top.gluing_data.rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `f i j x = y`. See `Top.gluing_data.imm_eq_iff_rel`.

## Main results

* `Top.gluing_data.is_open_iff`: A set in `glued` is open iff its preimage along each `imm i` is
    open.
* `Top.gluing_data.imm_jointly_surjective`: The `imm i`s are jointly surjective.
* `Top.gluing_data.glue_condition` : `f i j ≫ imm j = imm i`.
* `Top.gluing_data.rel_equiv`: `rel` is an equivalence relation.
* `Top.gluing_data.imm_eq_iff_rel`: `imm i x = imm j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `Top.gluing_data.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `Top.gluing_data.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `Top.gluing_data.preimage_image_eq_preimage_f`: The preimage of the image of some `U ⊆ U i` is
    given by the preimage along `f j i`.
* `Top.gluing_data.imm_open_embedding`: Each of the `imm i`s are open embeddings.

-/

noncomputable theory

open topological_space category_theory

universes v u

namespace category_theory.limits
open category_theory.limits.walking_cospan
local attribute [tidy] tactic.case_bash

variables {C : Type*} [category C] {X Y Z : C}
section
variables {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g)

def pullback_cone.symm : pullback_cone g f :=
{ X := c.X,
  π :=
    { app := by { rintro (_|_|_), exacts [c.π.app none, c.π.app right, c.π.app left] },
      naturality' := λ A B f, by
      { cases f,
        cases A; simp; erw category.id_comp,
        cases f_1, simpa using c.π.naturality hom.inr, simpa using c.π.naturality hom.inl } } }

@[simp] lemma pullback_cone.symm_X : c.symm.X = c.X := rfl
@[simp] lemma pullback_cone.symm_fst : c.symm.fst = c.snd := rfl
@[simp] lemma pullback_cone.symm_snd : c.symm.snd = c.fst := rfl
@[simp] lemma pullback_cone.symm_π_app_none  : c.symm.π.app none  = c.π.app none  := rfl
@[simp] lemma pullback_cone.symm_π_app_left  : c.symm.π.app left  = c.π.app right := rfl
@[simp] lemma pullback_cone.symm_π_app_right : c.symm.π.app right = c.π.app left  := rfl

def pullback_cone.symm_is_limit (c : pullback_cone f g) (h : is_limit c) : is_limit c.symm :=
{ lift := λ s, h.lift (pullback_cone.symm s),
  fac' := λ s, by { rintros (_|_|_); apply h.fac },
  uniq' := λ s m h', h.uniq' (pullback_cone.symm s) m
    (by { rintros (_|_|_), exacts [h' none, h' right, h' left] }) }

variables (f) (g)

lemma has_pullback_symmetry [has_pullback f g] : has_pullback g f :=
⟨⟨⟨_, pullback_cone.symm_is_limit _ (limit.is_limit _)⟩⟩⟩

section
local attribute[instance] has_pullback_symmetry

@[simps]
def pullback_symmetry [has_pullback f g] :
  pullback f g ≅ pullback g f :=
is_limit.cone_point_unique_up_to_iso
  (pullback_cone.symm_is_limit _ (limit.is_limit (cospan f g)))
  (@@limit.is_limit _ _ _ (has_pullback_symmetry f g))

lemma pullback_symmetry_hom_comp_fst [has_pullback f g] :
  (pullback_symmetry f g).hom ≫ pullback.fst = pullback.snd := by simp

end

section left_iso
variable [is_iso f]

def pullback_cone_of_left_iso : pullback_cone f g :=
{ X := Y, π := { app := by { rintro (_|_|_), exacts [g, g ≫ inv f, 𝟙 _] }, naturality' := λ A B i,
  begin
    cases i, rcases A with (_|_|_); simp [category.id_comp g], refl,
    cases i_1; simp [category.id_comp g]
  end } }

@[simp] lemma pullback_cone_of_left_iso_X :
  (pullback_cone_of_left_iso f g).X = Y := rfl

@[simp] lemma pullback_cone_of_left_iso_fst :
  (pullback_cone_of_left_iso f g).fst = g ≫ inv f := rfl

@[simp] lemma pullback_cone_of_left_iso_snd :
  (pullback_cone_of_left_iso f g).snd = 𝟙 _ := rfl

@[simp] lemma pullback_cone_of_left_iso_π_app_none :
  (pullback_cone_of_left_iso f g).π.app none = g := rfl

@[simp] lemma pullback_cone_of_left_iso_π_app_left :
  (pullback_cone_of_left_iso f g).π.app left = g ≫ inv f := rfl

@[simp] lemma pullback_cone_of_left_iso_π_app_right :
  (pullback_cone_of_left_iso f g).π.app right = 𝟙 _ := rfl

def pullback_cone_of_left_iso_is_limit :
  is_limit (pullback_cone_of_left_iso f g) :=
pullback_cone.is_limit_aux' _ (λ s, ⟨s.snd, by simp [← s.condition_assoc]⟩)

@[priority 100]
instance has_pullback_of_left_iso : has_pullback f g :=
⟨⟨⟨_, pullback_cone_of_left_iso_is_limit f g⟩⟩⟩

instance pullback_snd_iso_of_left_iso : is_iso (pullback.snd : pullback f g ⟶ _) :=
begin
  have := (pullback_cone_of_left_iso_is_limit f g).cone_point_unique_up_to_iso_hom_comp
    (limit.is_limit (cospan f g)) right,
  have : pullback.snd = _ := (iso.hom_comp_eq_id _).mp this,
  rw this,
  apply_instance
end

end left_iso


section right_iso
variable [is_iso g]

def pullback_cone_of_right_iso : pullback_cone f g :=
{ X := X, π := { app := by { rintro (_|_|_), exacts [f, 𝟙 _, f ≫ inv g] }, naturality' := λ A B i,
  begin
    cases i, rcases A with (_|_|_); simp [category.id_comp f], refl,
    cases i_1; simp [category.id_comp f]
  end } }

@[simp] lemma pullback_cone_of_right_iso_X :
  (pullback_cone_of_right_iso f g).X = X := rfl

@[simp] lemma pullback_cone_of_right_iso_fst :
  (pullback_cone_of_right_iso f g).fst = 𝟙 _ := rfl

@[simp] lemma pullback_cone_of_right_iso_snd :
  (pullback_cone_of_right_iso f g).snd = f ≫ inv g := rfl

@[simp] lemma pullback_cone_of_right_iso_π_app_none :
  (pullback_cone_of_right_iso f g).π.app none = f := rfl

@[simp] lemma pullback_cone_of_right_iso_π_app_left :
  (pullback_cone_of_right_iso f g).π.app left = 𝟙 _ := rfl

@[simp] lemma pullback_cone_of_right_iso_π_app_right :
  (pullback_cone_of_right_iso f g).π.app right = f ≫ inv g := rfl

def pullback_cone_of_right_iso_is_limit :
  is_limit (pullback_cone_of_right_iso f g) :=
pullback_cone.is_limit_aux' _ (λ s, ⟨s.fst, by simp [s.condition_assoc]⟩)

@[priority 100]
instance has_pullback_of_right_iso : has_pullback f g :=
⟨⟨⟨_, pullback_cone_of_right_iso_is_limit f g⟩⟩⟩

instance pullback_snd_iso_of_right_iso : is_iso (pullback.fst : pullback f g ⟶ _) :=
begin
  have := (pullback_cone_of_right_iso_is_limit f g).cone_point_unique_up_to_iso_hom_comp
    (limit.is_limit (cospan f g)) left,
  have : pullback.fst = _ := (iso.hom_comp_eq_id _).mp this,
  rw this,
  apply_instance
end

end right_iso

end

variable (f : X ⟶ Y)

instance has_kernel_pair_of_mono [mono f] : has_pullback f f :=
⟨⟨⟨_, (is_kernel_pair.id_of_mono f).is_limit⟩⟩⟩

lemma fst_eq_snd_of_mono_eq [mono f] : (pullback.fst : pullback f f ⟶ _) = pullback.snd :=
((is_kernel_pair.id_of_mono f).is_limit.fac (get_limit_cone (cospan f f)).cone left).symm.trans
  ((is_kernel_pair.id_of_mono f).is_limit.fac (get_limit_cone (cospan f f)).cone right : _)

@[simp]
lemma pullback_symmetry_hom_of_eq_fun [mono f] :
(@pullback_symmetry _ _ _ _ _ f f _).hom = 𝟙 _ :=
begin
  have : (pullback_symmetry f f).hom ≫ pullback.fst = 𝟙 _ ≫ pullback.snd := by simp,
  rw fst_eq_snd_of_mono_eq at this,
  exact mono.right_cancellation _ _ this,
end

instance fst_iso_of_mono_eq [mono f] : is_iso (pullback.fst : pullback f f ⟶ _) :=
begin
  have := (is_kernel_pair.id_of_mono f).is_limit.cone_point_unique_up_to_iso_hom_comp
    (limit.is_limit (cospan f f)) left,
  have : pullback.fst = _ := (iso.hom_comp_eq_id _).mp this,
  rw this,
  apply_instance
end

instance snd_iso_of_mono_eq [mono f] : is_iso (pullback.snd : pullback f f ⟶ _) :=
by {rw ←fst_eq_snd_of_mono_eq, apply_instance }

end category_theory.limits
open category_theory.limits
namespace Top
/--
A family of gluing data consists of
1. An index type `ι`
2. A topological space `U i` for each `i : ι`.
3. An open subset `V i j ⊆ U i` for each `i j : ι`.
4. A transition map `f i j : V i j ⟶ V j i` for each `i j : ι`.
such that
5. `V i i = U i`.
6. `f i i` is the identity.
7. `f i j x ∈ V j k` for all `x ∈ V i j ∩ V i k`.
8. `f i j ≫ f j k = f i k`.

We can then glue the topological spaces `U i` along `V i j`.
-/
@[nolint has_inhabited_instance]
structure glue_data : Type (u+1) :=
  (ι : Type u)
  (U : ι → Top.{u})
  (V : ι × ι → Top.{u})
  (f : Π i j, V (i, j) ⟶ U i)
  (f_open : ∀ i j, open_embedding (f i j))
  (f_id : ∀ i, is_iso (f i i))
  (t : Π i j, V (i, j) ⟶ V (j, i))
  (t_id : ∀ i, t i i = 𝟙 _)
  (t' : Π i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i))
  (t_fac : ∀ i j k, t' i j k ≫ pullback.snd = pullback.fst ≫ t i j)
  (cocycle : ∀ i j k , t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _)

attribute [simp] glue_data.t_id
attribute [instance] glue_data.f_id
attribute [reassoc] glue_data.t_fac glue_data.cocycle


namespace glue_data

variable (D : glue_data.{u})

instance (i j : D.ι) : mono (D.f i j) :=
(Top.mono_iff_injective _).mpr (D.f_open i j).to_embedding.inj

@[simp] lemma t'_iij (i j : D.ι) : D.t' i i j = (pullback_symmetry _ _).hom :=
begin
  have eq₁ := D.t_fac i i j,
  have eq₂ := (is_iso.eq_comp_inv (D.f i i)).mpr (@pullback.condition _ _ _ _ _ _ (D.f i j) _),
  rw [D.t_id, category.comp_id, eq₂] at eq₁,
  have eq₃ := (is_iso.eq_comp_inv (D.f i i)).mp eq₁,
  rw [category.assoc, ←pullback.condition, ←category.assoc] at eq₃,
  exact mono.right_cancellation _ _
    ((mono.right_cancellation _ _ eq₃).trans (pullback_symmetry_hom_comp_fst _ _).symm)
end

lemma t'_jii (i j : D.ι) : D.t' j i i = pullback.fst ≫ D.t j i ≫ inv pullback.snd :=
by { rw [←category.assoc, ←D.t_fac], simp }

lemma t'_iji (i j : D.ι) : D.t' i j i = pullback.fst ≫ D.t i j ≫ inv pullback.snd :=
by { rw [←category.assoc, ←D.t_fac], simp }

@[simp, reassoc, elementwise] lemma t_inv (i j : D.ι) :
  D.t i j ≫ D.t j i = 𝟙 _ :=
begin
  have eq : (pullback_symmetry (D.f i i) (D.f i j)).hom = pullback.snd ≫ inv pullback.fst,
  simp,
  have := D.cocycle i j i,
  rw [D.t'_iij, D.t'_jii, D.t'_iji, fst_eq_snd_of_mono_eq, eq] at this,
  simp only [category.assoc, is_iso.inv_hom_id_assoc] at this,
  rw [←is_iso.eq_inv_comp, ←category.assoc, is_iso.comp_inv_eq] at this,
  simpa using this,
end

instance t_is_iso (i j : D.ι) : is_iso (D.t i j) :=
⟨⟨D.t j i, D.t_inv _ _, D.t_inv _ _⟩⟩

instance t'_is_iso (i j k : D.ι) : is_iso (D.t' i j k) :=
⟨⟨D.t' j k i ≫ D.t' k i j, D.cocycle _ _ _, D.cocycle _ _ _⟩⟩

/-- (Implementation) The disjoint union of `U i`. -/
def sigma_opens : Top := ∐ D.U

/-- (Implementation) The disjoint union of `V i j`. -/
def sigma_inters : Top := ∐ D.V

/-- (Implementation) The projection `∐ D.inters ⟶ ∐ D.U` via left projection. -/
def left_imm : D.sigma_inters ⟶ D.sigma_opens :=
sigma.desc (λ ⟨i, j⟩, D.f i j ≫ sigma.ι D.U i)

/-- (Implementation) The projection `∐ D.inters ⟶ ∐ D.U` via right projection. -/
def right_imm : D.sigma_inters ⟶ D.sigma_opens :=
sigma.desc (λ ⟨i, j⟩, D.t i j ≫ D.f j i ≫ sigma.ι D.U j)

/-- (Implementation) The diagram to take colimit of. -/
def diagram := parallel_pair D.left_imm D.right_imm

/-- The glued topological space given a family of gluing data. -/
def glued : Top :=
coequalizer D.left_imm D.right_imm

/-- (Implementation) The projection `∐ D.U ⟶ D.glued` given by the colimit. -/
def π : D.sigma_opens ⟶ D.glued :=
coequalizer.π _ _

instance π_epi : epi D.π :=
coequalizer.π_epi

lemma π_surjective : function.surjective D.π :=
(Top.epi_iff_surjective D.π).mp infer_instance

/-- The open immersion `D.U i ⟶ D.glued` for each `i`. -/
def imm (i : D.ι) : D.U i ⟶ D.glued :=
sigma.ι _ _ ≫ D.π

lemma is_open_iff (U : set D.glued) : is_open U ↔ ∀ i, is_open (D.imm i ⁻¹' U) :=
by { rw [coequalizer_is_open_iff, colimit_is_open_iff], refl }

lemma imm_jointly_surjective (x : D.glued) : ∃ i (y : D.U i), D.imm i y = x :=
begin
  rcases D.π_surjective x with ⟨x', rfl⟩,
  rw ← (show (coprod_iso_sigma _).inv _ = x', from congr_fun (coprod_iso_sigma _).hom_inv_id x'),
  rcases (coprod_iso_sigma _).hom x' with ⟨i, y⟩,
  exact ⟨i, y, by simpa⟩
end

@[simp, elementwise]
lemma glue_condition (i j : D.ι) :
  D.t i j ≫ D.f j i ≫ D.imm j = D.f i j ≫ D.imm i :=
begin
  ext x,
  symmetry,
  simpa [π, left_imm, right_imm] using continuous_map.congr_fun
    (coequalizer.condition D.left_imm D.right_imm) ((sigma.ι D.V (i, j) : _) x),
end

def pullback_preimage {X Y Z : Top.{v}} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y)
  (h : f x = g y) : (pullback f g : Top) :=
(limit.is_limit (cospan _ _)).lift
  (@pullback_cone.mk Top _ _ _ _ f g ⟨punit⟩
    ⟨λ _, x, by continuity⟩ ⟨λ _, y, by continuity⟩
    (by { ext a, cases a, simp[h] })) punit.star

@[simp] lemma pullback_preimage_fst {X Y Z : Top.{v}} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y)
  (h : f x = g y) :
  (pullback.fst : pullback f g ⟶ _) (pullback_preimage f g x y h) = x :=
by { unfold pullback_preimage, simp }

@[simp] lemma pullback_preimage_snd {X Y Z : Top.{v}} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y)
  (h : f x = g y) :
  (pullback.snd : pullback f g ⟶ _) (pullback_preimage f g x y h) = y :=
by { unfold pullback_preimage, simp }

def rel (a b : Σ i, D.U i) : Prop :=
  a = b ∨ ∃ (x : D.V (a.1, b.1)) , D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2

lemma rel_equiv : equivalence D.rel :=
⟨ λ x, or.inl (refl x),
  λ a b h,
  begin
    rcases h with (⟨⟨⟩⟩|⟨x,e₁,e₂⟩), exact or.inl rfl,
    right,
    use (D.t _ _ x), simp[e₁, e₂]
  end,
  begin
    rintros ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩ (⟨⟨⟩⟩|⟨x,e₁,e₂⟩), exact id,
    rintro (⟨⟨⟩⟩|⟨y,e₃,e₄⟩), exact or.inr ⟨x,e₁,e₂⟩,
    let z : (pullback (D.f j i) (D.f j k) : Top) :=
      pullback_preimage (D.f j i) (D.f j k) (D.t i j x) y (e₂.trans e₃.symm),
    have eq₁ : (D.t j i) ((pullback.fst : _ ⟶ D.V _) z) = x := by simp,
    have eq₂ : (pullback.snd : _ ⟶ D.V _) z = _ := pullback_preimage_snd _ _ _ _ _,
    clear_value z,
    right,
    use (pullback.fst : _ ⟶ D.V (i, k)) (D.t' _ _ _ z),
    dsimp only at *,
    cases e₁, cases e₃, cases e₄, cases eq₁, cases eq₂, simp,
    have h₁ : D.t' j i k ≫ pullback.fst ≫ D.f i k = pullback.fst ≫ D.t j i ≫ D.f i j,
    { rw ←D.t_fac_assoc, congr' 1, exact pullback.condition },
    have h₂ : D.t' j i k ≫ pullback.fst ≫ D.t i k ≫ D.f k i =
      pullback.snd ≫ D.t j k ≫ D.f k j,
    { rw ←D.t_fac_assoc,
      apply @epi.left_cancellation _ _ _ _ (D.t' k j i),
      rw [D.cocycle_assoc, D.t_fac_assoc, D.t_inv_assoc],
      exact pullback.condition.symm },
    exact ⟨continuous_map.congr_fun h₁ z, continuous_map.congr_fun h₂ z⟩
  end⟩

open category_theory.limits.walking_parallel_pair

lemma eqv_gen_of_π_eq {x y : ∐ D.U} (h : D.π x = D.π y) :
  eqv_gen (types.coequalizer_rel (D.left_imm) (D.right_imm)) x y :=
begin
  change colimit.ι D.diagram one x = colimit.ι D.diagram one y at h,
  have : colimit.ι (D.diagram ⋙ forget _) one x = colimit.ι (D.diagram ⋙ forget _) one y,
  { rw ←ι_preserves_colimits_iso_hom,
    simp[h] },
  have :
    (colimit.ι (D.diagram ⋙ forget _) _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).hom) _ =
    (colimit.ι (D.diagram ⋙ forget _) _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).hom) _ :=
    (congr_arg (colim.map (diagram_iso_parallel_pair (D.diagram ⋙ forget _)).hom
    ≫ (colimit.iso_colimit_cocone (types.coequalizer_limit _ _)).hom) this : _),
  simp only [eq_to_hom_refl, types_comp_apply, colimit.ι_map_assoc,
    diagram_iso_parallel_pair_hom_app, colimit.iso_colimit_cocone_ι_hom, types_id_apply] at this,
  exact quot.eq.1 this,
end

lemma inv_image.equivalence {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β)
  (h : equivalence r) : equivalence (inv_image r f) :=
⟨λ _, h.1 _, λ _ _ x, h.2.1 x, inv_image.trans r f h.2.2⟩

lemma imm_eq_iff_rel (i j : D.ι) (x : D.U i) (y : D.U j) :
  D.imm i x = D.imm j y ↔ D.rel ⟨i, x⟩ ⟨j, y⟩ :=
begin
  split,
  { intro h,
    rw ← (show _ = sigma.mk i x, from congr_fun (coprod_iso_sigma D.U).inv_hom_id _),
    rw ← (show _ = sigma.mk j y, from congr_fun (coprod_iso_sigma D.U).inv_hom_id _),
    change inv_image D.rel (coprod_iso_sigma D.U).hom _ _,
    simp only [Top.coprod_iso_sigma_inv_app],
    rw ←relation.eqv_gen_iff_of_equivalence (inv_image.equivalence _ _ D.rel_equiv),
    refine relation.eqv_gen_mono _ (D.eqv_gen_of_π_eq h : _),
    rintros _ _ ⟨x⟩,
    rw ← (show (coprod_iso_sigma _).inv _ = x, from congr_fun (coprod_iso_sigma _).hom_inv_id x),
    generalize : (coprod_iso_sigma D.V).hom x = x',
    rcases x' with ⟨⟨i,j⟩,y⟩,
    unfold inv_image left_imm right_imm,
    simp only [opens.inclusion_to_fun, Top.comp_app, coprod_iso_sigma_inv_app,
      category_theory.limits.colimit.ι_desc_apply, cofan.mk_ι_app,
      coprod_iso_sigma_hom_app, continuous_map.to_fun_eq_coe],
    erw [Top.coprod_iso_sigma_hom_app, Top.coprod_iso_sigma_hom_app],
    exact or.inr ⟨y, by simp⟩ },
  { rintro (⟨⟨⟩⟩ | ⟨_, e₁, e₂⟩),
    refl, dsimp only at *, cases e₁, cases e₂, simp }
end

lemma imm_injective (i : D.ι) : function.injective (D.imm i) :=
begin
  intros x y h,
  rcases (D.imm_eq_iff_rel _ _ _ _).mp h with (⟨⟨⟩⟩| ⟨_,e₁,e₂⟩),
  refl,
  dsimp only at *,
  cases e₁, cases e₂, simp
end

instance imm_mono (i : D.ι) : mono (D.imm i) :=
(Top.mono_iff_injective _).mpr (D.imm_injective _)

local attribute [elementwise] is_iso.hom_inv_id is_iso.inv_hom_id

lemma image_inter (i j : D.ι) :
  set.range (D.imm i) ∩ set.range (D.imm j) = set.range (D.f i j ≫ D.imm _) :=
begin
  ext x,
  split,
  { rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩,
    have := (D.imm_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm),
    rcases this with (⟨⟨⟩⟩|⟨y,e₁,e₂⟩),
    exact ⟨inv (D.f i i) x₁, by simp[eq₁]⟩,
    dsimp only at *,
    cases e₁, cases eq₁,
    exact ⟨y, by simpa⟩ },
  { rintro ⟨x, hx⟩,
    exact ⟨⟨D.f i j x, hx⟩, ⟨D.f j i (D.t _ _ x), by simp[←hx]⟩⟩ }
end

lemma preimage_range (i j : D.ι) :
  D.imm j ⁻¹' (set.range (D.imm i)) = set.range (D.f j i) :=
by rw [ ←set.preimage_image_eq (set.range (D.f j i)) (D.imm_injective j), ←set.image_univ,
        ←set.image_univ, ←set.image_comp, ←coe_comp, set.image_univ,set.image_univ,
        ←image_inter, set.preimage_range_inter]

lemma preimage_image_eq_preimage_f (i j : D.ι) (U : set (D.U i)) :
D.imm j ⁻¹' (D.imm i '' U) = D.f _ _ '' ((D.t j i ≫ D.f _ _) ⁻¹' U) :=
begin
  have : D.f _ _ ⁻¹' (D.imm j ⁻¹' (D.imm i '' U)) = (D.t j i ≫ D.f _ _) ⁻¹' U,
  { ext x,
    conv_rhs { rw ← set.preimage_image_eq U (D.imm_injective _) },
    generalize : D.imm i '' U = U',
    simp },
  rw [←this, set.image_preimage_eq_inter_range],
  symmetry,
  apply set.inter_eq_self_of_subset_left,
  rw ← D.preimage_range i j,
  exact set.preimage_mono (set.image_subset_range _ _),
end

lemma open_image_open (i : D.ι) (U : opens (D.U i)) : is_open (D.imm i '' U) :=
begin
  rw is_open_iff,
  intro j,
  rw preimage_image_eq_preimage_f,
  apply (D.f_open _ _).is_open_map,
  apply (D.t j i ≫ D.f i j).continuous_to_fun.is_open_preimage,
  exact U.property
end

lemma imm_open_embedding (i : D.ι) : open_embedding (D.imm i) :=
open_embedding_of_continuous_injective_open
  (D.imm i).continuous_to_fun (D.imm_injective i) (λ U h, D.open_image_open i ⟨U, h⟩)

end glue_data

end Top
#lint
