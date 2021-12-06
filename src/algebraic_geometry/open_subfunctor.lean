import algebraic_geometry.Scheme
import category_theory.limits.functor_category
import algebraic_geometry.open_immersion
import algebraic_geometry.presheafed_space.gluing
import category_theory.limits.yoneda
import category_theory.limits.opposites

universes v u
noncomputable theory

open category_theory category_theory.limits algebraic_geometry
namespace algebraic_geometry.Scheme

variables {C : Type u} [category.{v} C]

/-- An open cover of `X` consists of a family of open immersions into `X`,
and for each `x : X` an open immersion (indexed by `f x`) that covers `x`.

This is merely a coverage in the Zariski pretopology, and it would be optimal
if we could reuse the existing API about pretopologies, However, since such a
coverage in the pretopology usually contains a proper class of immersions, it is quite hard to
glue them, reason about finite covers, etc.
-/
structure open_cover (X : Scheme.{u}) :=
(J : Type u)
(obj : Π (j : J), Scheme)
(map : Π (j : J), obj j ⟶ X)
(f : X.carrier → J)
(covers : ∀ x, x ∈ set.range ((map (f x)).1.base))
(is_open : ∀ x, is_open_immersion (map x) . tactic.apply_instance)

attribute [instance] open_cover.is_open

variables {X Y Z : Scheme.{u}} (𝒰 : open_cover X) (f : X ⟶ Z) (g : Y ⟶ Z)
variables [∀ x, has_pullback (𝒰.map x ≫ f) g]

def affine_cover (X : Scheme) : open_cover X :=
{ J := X.carrier,
  obj := λ x, Spec.obj $ opposite.op (X.local_affine x).some_spec.some,
  map := λ x, ((X.local_affine x).some_spec.some_spec.some.inv ≫
    X.to_LocallyRingedSpace.of_restrict _ : _),
  f := λ x, x,
  is_open := λ x, begin
    apply_with PresheafedSpace.is_open_immersion.comp { instances := ff },
    apply_instance,
    apply PresheafedSpace.is_open_immersion.of_restrict,
  end,
  covers :=
  begin
    intro x,
    erw coe_comp,
    rw [set.range_comp, set.range_iff_surjective.mpr, set.image_univ],
    erw subtype.range_coe_subtype,
    exact (X.local_affine x).some.2,
    rw ← Top.epi_iff_surjective,
    change epi ((SheafedSpace.forget _).map (LocallyRingedSpace.forget_to_SheafedSpace.map _)),
    apply_instance
  end }

instance localization_unit_is_iso (R : CommRing) :
  is_iso (CommRing.of_hom $ algebra_map R (localization.away (1 : R))) :=
is_iso.of_iso (is_localization.at_one R (localization.away (1 : R))).to_ring_equiv.to_CommRing_iso

instance localization_unit_is_iso' (R : CommRing) :
  @is_iso CommRing _ R _ (CommRing.of_hom $ algebra_map R (localization.away (1 : R))) :=
by { cases R, exact algebraic_geometry.Scheme.localization_unit_is_iso _ }

lemma is_open_immersion.open_range (f : X ⟶ Y) [H : is_open_immersion f] :
  is_open (set.range f.1.base) := H.base_open.open_range

namespace open_cover

@[simps]
def pullback_cover {W : Scheme} (f : W ⟶ X) : open_cover W :=
{ J := 𝒰.J,
  obj := λ x, pullback f (𝒰.map x),
  map := λ x, pullback.fst,
  f := λ x, 𝒰.f (f.1.base x),
  covers := λ x, begin
    rw ← (show _ = (pullback.fst : pullback f (𝒰.map (𝒰.f (f.1.base x))) ⟶ _).1.base,
      from preserves_pullback.iso_hom_fst (Scheme.forget ⋙
        LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _) f
      (𝒰.map (𝒰.f (f.1.base x)))),
    rw [coe_comp, set.range_comp, set.range_iff_surjective.mpr, set.image_univ,
      Top.pullback_fst_range],
    rcases 𝒰.covers (f.1.base x) with ⟨y, h⟩,
    exact ⟨y, h.symm⟩,
    { rw ← Top.epi_iff_surjective, apply_instance }
  end }

def bind_covers (f : Π (x : 𝒰.J), open_cover (𝒰.obj x)) : open_cover X :=
{ J := Σ (i : 𝒰.J), (f i).J,
  obj := λ x, (f x.1).obj x.2,
  map := λ x, (f x.1).map x.2 ≫ 𝒰.map x.1,
  f := λ x, ⟨_, (f _).f (𝒰.covers x).some⟩,
  covers := λ x,
  begin
    let y := (𝒰.covers x).some,
    have hy : (𝒰.map (𝒰.f x)).val.base y = x := (𝒰.covers x).some_spec,
    rcases (f (𝒰.f x)).covers y with ⟨z, hz⟩,
    change x ∈ set.range (((f (𝒰.f x)).map ((f (𝒰.f x)).f y) ≫ 𝒰.map (𝒰.f x)).1.base),
    use z,
    erw comp_apply,
    rw [hz, hy],
  end }

local attribute [reducible] CommRing.of CommRing.of_hom

instance val_base_is_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] : is_iso f.1.base :=
(Scheme.forget ⋙
      LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _).map_is_iso f

def affine_basis_cover_of_affine (R : CommRing) : open_cover (Spec.obj (opposite.op R)) :=
{ J := R,
  obj := λ r, Spec.obj (opposite.op $ CommRing.of $ localization.away r),
  map := λ r, Spec.map (quiver.hom.op (algebra_map R (localization.away r) : _)),
  f := λ x, 1,
  covers := λ r,
  begin
    rw set.range_iff_surjective.mpr ((Top.epi_iff_surjective _).mp _),
    { exact trivial },
    { apply_instance }
  end,
  is_open := λ x, algebraic_geometry.basic_open_is_open_immersion x }

section end

include 𝒰

/--
Every open cover of a quasi-compact scheme can be refined into a finite subcover.
-/
def finite_subcover [H : compact_space X.carrier] : open_cover X :=
begin
  have := @@compact_space.elim_nhds_subcover _ H
    (λ (x : X.carrier), set.range ((𝒰.map (𝒰.f x)).1.base))
    (λ x, (is_open_immersion.open_range (𝒰.map (𝒰.f x))).mem_nhds (𝒰.covers x)),
  let t := this.some,
  have h : ∀ (x : X.carrier), ∃ (y : t), x ∈ set.range ((𝒰.map (𝒰.f y)).1.base),
  { intro x,
    have h' : x ∈ (⊤ : set X.carrier) := trivial,
    rw [← classical.some_spec this, set.mem_Union] at h',
    rcases h' with ⟨y,_,⟨hy,rfl⟩,hy'⟩,
    exact ⟨⟨y,hy⟩,hy'⟩ },
  exact
  { J := t,
    obj := λ x, 𝒰.obj (𝒰.f x.1),
    map := λ x, 𝒰.map (𝒰.f x.1),
    f := λ x, (h x).some,
    covers := λ x, (h x).some_spec }
end

instance [H : compact_space X.carrier] : fintype 𝒰.finite_subcover.J :=
by { delta finite_subcover, apply_instance }

end open_cover

def affine_basis_cover (X : Scheme) : open_cover X :=
X.affine_cover.bind_covers (λ x, open_cover.affine_basis_cover_of_affine _)

lemma affine_basis_cover_map_range (X : Scheme)
  (x : X.carrier) (r : (X.local_affine x).some_spec.some) :
  set.range (X.affine_basis_cover.map ⟨x, r⟩).1.base =
    (X.affine_cover.map x).1.base '' (prime_spectrum.basic_open r).1 :=
begin
  erw [coe_comp, set.range_comp],
  congr,
  exact (prime_spectrum.localization_away_comap_range (localization.away r) r : _)
end

lemma affine_basis_cover_is_basis (X : Scheme) :
  topological_space.is_topological_basis
    { x : set X.carrier | ∃ a : X.affine_basis_cover.J, x =
      set.range ((X.affine_basis_cover.map a).1.base) } :=
begin
  apply topological_space.is_topological_basis_of_open_of_nhds,
  { rintros _ ⟨a, rfl⟩,
    exact is_open_immersion.open_range (X.affine_basis_cover.map a) },
  { rintros a U haU hU,
    rcases X.affine_cover.covers a with ⟨x, e⟩,
    let U' := (X.affine_cover.map (X.affine_cover.f a)).1.base ⁻¹' U,
    have hxU' : x ∈ U' := by { rw ← e at haU, exact haU },
    rcases prime_spectrum.is_basis_basic_opens.exists_subset_of_mem_open hxU'
      ((X.affine_cover.map (X.affine_cover.f a)).1.base.continuous_to_fun.is_open_preimage _ hU)
      with ⟨_,⟨_,⟨s,rfl⟩,rfl⟩,hxV,hVU⟩,
    refine ⟨_,⟨⟨_,s⟩,rfl⟩,_,_⟩; erw affine_basis_cover_map_range,
    { exact ⟨x,hxV,e⟩ },
    { rw set.image_subset_iff, exact hVU } }
end


namespace open_cover

def glued_cover_t' (x y z : 𝒰.J) :
  pullback (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _)
    (pullback.fst : pullback (𝒰.map x) (𝒰.map z) ⟶ _) ⟶
  pullback (pullback.fst : pullback (𝒰.map y) (𝒰.map z) ⟶ _)
    (pullback.fst : pullback (𝒰.map y) (𝒰.map x) ⟶ _) :=
begin
  refine (pullback_right_pullback_fst_iso _ _ _).hom ≫ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_right_pullback_fst_iso _ _ _).inv,
  refine pullback.map _ _ _ _ (pullback_symmetry _ _).hom (𝟙 _) (𝟙 _) _ _,
  { simp [pullback.condition] },
  { simp }
end

@[simp, reassoc]
lemma glued_cover_t'_fst_fst (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_fst_snd (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_snd_fst (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_snd_snd (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
by { delta glued_cover_t', simp }

lemma glued_cover_cocycle_fst (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ glued_cover_t' 𝒰 y z x ≫ glued_cover_t' 𝒰 z x y ≫ pullback.fst =
    pullback.fst :=
by apply pullback.hom_ext; simp

lemma glued_cover_cocycle_snd (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ glued_cover_t' 𝒰 y z x ≫ glued_cover_t' 𝒰 z x y ≫ pullback.snd =
    pullback.snd :=
by apply pullback.hom_ext; simp [pullback.condition]

lemma glued_cover_cocycle (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ glued_cover_t' 𝒰 y z x ≫ glued_cover_t' 𝒰 z x y = 𝟙 _ :=
begin
  apply pullback.hom_ext; simp_rw [category.id_comp, category.assoc],
  apply glued_cover_cocycle_fst,
  apply glued_cover_cocycle_snd,
end

@[simps]
def glued_cover : Scheme.glue_data.{u} :=
{ ι := 𝒰.J,
  U := 𝒰.obj,
  V := λ ⟨x, y⟩, pullback (𝒰.map x) (𝒰.map y),
  f := λ x y, pullback.fst,
  f_id := λ x, infer_instance,
  t := λ x y, (pullback_symmetry _ _).hom,
  t_id := λ x, by simpa,
  t' := λ x y z, glued_cover_t' 𝒰 x y z,
  t_fac := λ x y z, by apply pullback.hom_ext; simp,
  cocycle := λ x y z, glued_cover_cocycle 𝒰 x y z,
  f_open := λ x, infer_instance }

abbreviation glued := 𝒰.glued_cover.glued

def from_glued : 𝒰.glued ⟶ X :=
begin
  fapply multicoequalizer.desc,
  exact λ x, (𝒰.map x),
  rintro ⟨x, y⟩,
  change pullback.fst ≫ _ = ((pullback_symmetry _ _).hom ≫ pullback.fst) ≫ _,
  simpa using pullback.condition
end

@[simp, reassoc]
lemma imm_from_glued (x : 𝒰.J) :
  𝒰.glued_cover.imm x ≫ 𝒰.from_glued = 𝒰.map x :=
multicoequalizer.π_desc _ _ _ _ _

lemma from_glued_injective : function.injective 𝒰.from_glued.1.base :=
begin
  intros x y h,
  rcases 𝒰.glued_cover.imm_jointly_surjective x with ⟨i, x, rfl⟩,
  rcases 𝒰.glued_cover.imm_jointly_surjective y with ⟨j, y, rfl⟩,
  simp_rw [← comp_apply, ← SheafedSpace.comp_base, ← LocallyRingedSpace.comp_val] at h,
  erw [imm_from_glued, imm_from_glued] at h,
  let e := (Top.pullback_cone_is_limit _ _).cone_point_unique_up_to_iso
    (is_limit_of_has_pullback_of_preserves_limit (Scheme.forget ⋙
      LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _)
      (𝒰.map i) (𝒰.map j)),
  rw 𝒰.glued_cover.imm_eq_iff,
  right,
  use e.hom ⟨⟨x,y⟩, h⟩,
  simp_rw ← comp_apply,
  split,
  { erw is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.left,
    refl },
  { erw pullback_symmetry_hom_comp_fst,
    erw is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right,
    refl }
end

instance from_glued_stalk_iso (x : 𝒰.glued_cover.glued.carrier) :
  is_iso (PresheafedSpace.stalk_map 𝒰.from_glued.val x) :=
begin
  rcases 𝒰.glued_cover.imm_jointly_surjective x with ⟨i, x, rfl⟩,
  have := PresheafedSpace.stalk_map.congr_hom _ _
    (congr_arg subtype.val $ 𝒰.imm_from_glued i) x,
  erw PresheafedSpace.stalk_map.comp at this,
  rw ← is_iso.eq_comp_inv at this,
  rw this,
  apply_instance,
end

lemma from_glued_open_map : is_open_map 𝒰.from_glued.1.base :=
begin
  intros U hU,
  rw is_open_iff_forall_mem_open,
  intros x hx,
  rw 𝒰.glued_cover.is_open_iff at hU,
  use 𝒰.from_glued.val.base '' U ∩ set.range (𝒰.map (𝒰.f x)).1.base,
  use set.inter_subset_left _ _,
  split,
  { rw ← set.image_preimage_eq_inter_range,
    apply (show is_open_immersion (𝒰.map (𝒰.f x)), by apply_instance).base_open.is_open_map,
    convert hU (𝒰.f x) using 1,
    rw ← imm_from_glued, erw coe_comp, rw set.preimage_comp,
    congr' 1,
    refine set.preimage_image_eq _ 𝒰.from_glued_injective },
  { exact ⟨hx, 𝒰.covers x⟩ }
end

lemma from_glued_open_embedding : open_embedding 𝒰.from_glued.1.base :=
open_embedding_of_continuous_injective_open (by continuity) 𝒰.from_glued_injective
  𝒰.from_glued_open_map

instance : epi 𝒰.from_glued.val.base :=
begin
  rw Top.epi_iff_surjective,
  intro x,
  rcases 𝒰.covers x with ⟨y, h⟩,
  use (𝒰.glued_cover.imm (𝒰.f x)).1.base y,
  rw ← comp_apply,
  rw ← 𝒰.imm_from_glued (𝒰.f x) at h,
  exact h
end

instance from_glued_open_immersion : is_open_immersion 𝒰.from_glued :=
SheafedSpace.is_open_immersion.of_stalk_iso _ 𝒰.from_glued_open_embedding

instance : is_iso 𝒰.from_glued :=
begin
  apply is_iso_of_reflects_iso _ (forget ⋙ LocallyRingedSpace.forget_to_SheafedSpace ⋙
    SheafedSpace.forget_to_PresheafedSpace),
  change @is_iso (PresheafedSpace _) _ _ _ 𝒰.from_glued.val,
  apply PresheafedSpace.is_open_immersion.to_iso,
end

def glue_morphism {Y : Scheme} (f : ∀ x, 𝒰.obj x ⟶ Y)
  (hf : ∀ x y, (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _) ≫ f x = pullback.snd ≫ f y) :
  X ⟶ Y :=
begin
  refine inv 𝒰.from_glued ≫ _,
  fapply multicoequalizer.desc,
  exact f,
  rintro ⟨i, j⟩,
  change pullback.fst ≫ f i = (_ ≫ _) ≫ f j,
  erw pullback_symmetry_hom_comp_fst,
  exact hf i j
end

lemma imm_glue_morphism {Y : Scheme} (f : ∀ x, 𝒰.obj x ⟶ Y)
  (hf : ∀ x y, (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _) ≫ f x = pullback.snd ≫ f y)
  (x : 𝒰.J) : (𝒰.map x) ≫ 𝒰.glue_morphism f hf = f x :=
begin
  rw [← imm_from_glued, category.assoc],
  erw [is_iso.hom_inv_id_assoc, multicoequalizer.π_desc],
end

end open_cover

def glue_data.open_cover (D : Scheme.glue_data) : open_cover D.glued :=
{ J := D.ι,
  obj := D.U,
  map := D.imm,
  f := λ x, (D.imm_jointly_surjective x).some,
  covers := λ x, ⟨_, (D.imm_jointly_surjective x).some_spec.some_spec⟩ }

/-- (Xᵢ ×[Z] Y) ×[X] Xⱼ -/
def V (x y : 𝒰.J) : Scheme :=
pullback ((pullback.fst : pullback ((𝒰.map x) ≫ f) g ⟶ _) ≫ (𝒰.map x)) (𝒰.map y)

def t (x y : 𝒰.J) : V 𝒰 f g x y ⟶ V 𝒰 f g y x :=
begin
  haveI : has_pullback (pullback.snd ≫ 𝒰.map x ≫ f) g :=
    has_pullback_assoc_symm (𝒰.map y) (𝒰.map x) (𝒰.map x ≫ f) g,
  haveI : has_pullback (pullback.snd ≫ 𝒰.map y ≫ f) g :=
    has_pullback_assoc_symm (𝒰.map x) (𝒰.map y) (𝒰.map y ≫ f) g,
  refine (pullback_symmetry _ _).hom ≫ _,
  refine (pullback_assoc _ _ _ _).inv ≫ _,
  change pullback _ _ ⟶ pullback _ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_assoc _ _ _ _).hom,
  refine pullback.map _ _ _ _ (pullback_symmetry _ _).hom (𝟙 _) (𝟙 _) _ _,
  rw [pullback_symmetry_hom_comp_snd_assoc, pullback.condition_assoc, category.comp_id],
  rw [category.comp_id, category.id_comp]
end

@[simp, reassoc]
lemma t_fst_fst (x y : 𝒰.J) : t 𝒰 f g x y ≫ pullback.fst ≫ pullback.fst = pullback.snd :=
by { delta t, simp }

@[simp, reassoc]
lemma t_fst_snd (x y : 𝒰.J) :
  t 𝒰 f g x y ≫ pullback.fst ≫ pullback.snd = pullback.fst ≫ pullback.snd :=
by { delta t, simp }

@[simp, reassoc]
lemma t_snd (x y : 𝒰.J) :
  t 𝒰 f g x y ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
by { delta t, simp }

lemma t_id (x : 𝒰.J) : t 𝒰 f g x x = 𝟙 _ :=
begin
  apply pullback.hom_ext; rw category.id_comp,
  apply pullback.hom_ext,
  { rw ← cancel_mono (𝒰.map x),
    simp [pullback.condition] },
  { simp },
  { rw ← cancel_mono (𝒰.map x),
    simp [pullback.condition] }
end

abbreviation fV (x y : 𝒰.J) : V 𝒰 f g x y ⟶ pullback ((𝒰.map x) ≫ f) g := pullback.fst

/-- (Xᵢ ×[Z] Y) ×[X] Xⱼ ×[Xᵢ ×[Z] Y] (Xᵢ ×[Z] Y) ×[X] Xₖ  -/
def t' (x y z : 𝒰.J) :
  pullback (fV 𝒰 f g x y) (fV 𝒰 f g x z) ⟶ pullback (fV 𝒰 f g y z) (fV 𝒰 f g y x) :=
begin
  refine (pullback_right_pullback_fst_iso _ _ _).hom ≫ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_right_pullback_fst_iso _ _ _).inv,
  refine pullback.map _ _ _ _ (t 𝒰 f g x y) (𝟙 _) (𝟙 _) _ _,
  { simp [← pullback.condition] },
  { simp }
end

section end

@[simp, reassoc]
lemma t'_fst_fst_fst (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.fst ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_fst_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.fst ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_fst_fst (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.snd ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.snd ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
by { delta t', simp, }

lemma cocycle_fst_fst_fst (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.fst ≫ pullback.fst ≫
  pullback.fst = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
by simp

lemma cocycle_fst_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.fst ≫ pullback.fst ≫
  pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by simp

lemma cocycle_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.snd :=
by simp

lemma cocycle_snd_fst_fst (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.snd ≫ pullback.fst ≫
  pullback.fst = pullback.snd ≫ pullback.fst ≫ pullback.fst :=
by { rw ← cancel_mono (𝒰.map x), simp [pullback.condition_assoc, pullback.condition] }

lemma cocycle_snd_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.snd ≫ pullback.fst ≫
  pullback.snd = pullback.snd ≫ pullback.fst ≫ pullback.snd :=
by { simp [pullback.condition_assoc, pullback.condition] }

lemma cocycle_snd_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.snd ≫ pullback.snd =
    pullback.snd ≫ pullback.snd :=
by simp

lemma cocycle (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y = 𝟙 _ :=
begin
  apply pullback.hom_ext; rw category.id_comp,
  apply pullback.hom_ext,
  apply pullback.hom_ext,
  simp_rw category.assoc,
  exact cocycle_fst_fst_fst 𝒰 f g x y z,
  simp_rw category.assoc,
  exact cocycle_fst_fst_snd 𝒰 f g x y z,
  simp_rw category.assoc,
  exact cocycle_fst_snd 𝒰 f g x y z,
  apply pullback.hom_ext,
  apply pullback.hom_ext,
  simp_rw category.assoc,
  exact cocycle_snd_fst_fst 𝒰 f g x y z,
  simp_rw category.assoc,
  exact cocycle_snd_fst_snd 𝒰 f g x y z,
  simp_rw category.assoc,
  exact cocycle_snd_snd 𝒰 f g x y z
end

@[simps]
def gluing : Scheme.glue_data.{u} :=
{ ι := 𝒰.J,
  U := λ x, pullback ((𝒰.map x) ≫ f) g,
  V := λ ⟨x, y⟩, V 𝒰 f g x y, -- p⁻¹(Xᵢ ∩ Xⱼ)
  f := λ x y, pullback.fst,
  f_id := λ x, infer_instance,
  f_open := infer_instance,
  t := λ x y, t 𝒰 f g x y,
  t_id := λ x, t_id 𝒰 f g x,
  t' := λ x y z, t' 𝒰 f g x y z,
  t_fac := λ x y z, begin
    apply pullback.hom_ext,
    apply pullback.hom_ext,
    all_goals { simp }
  end,
  cocycle := λ x y z, cocycle 𝒰 f g x y z }

section end

def p1 : (gluing 𝒰 f g).glued ⟶ X :=
begin
  fapply multicoequalizer.desc,
  exact λ x, pullback.fst ≫ 𝒰.map x,
  rintro ⟨x,y⟩,
  change pullback.fst ≫ _ ≫ 𝒰.map x = (_ ≫ _) ≫ _ ≫ 𝒰.map y,
  rw pullback.condition,
  rw ← category.assoc,
  congr' 1,
  rw category.assoc,
  exact (t_fst_fst _ _ _ _ _).symm
end

def p2 : (gluing 𝒰 f g).glued ⟶ Y :=
begin
  fapply multicoequalizer.desc,
  exact λ x, pullback.snd,
  rintro ⟨x,y⟩,
  change pullback.fst ≫ _ = (_ ≫ _) ≫ _,
  rw category.assoc,
  exact (t_fst_snd _ _ _ _ _).symm
end

section end

lemma p_comm : p1 𝒰 f g ≫ f = p2 𝒰 f g ≫ g :=
begin
  apply multicoequalizer.hom_ext,
  intro x,
  erw [multicoequalizer.π_desc_assoc, multicoequalizer.π_desc_assoc],
  rw [category.assoc, pullback.condition]
end

section end

variable (s : pullback_cone f g)

def pullback_map (x y : 𝒰.J) :
  pullback ((𝒰.pullback_cover s.fst).map x) ((𝒰.pullback_cover s.fst).map y) ⟶
    (gluing 𝒰 f g).V ⟨x, y⟩ :=
begin
  change pullback pullback.fst pullback.fst ⟶ pullback _ _,
  refine (pullback_right_pullback_fst_iso _ _ _).hom ≫ _,
  refine pullback.map _ _ _ _ _ (𝟙 _) (𝟙 _) _ _,
  { exact (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition },
  { simpa using pullback.condition },
  { simp }
end

section end

@[reassoc]
lemma pullback_map_fst (x y : 𝒰.J) :
  pullback_map 𝒰 f g s x y ≫ pullback.fst = pullback.fst ≫
    (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition :=
by { delta pullback_map, simp }

@[reassoc]
lemma pullback_map_snd (x y : 𝒰.J) :
  pullback_map 𝒰 f g s x y ≫ pullback.snd = pullback.snd ≫ pullback.snd  :=
by { delta pullback_map, simp }


def glued_lift : s.X ⟶ (gluing 𝒰 f g).glued :=
begin
  fapply (𝒰.pullback_cover s.fst).glue_morphism,
  { exact λ x, (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition ≫
      (gluing 𝒰 f g).imm x },
  intros x y,
  rw ← pullback_map_fst_assoc,
  have : _ = pullback.fst ≫ _ :=
    (gluing 𝒰 f g).glue_condition x y,
  rw ← this,
  rw [gluing_to_glue_data_t, gluing_to_glue_data_f],
  simp_rw ← category.assoc,
  congr' 1,
  apply pullback.hom_ext; simp_rw category.assoc,
  { rw t_fst_fst,
    rw pullback_map_snd,
    congr' 1,
    rw [← iso.inv_comp_eq, pullback_symmetry_inv_comp_snd],
    erw pullback.lift_fst,
    rw category.comp_id },
  { rw t_fst_snd,
    rw pullback_map_fst_assoc,
    erw [pullback.lift_snd, pullback.lift_snd],
    rw [pullback_symmetry_hom_comp_snd_assoc, pullback_symmetry_hom_comp_snd_assoc],
    exact pullback.condition_assoc _ }
end

section end

lemma glued_lift_p1 : glued_lift 𝒰 f g s ≫ p1 𝒰 f g = s.fst :=
begin
  rw ← cancel_epi (𝒰.pullback_cover s.fst).from_glued,
  apply multicoequalizer.hom_ext,
  intro b,
  erw multicoequalizer.π_desc_assoc,
  erw multicoequalizer.π_desc_assoc,
  delta glued_lift,
  simp_rw ← category.assoc,
  rw (𝒰.pullback_cover s.fst).imm_glue_morphism,
  simp_rw category.assoc,
  erw [multicoequalizer.π_desc, pullback.lift_fst_assoc, pullback.condition, category.comp_id],
  rw pullback_symmetry_hom_comp_fst_assoc,
end

lemma glued_lift_p2 : glued_lift 𝒰 f g s ≫ p2 𝒰 f g = s.snd :=
begin
  rw ← cancel_epi (𝒰.pullback_cover s.fst).from_glued,
  apply multicoequalizer.hom_ext,
  intro b,
  erw multicoequalizer.π_desc_assoc,
  erw multicoequalizer.π_desc_assoc,
  delta glued_lift,
  simp_rw ← category.assoc,
  rw (𝒰.pullback_cover s.fst).imm_glue_morphism,
  simp_rw category.assoc,
  erw [multicoequalizer.π_desc, pullback.lift_snd],
  rw pullback_symmetry_hom_comp_snd_assoc,
  refl
end

section end

namespace open_cover
lemma hom_ext (f₁ f₂ : X ⟶ Y) (h : ∀ x, 𝒰.map x ≫ f₁ = 𝒰.map x ≫ f₂) : f₁ = f₂ :=
begin
  rw ← cancel_epi 𝒰.from_glued,
  apply multicoequalizer.hom_ext,
  intro x,
  erw multicoequalizer.π_desc_assoc,
  erw multicoequalizer.π_desc_assoc,
  exact h x,
end

end open_cover

def pullback_p1_imm_imm (x y : 𝒰.J) :
  pullback (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map x) ⟶ _) ((gluing 𝒰 f g).imm y) ⟶
    V 𝒰 f g y x :=
(pullback_symmetry _ _ ≪≫
  (pullback_right_pullback_fst_iso (p1 𝒰 f g) (𝒰.map x) _)).hom ≫
    (pullback.congr_hom (multicoequalizer.π_desc _ _ _ _ _) rfl).hom

@[simp, reassoc] lemma pullback_p1_imm_imm_fst (x y : 𝒰.J) :
  pullback_p1_imm_imm 𝒰 f g x y ≫ pullback.fst = pullback.snd :=
by { delta pullback_p1_imm_imm, simp }

@[simp, reassoc] lemma pullback_p1_imm_imm_snd (x y : 𝒰.J) :
  pullback_p1_imm_imm 𝒰 f g x y ≫ pullback.snd = pullback.fst ≫ pullback.snd :=
by { delta pullback_p1_imm_imm, simp }

lemma lift_p1_imm_imm_eq (x : 𝒰.J) : pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g)
  (by rw [← pullback.condition_assoc, category.assoc, p_comm]) ≫
  (gluing 𝒰 f g).imm x = (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map x) ⟶ _) :=
begin
  apply ((gluing 𝒰 f g).open_cover.pullback_cover pullback.fst).hom_ext,
  intro y,
  dsimp only [open_cover.pullback_cover],
  transitivity pullback_p1_imm_imm 𝒰 f g x y ≫ fV 𝒰 f g y x ≫ (gluing 𝒰 f g).imm _,
  { rw ← (show _ = fV 𝒰 f g y x ≫ _, from (gluing 𝒰 f g).glue_condition y x),
    simp_rw ← category.assoc,
    congr' 1,
    rw [gluing_to_glue_data_f, gluing_to_glue_data_t],
    apply pullback.hom_ext; simp_rw category.assoc,
    { rw [t_fst_fst, pullback.lift_fst, pullback_p1_imm_imm_snd] },
    { rw [t_fst_snd, pullback.lift_snd, pullback_p1_imm_imm_fst_assoc,
        pullback.condition_assoc], erw multicoequalizer.π_desc } },
  { rw [pullback.condition, ← category.assoc],
    congr' 1,
    apply pullback.hom_ext,
    { simp },
    { simp } }
end

section end

def pullback_p1_iso (x : 𝒰.J) :
  pullback (p1 𝒰 f g) (𝒰.map x) ≅ pullback (𝒰.map x ≫ f) g :=
begin
  fsplit,
  exact pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g)
    (by rw [← pullback.condition_assoc, category.assoc, p_comm]),
  refine pullback.lift ((gluing 𝒰 f g).imm x) pullback.fst
    (by erw multicoequalizer.π_desc),
  { apply pullback.hom_ext,
    { simpa using lift_p1_imm_imm_eq 𝒰 f g x },
    { simp } },
  { apply pullback.hom_ext,
    { simp },
    { simp, erw multicoequalizer.π_desc } },
end

section end

@[simp, reassoc] lemma pullback_p1_iso_hom_fst (x : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g x).hom ≫ pullback.fst = pullback.snd :=
by { delta pullback_p1_iso, simp }

@[simp, reassoc] lemma pullback_p1_iso_hom_snd (x : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g x).hom ≫ pullback.snd = pullback.fst ≫ p2 𝒰 f g :=
by { delta pullback_p1_iso, simp, }

@[simp, reassoc] lemma pullback_p1_iso_inv_fst (x : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g x).inv ≫ pullback.fst = (gluing 𝒰 f g).imm x :=
by { delta pullback_p1_iso, simp }

@[simp, reassoc] lemma pullback_p1_iso_inv_snd (x : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g x).inv ≫ pullback.snd = pullback.fst :=
by { delta pullback_p1_iso, simp }

@[simp, reassoc]
lemma pullback_p1_iso_hom_imm (x : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g x).hom ≫ (gluing 𝒰 f g).imm x = pullback.fst :=
by rw [← pullback_p1_iso_inv_fst, iso.hom_inv_id_assoc]

lemma glued_is_limit : is_limit (pullback_cone.mk _ _ (p_comm 𝒰 f g)) :=
begin
  apply pullback_cone.is_limit_aux',
  intro s,
  use glued_lift 𝒰 f g s,
  use glued_lift_p1 𝒰 f g s,
  use glued_lift_p2 𝒰 f g s,
  intros m h₁ h₂,
  change m ≫ p1 𝒰 f g = _ at h₁,
  change m ≫ p2 𝒰 f g = _ at h₂,
  apply (𝒰.pullback_cover s.fst).hom_ext,
  intro x,
  rw open_cover.pullback_cover_map,
  have := pullback_right_pullback_fst_iso (p1 𝒰 f g) (𝒰.map x) m
    ≪≫ pullback.congr_hom h₁ rfl,
  erw (𝒰.pullback_cover s.fst).imm_glue_morphism,
  rw ← cancel_epi (pullback_right_pullback_fst_iso (p1 𝒰 f g) (𝒰.map x) m
    ≪≫ pullback.congr_hom h₁ rfl).hom,
  rw [iso.trans_hom, category.assoc, pullback.congr_hom_hom, pullback.lift_fst_assoc,
    category.comp_id, pullback_right_pullback_fst_iso_hom_fst_assoc, pullback.condition],
  transitivity pullback.snd ≫ (pullback_p1_iso 𝒰 f g _).hom ≫ (gluing 𝒰 f g).imm _,
  { congr' 1, rw ← pullback_p1_iso_hom_imm },
  simp_rw ← category.assoc,
  congr' 1,
  apply pullback.hom_ext,
  { simp only [category.comp_id, pullback_right_pullback_fst_iso_hom_snd, category.assoc,
      pullback_p1_iso_hom_fst, pullback.lift_snd, pullback.lift_fst,
      pullback_symmetry_hom_comp_fst] },
  { simp only [category.comp_id, pullback_right_pullback_fst_iso_hom_fst_assoc,
    pullback_p1_iso_hom_snd, category.assoc, pullback.lift_fst_assoc,
    pullback_symmetry_hom_comp_snd_assoc, pullback.lift_snd],
    rw [← pullback.condition_assoc, h₂] }
end

section end

lemma has_pullback_of_cover : has_pullback f g := ⟨⟨⟨_, glued_is_limit 𝒰 f g⟩⟩⟩

instance Spec.preserves_limits : preserves_limits Spec := sorry
instance Spec.full : full Spec := sorry
instance Spec.faithful : faithful Spec.to_LocallyRingedSpace := sorry
instance : has_colimits CommRing := infer_instance
instance : has_limits CommRingᵒᵖ := has_limits_op_of_has_colimits

instance affine_has_pullback {A B C : CommRing}
  (f : Spec.obj (opposite.op A) ⟶ Spec.obj (opposite.op C))
  (g : Spec.obj (opposite.op B) ⟶ Spec.obj (opposite.op C)) : has_pullback f g :=
begin
  rw [← Spec.image_preimage f, ← Spec.image_preimage g],
  exact ⟨⟨⟨_,is_limit_of_has_pullback_of_preserves_limit
    Spec (Spec.preimage f) (Spec.preimage g)⟩⟩⟩
end

lemma affine_affine_has_pullback {B C : CommRing} {X : Scheme}
  (f : X ⟶ Spec.obj (opposite.op C))
  (g : Spec.obj (opposite.op B) ⟶ Spec.obj (opposite.op C)) : has_pullback f g :=
has_pullback_of_cover X.affine_cover f g

instance base_affine_has_pullback {C : CommRing} {X Y : Scheme}
  (f : X ⟶ Spec.obj (opposite.op C))
  (g : Y ⟶ Spec.obj (opposite.op C)) : has_pullback f g :=
@@has_pullback_symmetry _ _ _
  (@@has_pullback_of_cover Y.affine_cover g f
    (λ x, @@has_pullback_symmetry _ _ _ $ affine_affine_has_pullback _ _))

instance left_affine_comp_pullback_has_pullback {X Y Z : Scheme}
  (f : X ⟶ Z) (g : Y ⟶ Z) (x : Z.affine_cover.J) :
    has_pullback ((Z.affine_cover.pullback_cover f).map x ≫ f) g :=
begin
  let Xᵢ := pullback f (Z.affine_cover.map x),
  let Yᵢ := pullback g (Z.affine_cover.map x),
  let W := pullback (pullback.snd : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _),
  have := big_square_is_pullback (pullback.fst : W ⟶ _) (pullback.fst : Yᵢ ⟶ _)
    (pullback.snd : Xᵢ ⟶ _) (Z.affine_cover.map x) pullback.snd pullback.snd g
    pullback.condition.symm pullback.condition.symm
      (pullback_cone.flip_is_limit $ pullback_is_pullback _ _)
      (pullback_cone.flip_is_limit $ pullback_is_pullback _ _),
  have : has_pullback (pullback.snd ≫ Z.affine_cover.map x : Xᵢ ⟶ _) g :=
    ⟨⟨⟨_,this⟩⟩⟩,
  rw ← pullback.condition at this,
  exact this,
end

instance {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) : has_pullback f g :=
has_pullback_of_cover (Z.affine_cover.pullback_cover f) f g

end algebraic_geometry.Scheme
