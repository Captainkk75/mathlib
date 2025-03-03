/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.AffineScheme
import algebraic_geometry.pullbacks
import category_theory.morphism_property

/-!
# Properties of morphisms between Schemes

We provide the basic framework for talking about properties of morphisms between Schemes.

A `morphism_property Scheme` is a predicate on morphisms between schemes, and an
`affine_target_morphism_property` is a predicate on morphisms into affine schemes. Given a
`P : affine_target_morphism_property`, we may construct a `morphism_property` called
`target_affine_locally P` that holds for `f : X ⟶ Y` whenever `P` holds for the
restriction of `f` on every affine open subset of `Y`.

## Main definitions

- `algebraic_geometry.affine_target_morphism_property.is_local`: We say that `P.is_local` if `P`
satisfies the assumptions of the affine communication lemma
(`algebraic_geometry.of_affine_open_cover`). That is,
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basic_open r` for any
  global section `r`.
3. If `P` holds for `f ∣_ Y.basic_open r` for all `r` in a spanning set of the global sections,
  then `P` holds for `f`.

- `algebraic_geometry.property_is_local_at_target`: We say that `property_is_local_at_target P` for
`P : morphism_property Scheme` if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.

## Main results

- `algebraic_geometry.affine_target_morphism_property.is_local.affine_open_cover_tfae`:
  If `P.is_local`, then `target_affine_locally P f` iff there exists an affine cover `{ Uᵢ }` of `Y`
  such that `P` holds for `f ∣_ Uᵢ`.
- `algebraic_geometry.affine_target_morphism_property.is_local_of_open_cover_imply`:
  If the existance of an affine cover `{ Uᵢ }` of `Y` such that `P` holds for `f ∣_ Uᵢ` implies
  `target_affine_locally P f`, then `P.is_local`.
- `algebraic_geometry.affine_target_morphism_property.is_local.affine_target_iff`:
  If `Y` is affine and `f : X ⟶ Y`, then `target_affine_locally P f ↔ P f` provided `P.is_local`.
- `algebraic_geometry.affine_target_morphism_property.is_local.target_affine_locally_is_local` :
  If `P.is_local`, then `property_is_local_at_target (target_affine_locally P)`.
- `algebraic_geometry.property_is_local_at_target.open_cover_tfae`:
  If `property_is_local_at_target P`, then `P f` iff there exists an open cover `{ Uᵢ }` of `Y`
  such that `P` holds for `f ∣_ Uᵢ`.

These results should not be used directly, and should be ported to each property that is local.

-/

universe u

open topological_space category_theory category_theory.limits opposite

noncomputable theory

namespace algebraic_geometry

/-- An `affine_target_morphism_property` is a class of morphisms from an arbitrary scheme into an
affine scheme. -/
def affine_target_morphism_property := ∀ ⦃X Y : Scheme⦄ (f : X ⟶ Y) [is_affine Y], Prop

/-- `is_iso` as a `morphism_property`. -/
protected def Scheme.is_iso : morphism_property Scheme := @is_iso Scheme _

/-- `is_iso` as an `affine_morphism_property`. -/
protected def Scheme.affine_target_is_iso : affine_target_morphism_property :=
λ X Y f H, is_iso f

instance : inhabited affine_target_morphism_property := ⟨Scheme.affine_target_is_iso⟩

/-- A `affine_target_morphism_property` can be extended to a `morphism_property` such that it
*never* holds when the target is not affine -/
def affine_target_morphism_property.to_property (P : affine_target_morphism_property) :
  morphism_property Scheme :=
λ X Y f, ∃ h, @@P f h

lemma affine_target_morphism_property.to_property_apply (P : affine_target_morphism_property)
  {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] :
  P.to_property f ↔ P f := by { delta affine_target_morphism_property.to_property, simp [*] }

lemma affine_cancel_left_is_iso {P : affine_target_morphism_property}
  (hP : P.to_property.respects_iso) {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) [is_iso f] [is_affine Z] : P (f ≫ g) ↔ P g :=
by rw [← P.to_property_apply, ← P.to_property_apply, hP.cancel_left_is_iso]

lemma affine_cancel_right_is_iso
  {P : affine_target_morphism_property} (hP : P.to_property.respects_iso) {X Y Z : Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso g] [is_affine Z] [is_affine Y] : P (f ≫ g) ↔ P f :=
by rw [← P.to_property_apply, ← P.to_property_apply, hP.cancel_right_is_iso]

/-- For a `P : affine_target_morphism_property`, `target_affine_locally P` holds for
`f : X ⟶ Y` whenever `P` holds for the restriction of `f` on every affine open subset of `Y`. -/
def target_affine_locally (P : affine_target_morphism_property) : morphism_property Scheme :=
  λ {X Y : Scheme} (f : X ⟶ Y), ∀ (U : Y.affine_opens), @@P (f ∣_ U) U.prop

lemma is_affine_open.map_is_iso {X Y : Scheme} {U : opens Y.carrier} (hU : is_affine_open U)
  (f : X ⟶ Y) [is_iso f] : is_affine_open ((opens.map f.1.base).obj U) :=
begin
  haveI : is_affine _ := hU,
  exact is_affine_of_iso (f ∣_ U),
end

lemma target_affine_locally_respects_iso {P : affine_target_morphism_property}
  (hP : P.to_property.respects_iso) : (target_affine_locally P).respects_iso :=
begin
  split,
  { introv H U,
    rw [morphism_restrict_comp, affine_cancel_left_is_iso hP],
    exact H U },
  { introv H,
    rintro ⟨U, hU : is_affine_open U⟩, dsimp,
    haveI : is_affine _ := hU,
    haveI : is_affine _ := hU.map_is_iso e.hom,
    rw [morphism_restrict_comp, affine_cancel_right_is_iso hP],
    exact H ⟨(opens.map e.hom.val.base).obj U, hU.map_is_iso e.hom⟩ }
end

/--
We say that `P : affine_target_morphism_property` is a local property if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basic_open r` for any
  global section `r`.
3. If `P` holds for `f ∣_ Y.basic_open r` for all `r` in a spanning set of the global sections,
  then `P` holds for `f`.
-/
structure affine_target_morphism_property.is_local (P : affine_target_morphism_property) : Prop :=
(respects_iso : P.to_property.respects_iso)
(to_basic_open : ∀ {X Y : Scheme} [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj $ op ⊤),
  by exactI P f →
    @@P (f ∣_ (Y.basic_open r)) ((top_is_affine_open Y).basic_open_is_affine _))
(of_basic_open_cover : ∀ {X Y : Scheme} [is_affine Y] (f : X ⟶ Y)
  (s : finset (Y.presheaf.obj $ op ⊤)) (hs : ideal.span (s : set (Y.presheaf.obj $ op ⊤)) = ⊤),
  by exactI (∀ (r : s), @@P (f ∣_ (Y.basic_open r.1))
    ((top_is_affine_open Y).basic_open_is_affine _)) → P f)

lemma target_affine_locally_of_open_cover {P : affine_target_morphism_property}
  (hP : P.is_local)
  {X Y : Scheme} (f : X ⟶ Y) (𝒰 : Y.open_cover) [∀ i, is_affine (𝒰.obj i)]
  (h𝒰 : ∀ i, P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i)) :
    target_affine_locally P f :=
begin
  classical,
  let S := λ i, (⟨⟨set.range (𝒰.map i).1.base, (𝒰.is_open i).base_open.open_range⟩,
    range_is_affine_open_of_open_immersion (𝒰.map i)⟩ : Y.affine_opens),
  intro U,
  apply of_affine_open_cover U (set.range S),
  { intros U r h,
    haveI : is_affine _ := U.2,
    have := hP.2 (f ∣_ U.1),
    replace this := this (Y.presheaf.map (eq_to_hom U.1.open_embedding_obj_top).op r) h,
    rw ← P.to_property_apply at this ⊢,
    exact (hP.1.arrow_mk_iso_iff (morphism_restrict_restrict_basic_open f _ r)).mp this },
  { intros U s hs H,
    haveI : is_affine _ := U.2,
    apply hP.3 (f ∣_ U.1) (s.image (Y.presheaf.map (eq_to_hom U.1.open_embedding_obj_top).op)),
    { apply_fun ideal.comap (Y.presheaf.map (eq_to_hom U.1.open_embedding_obj_top.symm).op) at hs,
      rw ideal.comap_top at hs,
      rw ← hs,
      simp only [eq_to_hom_op, eq_to_hom_map, finset.coe_image],
      have : ∀ {R S : CommRing} (e : S = R) (s : set S),
        (by exactI ideal.span (eq_to_hom e '' s) = ideal.comap (eq_to_hom e.symm) (ideal.span s)),
      { intros, subst e, simpa },
      apply this },
    { rintro ⟨r, hr⟩,
      obtain ⟨r, hr', rfl⟩ := finset.mem_image.mp hr,
      simp_rw ← P.to_property_apply at ⊢ H,
      exact
        (hP.1.arrow_mk_iso_iff (morphism_restrict_restrict_basic_open f _ r)).mpr (H ⟨r, hr'⟩) } },
  { rw set.eq_univ_iff_forall,
    simp only [set.mem_Union],
    intro x,
    exact ⟨⟨_, ⟨𝒰.f x, rfl⟩⟩, 𝒰.covers x⟩ },
  { rintro ⟨_, i, rfl⟩,
    simp_rw ← P.to_property_apply at ⊢ h𝒰,
    exact (hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _)).mpr (h𝒰 i) },
end

lemma affine_target_morphism_property.is_local.affine_open_cover_tfae
  {P : affine_target_morphism_property}
  (hP : P.is_local) {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [target_affine_locally P f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)], ∀ (i : 𝒰.J),
      by exactI P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
      by exactI P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
      by exactI P (pullback.snd : pullback f g ⟶ U),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤) (hU' : ∀ i, is_affine_open (U i)),
      ∀ i, @@P (f ∣_ (U i)) (hU' i)] :=
begin
  tfae_have : 1 → 4,
  { intros H U g h₁ h₂,
    resetI,
    replace H := H ⟨⟨_, h₂.base_open.open_range⟩,
      range_is_affine_open_of_open_immersion g⟩,
    rw ← P.to_property_apply at H ⊢,
    rwa ← hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _) },
  tfae_have : 4 → 3,
  { intros H 𝒰 h𝒰 i,
    resetI,
    apply H },
  tfae_have : 3 → 2,
  { exact λ H, ⟨Y.affine_cover, infer_instance, H Y.affine_cover⟩ },
  tfae_have : 2 → 1,
  { rintro ⟨𝒰, h𝒰, H⟩, exactI target_affine_locally_of_open_cover hP f 𝒰 H },
  tfae_have : 5 → 2,
  { rintro ⟨ι, U, hU, hU', H⟩,
    refine ⟨Y.open_cover_of_supr_eq_top U hU, hU', _⟩,
    intro i,
    specialize H i,
    rw [← P.to_property_apply, ← hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _)],
    rw ← P.to_property_apply at H,
    convert H,
    all_goals { ext1, exact subtype.range_coe } },
  tfae_have : 1 → 5,
  { intro H,
    refine ⟨Y.carrier, λ x, is_open_immersion.opens_range (Y.affine_cover.map x), _,
      λ i, range_is_affine_open_of_open_immersion _, _⟩,
    { rw eq_top_iff, intros x _, erw opens.mem_supr, exact⟨x, Y.affine_cover.covers x⟩ },
    { intro i, exact H ⟨_, range_is_affine_open_of_open_immersion _⟩ } },
  tfae_finish
end

lemma affine_target_morphism_property.is_local_of_open_cover_imply
  (P : affine_target_morphism_property) (hP : P.to_property.respects_iso)
  (H : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)], ∀ (i : 𝒰.J),
      by exactI P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i)) →
    (∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
      by exactI P (pullback.snd : pullback f g ⟶ U))) : P.is_local :=
begin
  refine ⟨hP, _, _⟩,
  { introv h,
    resetI,
    haveI : is_affine _ := (top_is_affine_open Y).basic_open_is_affine r,
    delta morphism_restrict,
    rw affine_cancel_left_is_iso hP,
    refine @@H f ⟨Scheme.open_cover_of_is_iso (𝟙 Y), _, _⟩ (Y.of_restrict _) _inst _,
    { intro i, dsimp, apply_instance },
    { intro i, dsimp,
      rwa [← category.comp_id pullback.snd, ← pullback.condition, affine_cancel_left_is_iso hP] } },
  { introv hs hs',
    resetI,
    replace hs := ((top_is_affine_open Y).basic_open_union_eq_self_iff _).mpr hs,
    have := H f ⟨Y.open_cover_of_supr_eq_top _ hs, _, _⟩ (𝟙 _),
    rwa [← category.comp_id pullback.snd, ← pullback.condition,
      affine_cancel_left_is_iso hP] at this,
    { intro i, exact (top_is_affine_open Y).basic_open_is_affine _ },
    { rintro (i : s),
      specialize hs' i,
      haveI : is_affine _ := (top_is_affine_open Y).basic_open_is_affine i.1,
      delta morphism_restrict at hs',
      rwa affine_cancel_left_is_iso hP at hs' } }
end

lemma affine_target_morphism_property.is_local.affine_open_cover_iff
  {P : affine_target_morphism_property} (hP : P.is_local)
  {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.open_cover.{u} Y) [h𝒰 : ∀ i, is_affine (𝒰.obj i)] :
  target_affine_locally P f ↔ ∀ i, @@P (pullback.snd : pullback f (𝒰.map i) ⟶ _) (h𝒰 i) :=
⟨λ H, let h := ((hP.affine_open_cover_tfae f).out 0 2).mp H in h 𝒰,
  λ H, let h := ((hP.affine_open_cover_tfae f).out 1 0).mp in h ⟨𝒰, infer_instance, H⟩⟩

lemma affine_target_morphism_property.is_local.affine_target_iff
  {P : affine_target_morphism_property} (hP : P.is_local)
  {X Y : Scheme.{u}} (f : X ⟶ Y) [is_affine Y] :
  target_affine_locally P f ↔ P f :=
begin
  rw hP.affine_open_cover_iff f _,
  swap, { exact Scheme.open_cover_of_is_iso (𝟙 Y) },
  swap, { intro _, dsimp, apply_instance },
  transitivity (P (pullback.snd : pullback f (𝟙 _) ⟶ _)),
  { exact ⟨λ H, H punit.star, λ H _, H⟩ },
  rw [← category.comp_id pullback.snd, ← pullback.condition, affine_cancel_left_is_iso hP.1],
end

/--
We say that `P : morphism_property Scheme` is local at the target if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.
-/
structure property_is_local_at_target (P : morphism_property Scheme) : Prop :=
(respects_iso : P.respects_iso)
(restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier), P f → P (f ∣_ U))
(of_open_cover : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.open_cover.{u} Y),
    (∀ (i : 𝒰.J), P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i)) → P f)

lemma affine_target_morphism_property.is_local.target_affine_locally_is_local
  {P : affine_target_morphism_property} (hP : P.is_local) :
    property_is_local_at_target (target_affine_locally P) :=
begin
  constructor,
  { exact target_affine_locally_respects_iso hP.1 },
  { intros X Y f U H V,
    rw [← P.to_property_apply, hP.1.arrow_mk_iso_iff (morphism_restrict_restrict f _ _)],
    convert H ⟨_, is_affine_open.image_is_open_immersion V.2 (Y.of_restrict _)⟩,
    rw ← P.to_property_apply,
    refl },
  { rintros X Y f 𝒰 h𝒰,
    rw (hP.affine_open_cover_tfae f).out 0 1,
    refine ⟨𝒰.bind (λ _, Scheme.affine_cover _), _, _⟩,
    { intro i, dsimp [Scheme.open_cover.bind], apply_instance },
    { intro i,
      specialize h𝒰 i.1,
      rw (hP.affine_open_cover_tfae (pullback.snd : pullback f (𝒰.map i.fst) ⟶ _)).out 0 2
        at h𝒰,
      specialize h𝒰 (Scheme.affine_cover _) i.2,
      let e : pullback f ((𝒰.obj i.fst).affine_cover.map i.snd ≫ 𝒰.map i.fst) ⟶
        pullback (pullback.snd : pullback f (𝒰.map i.fst) ⟶ _)
          ((𝒰.obj i.fst).affine_cover.map i.snd),
      { refine (pullback_symmetry _ _).hom ≫ _,
        refine (pullback_right_pullback_fst_iso _ _ _).inv ≫ _,
        refine (pullback_symmetry _ _).hom ≫ _,
        refine pullback.map _ _ _ _ (pullback_symmetry _ _).hom (𝟙 _) (𝟙 _) _ _;
          simp only [category.comp_id, category.id_comp, pullback_symmetry_hom_comp_snd] },
      rw ← affine_cancel_left_is_iso hP.1 e at h𝒰,
      convert h𝒰,
      simp } },
end

lemma property_is_local_at_target.open_cover_tfae
  {P : morphism_property Scheme}
  (hP : property_is_local_at_target P)
  {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [P f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), P (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      P (pullback.snd : pullback f g ⟶ U),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤), (∀ i, P (f ∣_ (U i)))] :=
begin
  tfae_have : 2 → 1,
  { rintro ⟨𝒰, H⟩, exact hP.3 f 𝒰 H },
  tfae_have : 1 → 4,
  { intros H U, exact hP.2 f U H },
  tfae_have : 4 → 3,
  { intros H 𝒰 i,
    rw ← hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _),
    exact H (is_open_immersion.opens_range $ 𝒰.map i) },
  tfae_have : 3 → 2,
  { exact λ H, ⟨Y.affine_cover, H Y.affine_cover⟩ },
  tfae_have : 4 → 5,
  { intros H U g hg,
    resetI,
    rw ← hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _),
    apply H },
  tfae_have : 5 → 4,
  { intros H U,
    erw hP.1.cancel_left_is_iso,
    apply H },
  tfae_have : 4 → 6,
  { intro H, exact ⟨punit, λ _, ⊤, csupr_const, λ _, H _⟩ },
  tfae_have : 6 → 2,
  { rintro ⟨ι, U, hU, H⟩,
    refine ⟨Y.open_cover_of_supr_eq_top U hU, _⟩,
    intro i,
    rw ← hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _),
    convert H i,
    all_goals { ext1, exact subtype.range_coe } },
  tfae_finish
end

lemma affine_target_morphism_property.is_local.open_cover_iff
  {P : morphism_property Scheme} (hP : property_is_local_at_target P)
  {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.open_cover.{u} Y) :
  P f ↔ ∀ i, P (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
⟨λ H, let h := ((hP.open_cover_tfae f).out 0 2).mp H in h 𝒰,
  λ H, let h := ((hP.open_cover_tfae f).out 1 0).mp in h ⟨𝒰, H⟩⟩

end algebraic_geometry
