import algebraic_geometry.Scheme
import category_theory.limits.functor_category
import algebraic_geometry.open_immersion
import algebraic_geometry.presheafed_space.gluing
import category_theory.limits.yoneda
import category_theory.limits.opposites

universes v u

open category_theory category_theory.limits algebraic_geometry
namespace algebraic_geometry.Scheme

variables {C : Type u} [category.{v} C]

-- section

-- variables {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

-- variables [mono g]

-- def pullback_cone_of_left_factors : pullback_cone g (f ≫ g) :=
-- pullback_cone.mk f (𝟙 _) $ by simp

-- @[simp] lemma pullback_cone_of_left_factors_X :
--   (pullback_cone_of_left_factors f g).X = X := rfl

-- @[simp] lemma pullback_cone_of_left_factors_fst :
--   (pullback_cone_of_left_factors f g).fst = f := rfl

-- @[simp] lemma pullback_cone_of_left_factors_snd :
--   (pullback_cone_of_left_factors f g).snd = 𝟙 _ := rfl

-- @[simp] lemma pullback_cone_of_left_factors_π_app_none :
--   (pullback_cone_of_left_factors f g).π.app none = f ≫ g := rfl

-- @[simp] lemma pullback_cone_of_left_factors_π_app_left :
--   (pullback_cone_of_left_factors f g).π.app walking_cospan.left = f := rfl

-- @[simp] lemma pullback_cone_of_left_factors_π_app_right :
--   (pullback_cone_of_left_factors f g).π.app walking_cospan.right = 𝟙 _ := rfl

-- /-- Verify that the constructed cocone is indeed a colimit. -/
-- def pullback_cone_of_left_factors_is_limit :
--   is_limit (pullback_cone_of_left_factors f g) :=
-- pullback_cone.is_limit_aux' _ (λ s, ⟨s.snd, by simpa [← cancel_mono g] using s.condition.symm⟩)

-- instance has_pullback_of_left_factors : has_pullback g (f ≫ g) :=
-- ⟨⟨⟨_, pullback_cone_of_left_factors_is_limit f g⟩⟩⟩

-- instance pullback_fst_iso_of_left_factors : is_iso (pullback.snd : pullback g (f ≫ g) ⟶ _) :=
-- begin
--   have : _ ≫ 𝟙 _ = pullback.snd := limit.iso_limit_cone_hom_π
--     ⟨_, pullback_cone_of_left_factors_is_limit f g⟩ walking_cospan.right,
--   rw ← this,
--   apply_instance
-- end

-- def pullback_cone_of_right_factors : pullback_cone (f ≫ g) g :=
-- pullback_cone.mk (𝟙 _) f $ by simp

-- @[simp] lemma pullback_cone_of_right_factors_X :
--   (pullback_cone_of_right_factors f g).X = X := rfl

-- @[simp] lemma pullback_cone_of_right_factors_fst :
--   (pullback_cone_of_right_factors f g).fst = 𝟙 _ := rfl

-- @[simp] lemma pullback_cone_of_right_factors_snd :
--   (pullback_cone_of_right_factors f g).snd = f := rfl

-- @[simp] lemma pullback_cone_of_right_factors_π_app_none :
--   (pullback_cone_of_right_factors f g).π.app none = f ≫ g := category.id_comp _

-- @[simp] lemma pullback_cone_of_right_factors_π_app_left :
--   (pullback_cone_of_right_factors f g).π.app walking_cospan.left = 𝟙 _ := rfl

-- @[simp] lemma pullback_cone_of_right_factors_π_app_right :
--   (pullback_cone_of_right_factors f g).π.app walking_cospan.right = f := rfl

-- /-- Verify that the constructed cocone is indeed a colimit. -/
-- def pullback_cone_of_right_factors_is_limit :
--   is_limit (pullback_cone_of_right_factors f g) :=
-- pullback_cone.is_limit_aux' _ (λ s, ⟨s.fst, by simpa [← cancel_mono g] using s.condition⟩)

-- instance has_pullback_of_right_factors : has_pullback (f ≫ g) g :=
-- ⟨⟨⟨_, pullback_cone_of_right_factors_is_limit f g⟩⟩⟩

-- instance pullback_fst_iso_of_right_factors : is_iso (pullback.fst : pullback (f ≫ g) g ⟶ _) :=
-- begin
--   have : _ ≫ 𝟙 _ = pullback.fst := limit.iso_limit_cone_hom_π
--     ⟨_, pullback_cone_of_right_factors_is_limit f g⟩ walking_cospan.left,
--   rw ← this,
--   apply_instance
-- end

-- section

-- variables {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ X₂) (g₁ : X₂ ⟶ X₃) (f₂ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)
-- variables (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (i₃ : X₃ ⟶ Y₃)
-- variables (h₁ : i₁ ≫ f₂ = f₁ ≫ i₂) (h₂ : i₂ ≫ g₂ = g₁ ≫ i₃)

-- def comp_square_is_limit_of_is_limit (H : is_limit (pullback_cone.mk _ _ h₂))
--   (H' : is_limit (pullback_cone.mk _ _ h₁)) :
--   is_limit (pullback_cone.mk _ _ (show i₁ ≫ f₂ ≫ g₂ = (f₁ ≫ g₁) ≫ i₃,
--       by rw [← category.assoc, h₁, category.assoc, h₂, category.assoc])) :=
-- begin
--   fapply pullback_cone.is_limit_aux',
--   intro s,
--   have : (s.fst ≫ f₂) ≫ g₂ = s.snd ≫ i₃ := by rw [← s.condition, category.assoc],
--   rcases pullback_cone.is_limit.lift' H (s.fst ≫ f₂) s.snd this with ⟨l₁, hl₁, hl₁'⟩,
--   rcases pullback_cone.is_limit.lift' H' s.fst l₁ hl₁.symm with ⟨l₂, hl₂, hl₂'⟩,
--   use l₂,
--   use hl₂,
--   use show l₂ ≫ f₁ ≫ g₁ = s.snd, by { rw [← hl₁', ← hl₂', category.assoc], refl },
--   intros m hm₁ hm₂,
--   apply pullback_cone.is_limit.hom_ext H',
--   { erw [hm₁, hl₂] },
--   { apply pullback_cone.is_limit.hom_ext H,
--     { erw [category.assoc, ← h₁, ← category.assoc, hm₁, ← hl₂,
--       category.assoc, category.assoc, h₁], refl },
--     { erw [category.assoc, hm₂, ← hl₁', ← hl₂'] } }
-- end

-- def is_limit_of_comp_square_is_limit (H : is_limit (pullback_cone.mk _ _ h₂))
--   (H' : is_limit (pullback_cone.mk _ _ (show i₁ ≫ f₂ ≫ g₂ = (f₁ ≫ g₁) ≫ i₃,
--       by rw [← category.assoc, h₁, category.assoc, h₂, category.assoc]))) :
--   is_limit (pullback_cone.mk _ _ h₁) :=
-- begin
--   fapply pullback_cone.is_limit_aux',
--   intro s,
--   have : s.fst ≫ f₂ ≫ g₂ = (s.snd ≫ g₁) ≫ i₃ :=
--   by { rw [← category.assoc, s.condition, category.assoc, category.assoc, h₂] },
--   rcases pullback_cone.is_limit.lift' H' s.fst (s.snd ≫ g₁) this with ⟨l₁, hl₁, hl₁'⟩,
--   dsimp at *,
--   use l₁,
--   use hl₁,
--   split,
--   { apply pullback_cone.is_limit.hom_ext H,
--     { erw [category.assoc, ← h₁, ← category.assoc, hl₁, s.condition], refl },
--     { erw [category.assoc, hl₁'], refl } },
--   intros m hm₁ hm₂,
--   apply pullback_cone.is_limit.hom_ext H',
--   { erw [hm₁, hl₁] },
--   { erw [hl₁', ← hm₂], exact (category.assoc _ _ _).symm }
-- end

-- def comp_square_is_limit_iff_is_limit (H : is_limit (pullback_cone.mk _ _ h₂)) :
--   is_limit (pullback_cone.mk _ _ (show i₁ ≫ f₂ ≫ g₂ = (f₁ ≫ g₁) ≫ i₃,
--     by rw [← category.assoc, h₁, category.assoc, h₂, category.assoc])) ≃
--   is_limit (pullback_cone.mk _ _ h₁) :=
-- { to_fun := is_limit_of_comp_square_is_limit _ _ _ _ _ _ _ h₁ h₂ H,
--   inv_fun := comp_square_is_limit_of_is_limit _ _ _ _ _ _ _ h₁ h₂ H,
--   left_inv := by tidy,
--   right_inv := by tidy }

-- end
-- end
-- section
-- variables {X Y Z X' : C} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ X)
--   [has_pullback f g]
--   [has_pullback f' (pullback.fst : pullback f g ⟶ _)] [has_pullback (f' ≫ f) g]

-- noncomputable
-- def pullback_left_pullback_fst_iso :
--   pullback f' (pullback.fst : pullback f g ⟶ _) ≅ pullback (f' ≫ f) g :=
-- begin
--   let := comp_square_is_limit_of_is_limit
--     (pullback.snd : pullback f' (pullback.fst : pullback f g ⟶ _) ⟶ _) pullback.snd
--     f' f pullback.fst pullback.fst g pullback.condition pullback.condition
--     (pullback_is_pullback _ _) (pullback_is_pullback _ _),
--   exact (this.cone_point_unique_up_to_iso (pullback_is_pullback _ _) : _)
-- end

-- @[simp, reassoc]
-- lemma pullback_left_pullback_fst_iso_hom_fst :
--   (pullback_left_pullback_fst_iso f g f').hom ≫ pullback.fst = pullback.fst :=
-- is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.left

-- @[simp, reassoc]
-- lemma pullback_left_pullback_fst_iso_hom_snd :
--   (pullback_left_pullback_fst_iso f g f').hom ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
-- is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right

-- @[simp, reassoc]
-- lemma pullback_left_pullback_fst_iso_inv_fst :
--   (pullback_left_pullback_fst_iso f g f').inv ≫ pullback.fst = pullback.fst :=
-- is_limit.cone_point_unique_up_to_iso_inv_comp _ _ walking_cospan.left

-- @[simp, reassoc]
-- lemma pullback_left_pullback_fst_iso_inv_snd_snd :
--   (pullback_left_pullback_fst_iso f g f').inv ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
-- is_limit.cone_point_unique_up_to_iso_inv_comp _ _ walking_cospan.right

-- @[simp, reassoc]
-- lemma pullback_left_pullback_fst_iso_inv_snd_fst :
--   (pullback_left_pullback_fst_iso f g f').inv ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ f' :=
-- begin
--   rw ← pullback.condition,
--   exact pullback_left_pullback_fst_iso_inv_fst_assoc _ _ _ _
-- end

-- section pullback_assoc

-- noncomputable theory
-- /-

-- X₁



-- -/

-- variables {X₁ X₂ X₃ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₁) (f₃ : X₂ ⟶ Y₂)
-- variables (f₄ : X₃ ⟶ Y₂) [has_pullback f₁ f₂] [has_pullback f₃ f₄]

-- include f₁ f₂ f₃ f₄

-- local notation `Z₁` := pullback f₁ f₂
-- local notation `Z₂` := pullback f₃ f₄
-- local notation `g₁` := (pullback.fst : Z₁ ⟶ X₁)
-- local notation `g₂` := (pullback.snd : Z₁ ⟶ X₂)
-- local notation `g₃` := (pullback.fst : Z₂ ⟶ X₂)
-- local notation `g₄` := (pullback.snd : Z₂ ⟶ X₃)
-- local notation `W`  := pullback (g₂ ≫ f₃) f₄
-- local notation `W'` := pullback f₁ (g₃ ≫ f₂)
-- local notation `l₁` := (pullback.fst : W ⟶ Z₁)
-- local notation `l₂` := (pullback.lift (pullback.fst ≫ g₂) pullback.snd
--     ((category.assoc _ _ _).trans pullback.condition) : W ⟶ Z₂)
-- local notation `l₁'`:= (pullback.lift pullback.fst (pullback.snd ≫ g₃)
--     (pullback.condition.trans (category.assoc _ _ _).symm) : W' ⟶ Z₁)
-- local notation `l₂'`:= (pullback.snd : W' ⟶ Z₂)

-- /-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
-- def pullback_pullback_left_is_pullback [has_pullback (g₂ ≫ f₃) f₄] :
-- is_limit (pullback_cone.mk l₁ l₂ (show l₁ ≫ g₂ = l₂ ≫ g₃, from (pullback.lift_fst _ _ _).symm)) :=
-- begin
--   apply is_limit_of_comp_square_is_limit,
--   exact pullback_is_pullback f₃ f₄,
--   convert pullback_is_pullback (g₂ ≫ f₃) f₄,
--   rw pullback.lift_snd
-- end

-- /-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
-- def pullback_assoc_is_pullback [has_pullback (g₂ ≫ f₃) f₄] :
-- is_limit (pullback_cone.mk (l₁ ≫ g₁) l₂ (show (l₁ ≫ g₁) ≫ f₁ = l₂ ≫ (g₃ ≫ f₂),
--   by rw [pullback.lift_fst_assoc, category.assoc, category.assoc, pullback.condition])) :=
-- begin
--   apply pullback_cone.flip_is_limit,
--   apply comp_square_is_limit_of_is_limit,
--   apply pullback_cone.flip_is_limit,
--   exact pullback_is_pullback f₁ f₂,
--   apply pullback_cone.flip_is_limit,
--   apply pullback_pullback_left_is_pullback,
--   exact pullback.lift_fst _ _ _,
--   exact pullback.condition.symm
-- end

-- lemma has_pullback_assoc [has_pullback (g₂ ≫ f₃) f₄] :
-- has_pullback f₁ (g₃ ≫ f₂) :=
-- ⟨⟨⟨_, pullback_assoc_is_pullback f₁ f₂ f₃ f₄⟩⟩⟩

-- /-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
-- def pullback_pullback_right_is_pullback [has_pullback f₁ (g₃ ≫ f₂)] :
-- is_limit (pullback_cone.mk l₁' l₂' (show l₁' ≫ g₂ = l₂' ≫ g₃, from pullback.lift_snd _ _ _)) :=
-- begin
--   apply pullback_cone.flip_is_limit,
--   apply is_limit_of_comp_square_is_limit,
--   apply pullback_cone.flip_is_limit,
--   exact pullback_is_pullback f₁ f₂,
--   apply pullback_cone.flip_is_limit,
--   convert pullback_is_pullback f₁ (g₃ ≫ f₂),
--   rw pullback.lift_fst,
--   exact pullback.condition.symm
-- end

-- /-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[Y₂] X₃`. -/
-- def pullback_assoc_symm_is_pullback [has_pullback f₁ (g₃ ≫ f₂)] :
-- is_limit (pullback_cone.mk l₁' (l₂' ≫ g₄) (show l₁' ≫ (g₂ ≫ f₃) = (l₂' ≫ g₄) ≫ f₄,
--   by rw [pullback.lift_snd_assoc, category.assoc, category.assoc, pullback.condition])) :=
-- begin
--   apply comp_square_is_limit_of_is_limit,
--   exact pullback_is_pullback f₃ f₄,
--   apply pullback_pullback_right_is_pullback
-- end

-- lemma has_pullback_assoc_symm [has_pullback f₁ (g₃ ≫ f₂)] :
-- has_pullback (g₂ ≫ f₃) f₄ :=
-- ⟨⟨⟨_, pullback_assoc_symm_is_pullback f₁ f₂ f₃ f₄⟩⟩⟩

-- variables [has_pullback (g₂ ≫ f₃) f₄] [has_pullback f₁ (g₃ ≫ f₂)]

-- noncomputable
-- def pullback_assoc :
--   pullback (pullback.snd ≫ f₃ : pullback f₁ f₂ ⟶ _) f₄ ≅
--     pullback f₁ (pullback.fst ≫ f₂ : pullback f₃ f₄ ⟶ _) :=
-- (pullback_pullback_left_is_pullback f₁ f₂ f₃ f₄).cone_point_unique_up_to_iso
-- (pullback_pullback_right_is_pullback f₁ f₂ f₃ f₄)

-- @[simp, reassoc]
-- lemma pullback_assoc_inv_fst_fst :
--   (pullback_assoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.fst = pullback.fst :=
-- begin
--   transitivity l₁' ≫ pullback.fst,
--   rw ← category.assoc,
--   congr' 1,
--   exact is_limit.cone_point_unique_up_to_iso_inv_comp _ _ walking_cospan.left,
--   exact pullback.lift_fst _ _ _,
-- end

-- @[simp, reassoc]
-- lemma pullback_assoc_hom_fst :
--   (pullback_assoc f₁ f₂ f₃ f₄).hom ≫ pullback.fst = pullback.fst ≫ pullback.fst :=
-- by rw [← iso.eq_inv_comp, pullback_assoc_inv_fst_fst]

-- @[simp, reassoc]
-- lemma pullback_assoc_hom_snd_fst :
--   (pullback_assoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
-- begin
--   transitivity l₂ ≫ pullback.fst,
--   rw ← category.assoc,
--   congr' 1,
--   exact is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right,
--   exact pullback.lift_fst _ _ _,
-- end

-- @[simp, reassoc]
-- lemma pullback_assoc_hom_snd_snd :
--   (pullback_assoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
-- begin
--   transitivity l₂ ≫ pullback.snd,
--   rw ← category.assoc,
--   congr' 1,
--   exact is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right,
--   exact pullback.lift_snd _ _ _,
-- end

-- @[simp, reassoc]
-- lemma pullback_assoc_inv_fst_snd :
--   (pullback_assoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.fst :=
-- by rw [iso.inv_comp_eq, pullback_assoc_hom_snd_fst]

-- @[simp, reassoc]
-- lemma pullback_assoc_inv_snd :
--   (pullback_assoc f₁ f₂ f₃ f₄).inv ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
-- by rw [iso.inv_comp_eq, pullback_assoc_hom_snd_snd]

-- end pullback_assoc

-- instance pullback.map_is_iso {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [has_pullback f₁ f₂]
--   (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [has_pullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
--   (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) [is_iso i₁] [is_iso i₂] [is_iso i₃] :
--   is_iso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
-- begin
--   constructor,
--   fconstructor,
--   refine pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) _ _,
--   { rw [is_iso.comp_inv_eq, category.assoc, eq₁, is_iso.inv_hom_id_assoc] },
--   { rw [is_iso.comp_inv_eq, category.assoc, eq₂, is_iso.inv_hom_id_assoc] },
--   tidy
-- end

-- @[simps hom]
-- def pullback.congr_hom {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
--   (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) [has_pullback f₁ g₁] [has_pullback f₂ g₂] :
--     pullback f₁ g₁ ≅ pullback f₂ g₂ :=
-- as_iso $ pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

-- @[simp]
-- lemma pullback.congr_hom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
--   (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) [has_pullback f₁ g₁] [has_pullback f₂ g₂] :
--   (pullback.congr_hom h₁ h₂).inv =
--     pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) :=
-- begin
--   apply pullback.hom_ext,
--   { erw pullback.lift_fst,
--     rw iso.inv_comp_eq,
--     erw pullback.lift_fst_assoc,
--     rw [category.comp_id, category.comp_id] },
--   { erw pullback.lift_snd,
--     rw iso.inv_comp_eq,
--     erw pullback.lift_snd_assoc,
--     rw [category.comp_id, category.comp_id] },
-- end



-- instance lem : has_pullbacks (Scheme.{u}ᵒᵖ ⥤ Type u) := sorry
-- instance coyoneda_functor_preserves_limits :

-- class open_subfunctor {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) :=
-- (subfunctor : mono f)
-- (res : ∀ {S : Scheme.{u}} (g : yoneda.obj S ⟶ G), functor.representable (pullback f g))
-- (res_open : ∀ {S : Scheme.{u}} (g : yoneda.obj S ⟶ G),
--   is_open_immersion (yoneda.preimage (functor.repr_f (pullback f g) ≫ pullback.snd)).val)

-- attribute[instance] open_subfunctor.subfunctor open_subfunctor.res open_subfunctor.res_open

-- noncomputable
-- def res_repr_X {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) [open_subfunctor f]
--   {S : Scheme.{u}} (g : yoneda.obj S ⟶ G) : Scheme := functor.repr_X (pullback f g)

-- noncomputable
-- def res_repr_f {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) [open_subfunctor f]
--   {S : Scheme.{u}} (g : yoneda.obj S ⟶ G) : res_repr_X f g ⟶ S :=
-- yoneda.preimage (functor.repr_f (pullback f g) ≫ pullback.snd)

-- instance res_repr_f_is_open_immersion {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) [open_subfunctor f]
--   {S : Scheme.{u}} (g : yoneda.obj S ⟶ G) : is_open_immersion (res_repr_f f g) :=
-- open_subfunctor.res_open g

-- @[simp]
-- lemma yoneda_map_res_repr_f {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) [open_subfunctor f]
--   {S : Scheme.{u}} (g : yoneda.obj S ⟶ G) : yoneda.map (res_repr_f f g) =
--     (pullback f g).repr_f ≫ pullback.snd := functor.image_preimage _ _


-- structure open_subfunctor_cover (F : Scheme.{u}ᵒᵖ ⥤ Type u) :=
-- (ι : Type u)
-- (F' : ι → Scheme.{u}ᵒᵖ ⥤ Type u)
-- (f : Π (i : ι), F' i ⟶ F)
-- (f_open_subfunctor : ∀ i, open_subfunctor (f i))
-- (covers : ∀ (T : Scheme.{u}) (g : yoneda.obj T ⟶ F) (x : T.carrier),
--   ∃ (i : ι), (x ∈ set.range (res_repr_f (f i) g).1.base))

-- attribute[instance] open_subfunctor_cover.f_open_subfunctor


-- variables {F : Scheme.{u}ᵒᵖ ⥤ Type u}
--   (D : open_subfunctor_cover F) [H : ∀ i : D.ι, functor.representable (D.F' i)]

-- include H

-- noncomputable
-- def open_subfunctor_cover.functor_t (i j : D.ι) : pullback (D.f j) ((D.F' i).repr_f ≫ D.f i) ⟶
--   pullback (D.f i) ((D.F' j).repr_f ≫ D.f j) :=
-- pullback.map _ _ _ _ (𝟙 _) (D.F' i).repr_f (𝟙 _) (by simp) (by simp) ≫
--   (pullback_symmetry _ _).hom ≫
--   inv (pullback.map _ _ _ _ (𝟙 _) (D.F' j).repr_f (𝟙 _) (by simp) (by simp))

-- -- set_option pp.universes true

-- noncomputable
-- lemma open_subfunctor_cover.glue_data : Scheme.glue_data.{u} :=
-- { ι := D.ι,
--   U := λ i, functor.repr_X (D.F' i),
--   V := λ ⟨i, j⟩, res_repr_X (D.f j) ((D.F' i).repr_f ≫ D.f i),
--   f := λ i j, res_repr_f _ _,
--   -- f_id := λ i, by { apply is_iso_of_reflects_iso _ yoneda,
--   --   rw yoneda_map_res_repr_f, apply_instance },
--   f_open := λ i, by {   },
--   t := λ i j, yoneda.preimage (functor.repr_f _ ≫ D.functor_t i j ≫ inv (functor.repr_f _)),
--   -- t_id := λ i, by simp [open_subfunctor_cover.functor_t],
--   t' := λ i j k, yoneda.preimage (by {
--     have : yoneda.obj (pullback (res_repr_f (D.f j) ((D.F' i).repr_f ≫ D.f i)) (res_repr_f (D.f k) ((D.F' i).repr_f ≫ D.f i)))
--     ⟶ pullback (yoneda.map $ res_repr_f (D.f j) ((D.F' i).repr_f ≫ D.f i)) (yoneda)
--     let := @preserves_pullback.iso.{u+1 u+1} (Scheme.{u}ᵒᵖ ⥤ Type u) _,
--     -- have := (preserves_pullback.iso.{u u+1 u+1} yoneda.{u u+1} (res_repr_f.{u} (D.f j) ((D.F' i).repr_f ≫ D.f i))
--     --   (res_repr_f.{u} (D.f k) ((D.F' i).repr_f ≫ D.f i))).hom, })
--   })

-- }

-- section end

-- lemma open_subfunctor_cover.representable (F : Scheme.{u}ᵒᵖ ⥤ Type u)
--   (D : open_subfunctor_cover F) (H : ∀ i : D.ι, functor.representable (D.F' i)) :
--     functor.representable F :=
-- begin




end

structure open_cover (X : Scheme) :=
(obj : Π (x : X.carrier), Scheme)
(map : Π (x : X.carrier), obj x ⟶ X)
(covers : ∀ x, x ∈ set.range (map x).1.base)
(is_open : ∀ x, is_open_immersion (map x) . tactic.apply_instance)

attribute [instance] open_cover.is_open

variables {X Y Z : Scheme.{u}} (𝒰 : open_cover X) (f : X ⟶ Z) (g : Y ⟶ Z)
variables [∀ x, has_pullback (𝒰.map x ≫ f) g]

namespace open_cover

def glued_cover_t' (x y z : X.carrier) :
  pullback (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _)
    (pullback.fst : pullback (𝒰.map x) (𝒰.map z) ⟶ _) ⟶
  pullback (pullback.fst : pullback (𝒰.map y) (𝒰.map z) ⟶ _)
    (pullback.fst : pullback (𝒰.map y) (𝒰.map x) ⟶ _) :=
begin
  refine (pullback_left_pullback_fst_iso _ _ _).hom ≫ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_left_pullback_fst_iso _ _ _).inv,
  refine pullback.map _ _ _ _ (pullback_symmetry _ _).hom (𝟙 _) (𝟙 _) _ _,
  { simp [pullback.condition] },
  { simp }
end

@[simp, reassoc]
lemma glued_cover_t'_fst_fst (x y z : X.carrier) :
  glued_cover_t' 𝒰 x y z ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_fst_snd (x y z : X.carrier) :
  glued_cover_t' 𝒰 x y z ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_snd_fst (x y z : X.carrier) :
  glued_cover_t' 𝒰 x y z ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_snd_snd (x y z : X.carrier) :
  glued_cover_t' 𝒰 x y z ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
by { delta glued_cover_t', simp }

lemma glued_cover_cocycle_fst (x y z : X.carrier) :
  glued_cover_t' 𝒰 x y z ≫ glued_cover_t' 𝒰 y z x ≫ glued_cover_t' 𝒰 z x y ≫ pullback.fst =
    pullback.fst :=
by apply pullback.hom_ext; simp

lemma glued_cover_cocycle_snd (x y z : X.carrier) :
  glued_cover_t' 𝒰 x y z ≫ glued_cover_t' 𝒰 y z x ≫ glued_cover_t' 𝒰 z x y ≫ pullback.snd =
    pullback.snd :=
by apply pullback.hom_ext; simp [pullback.condition]

lemma glued_cover_cocycle (x y z : X.carrier) :
  glued_cover_t' 𝒰 x y z ≫ glued_cover_t' 𝒰 y z x ≫ glued_cover_t' 𝒰 z x y = 𝟙 _ :=
begin
  apply pullback.hom_ext; simp_rw [category.id_comp, category.assoc],
  apply glued_cover_cocycle_fst,
  apply glued_cover_cocycle_snd,
end

@[simps]
def glued_cover : Scheme.glue_data.{u} :=
{ ι := X.carrier,
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


-- `hc` is included so that the instances can be inferred from the type.
@[nolint unused_arguments]
def from_glued : 𝒰.glued ⟶ X :=
begin
  fapply multicoequalizer.desc,
  exact λ x, (𝒰.map x),
  rintro ⟨x, y⟩,
  change pullback.fst ≫ _ = ((pullback_symmetry _ _).hom ≫ pullback.fst) ≫ _,
  simpa using pullback.condition
end

@[simp, reassoc]
lemma imm_from_glued (x : X.carrier) :
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
  use 𝒰.from_glued.val.base '' U ∩ set.range (𝒰.map x).1.base,
  use set.inter_subset_left _ _,
  split,
  { rw ← set.image_preimage_eq_inter_range,
    apply (show is_open_immersion (𝒰.map x), by apply_instance).base_open.is_open_map,
    convert hU x using 1,
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
  use (𝒰.glued_cover.imm x).1.base y,
  rw ← comp_apply,
  rw ← 𝒰.imm_from_glued x at h,
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
  (x : X.carrier) : (𝒰.map x) ≫ 𝒰.glue_morphism f hf = f x :=
begin
  rw [← imm_from_glued, category.assoc],
  erw [is_iso.hom_inv_id_assoc, multicoequalizer.π_desc],
end

@[simps]
def pullback_cover {W : Scheme} (f : W ⟶ X) : open_cover W :=
{ obj := λ x, pullback f (𝒰.map (f.1.base x)),
  map := λ x, pullback.fst,
  covers := λ x, begin
    rw ← (show _ = (pullback.fst : pullback f (𝒰.map (f.1.base x)) ⟶ _).1.base,
      from preserves_pullback.iso_hom_fst (Scheme.forget ⋙
      LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _) f (𝒰.map (f.1.base x))),
    rw [coe_comp, set.range_comp, set.range_iff_surjective.mpr, set.image_univ,
      Top.pullback_fst_range],
    rcases 𝒰.covers (f.1.base x) with ⟨y, h⟩,
    exact ⟨y, h.symm⟩,
    { rw ← Top.epi_iff_surjective, apply_instance }
  end }

end open_cover

def glue_data.open_cover (D : Scheme.glue_data) : open_cover D.glued :=
{ obj := λ x, D.U (D.imm_jointly_surjective x).some,
  map := λ x, D.imm (D.imm_jointly_surjective x).some,
  covers := λ x, ⟨_, (D.imm_jointly_surjective x).some_spec.some_spec⟩ }

/-- (Xᵢ ×[Z] Y) ×[X] Xⱼ -/
def V (x y : X.carrier) : Scheme :=
pullback ((pullback.fst : pullback ((𝒰.map x) ≫ f) g ⟶ _) ≫ (𝒰.map x)) (𝒰.map y)

def t (x y : X.carrier) : V 𝒰 f g x y ⟶ V 𝒰 f g y x :=
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
lemma t_fst_fst (x y : X.carrier) : t 𝒰 f g x y ≫ pullback.fst ≫ pullback.fst = pullback.snd :=
by { delta t, simp }

@[simp, reassoc]
lemma t_fst_snd (x y : X.carrier) :
  t 𝒰 f g x y ≫ pullback.fst ≫ pullback.snd = pullback.fst ≫ pullback.snd :=
by { delta t, simp }

@[simp, reassoc]
lemma t_snd (x y : X.carrier) :
  t 𝒰 f g x y ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
by { delta t, simp }

lemma t_id (x : X.carrier) : t 𝒰 f g x x = 𝟙 _ :=
begin
  apply pullback.hom_ext; rw category.id_comp,
  apply pullback.hom_ext,
  { rw ← cancel_mono (𝒰.map x),
    simp [pullback.condition] },
  { simp },
  { rw ← cancel_mono (𝒰.map x),
    simp [pullback.condition] }
end

abbreviation fV (x y : X.carrier) : V 𝒰 f g x y ⟶ pullback ((𝒰.map x) ≫ f) g := pullback.fst

/-- (Xᵢ ×[Z] Y) ×[X] Xⱼ ×[Xᵢ ×[Z] Y] (Xᵢ ×[Z] Y) ×[X] Xₖ  -/
def t' (x y z : X.carrier) :
  pullback (fV 𝒰 f g x y) (fV 𝒰 f g x z) ⟶ pullback (fV 𝒰 f g y z) (fV 𝒰 f g y x) :=
begin
  refine (pullback_left_pullback_fst_iso _ _ _).hom ≫ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_left_pullback_fst_iso _ _ _).inv,
  refine pullback.map _ _ _ _ (t 𝒰 f g x y) (𝟙 _) (𝟙 _) _ _,
  { simp [← pullback.condition] },
  { simp }
end

section end

@[simp, reassoc]
lemma t'_fst_fst_fst (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ pullback.fst ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_fst_fst_snd (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ pullback.fst ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_fst_snd (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_fst_fst (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ pullback.snd ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_fst_snd (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ pullback.snd ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_snd (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
by { delta t', simp, }

lemma cocycle_fst_fst_fst (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.fst ≫ pullback.fst ≫
  pullback.fst = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
by simp

lemma cocycle_fst_fst_snd (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.fst ≫ pullback.fst ≫
  pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by simp

lemma cocycle_fst_snd (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.snd :=
by simp

lemma cocycle_snd_fst_fst (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.snd ≫ pullback.fst ≫
  pullback.fst = pullback.snd ≫ pullback.fst ≫ pullback.fst :=
by { rw ← cancel_mono (𝒰.map x), simp [pullback.condition_assoc, pullback.condition] }

lemma cocycle_snd_fst_snd (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.snd ≫ pullback.fst ≫
  pullback.snd = pullback.snd ≫ pullback.fst ≫ pullback.snd :=
by { simp [pullback.condition_assoc, pullback.condition] }

lemma cocycle_snd_snd (x y z : X.carrier) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.snd ≫ pullback.snd =
    pullback.snd ≫ pullback.snd :=
by simp

lemma cocycle (x y z : X.carrier) :
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
{ ι := X.carrier,
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

def pullback_map (x y : s.X.carrier) :
  pullback ((𝒰.pullback_cover s.fst).map x) ((𝒰.pullback_cover s.fst).map y) ⟶
    (gluing 𝒰 f g).V ⟨(s.fst.val.base) x, (s.fst.val.base) y⟩ :=
begin
  change pullback pullback.fst pullback.fst ⟶ pullback _ _,
  refine (pullback_left_pullback_fst_iso _ _ _).hom ≫ _,
  refine pullback.map _ _ _ _ _ (𝟙 _) (𝟙 _) _ _,
  { exact (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition },
  { simpa using pullback.condition },
  { simp }
end

section end

@[reassoc]
lemma pullback_map_fst (x y : s.X.carrier) :
  pullback_map 𝒰 f g s x y ≫ pullback.fst = pullback.fst ≫
    (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition :=
by { delta pullback_map, simp }

@[reassoc]
lemma pullback_map_snd (x y : s.X.carrier) :
  pullback_map 𝒰 f g s x y ≫ pullback.snd = pullback.snd ≫ pullback.snd  :=
by { delta pullback_map, simp }


def glued_lift : s.X ⟶ (gluing 𝒰 f g).glued :=
begin
  fapply (𝒰.pullback_cover s.fst).glue_morphism,
  { exact λ x, (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition ≫
      (gluing 𝒰 f g).imm (s.fst.1.base x) },
  intros x y,
  rw ← pullback_map_fst_assoc,
  have : _ = pullback.fst ≫ _ :=
    (gluing 𝒰 f g).glue_condition (s.fst.val.base x) (s.fst.val.base y),
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

-- lemma pullback_p1_eq (x : X.carrier) :
--   (pullback.fst : pullback (𝒰.map x) (p1 𝒰 f g) ⟶ _) ≫ 𝒰.map x ≫ f =
--     (pullback.snd ≫ p2 𝒰 f g) ≫ g := by simpa [←p_comm] using pullback.condition_assoc f

-- include 𝒰 f g

-- def test (x y : X.carrier) : sorry :=
-- begin
--   -- have := pullback (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _)
--   --   (pullback.fst : pullback (𝒰.map x ≫ f) g ⟶ _),
--   -- haveI : has_pullback (pullback.fst ≫ 𝒰.map x ≫ f : pullback (𝒰.map x) (𝒰.map y) ⟶ _) g := sorry,
--   -- have a := pullback_left_pullback_fst_iso (𝒰.map x ≫ f) g (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _),
--   -- have b := pullback_left_pullback_fst_iso (𝒰.map x) (𝒰.map y) (pullback.fst : pullback (𝒰.map x ≫ f) g ⟶ _),
--   -- have := b,
--   have := is_limit_of_comp_square_is_limit ((gluing 𝒰 f g).imm x) (p2 𝒰 f g) (𝒰.map x) f
--     pullback.fst (p1 𝒰 f g),
-- end

def pullback_p1_imm_imm (x y : X.carrier) :
  pullback (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map x) ⟶ _) ((gluing 𝒰 f g).imm y) ⟶
    V 𝒰 f g y x :=
(pullback_symmetry _ _ ≪≫
  (pullback_left_pullback_fst_iso (p1 𝒰 f g) (𝒰.map x) _)).hom ≫
    (pullback.congr_hom (multicoequalizer.π_desc _ _ _ _ _) rfl).hom

@[simp, reassoc] lemma pullback_p1_imm_imm_fst (x y : X.carrier) :
  pullback_p1_imm_imm 𝒰 f g x y ≫ pullback.fst = pullback.snd :=
by { delta pullback_p1_imm_imm, simp }

@[simp, reassoc] lemma pullback_p1_imm_imm_snd (x y : X.carrier) :
  pullback_p1_imm_imm 𝒰 f g x y ≫ pullback.snd = pullback.fst ≫ pullback.snd :=
by { delta pullback_p1_imm_imm, simp }

lemma lift_p1_imm_imm_eq (x : X.carrier) : pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g)
  (by rw [← pullback.condition_assoc, category.assoc, p_comm]) ≫
  (gluing 𝒰 f g).imm x = (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map x) ⟶ _) :=
begin
  apply ((gluing 𝒰 f g).open_cover.pullback_cover pullback.fst).hom_ext,
  intro y,
  dsimp only [open_cover.pullback_cover],
  let y' := (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map x) ⟶ _).val.base y,
  let y'' := ((gluing 𝒰 f g).imm_jointly_surjective y').some,
  transitivity pullback_p1_imm_imm 𝒰 f g x y'' ≫ fV 𝒰 f g y'' x ≫ (gluing 𝒰 f g).imm _,
  { rw ← (show _ = fV 𝒰 f g y'' x ≫ _, from (gluing 𝒰 f g).glue_condition y'' x),
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

def pullback_p1_iso (x : X.carrier) :
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

@[simp, reassoc] lemma pullback_p1_iso_hom_fst (x : X.carrier) :
  (pullback_p1_iso 𝒰 f g x).hom ≫ pullback.fst = pullback.snd :=
by { delta pullback_p1_iso, simp }

@[simp, reassoc] lemma pullback_p1_iso_hom_snd (x : X.carrier) :
  (pullback_p1_iso 𝒰 f g x).hom ≫ pullback.snd = pullback.fst ≫ p2 𝒰 f g :=
by { delta pullback_p1_iso, simp, }

@[simp, reassoc] lemma pullback_p1_iso_inv_fst (x : X.carrier) :
  (pullback_p1_iso 𝒰 f g x).inv ≫ pullback.fst = (gluing 𝒰 f g).imm x :=
by { delta pullback_p1_iso, simp }

@[simp, reassoc] lemma pullback_p1_iso_inv_snd (x : X.carrier) :
  (pullback_p1_iso 𝒰 f g x).inv ≫ pullback.snd = pullback.fst :=
by { delta pullback_p1_iso, simp }

@[simp, reassoc]
lemma pullback_p1_iso_hom_imm (x : X.carrier) :
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
  have := pullback_left_pullback_fst_iso (p1 𝒰 f g) (𝒰.map (s.fst.val.base x)) m
    ≪≫ pullback.congr_hom h₁ rfl,
  erw (𝒰.pullback_cover s.fst).imm_glue_morphism,
  rw ← cancel_epi (pullback_left_pullback_fst_iso (p1 𝒰 f g) (𝒰.map (s.fst.val.base x)) m
    ≪≫ pullback.congr_hom h₁ rfl).hom,
  rw [iso.trans_hom, category.assoc, pullback.congr_hom_hom, pullback.lift_fst_assoc,
    category.comp_id, pullback_left_pullback_fst_iso_hom_fst_assoc, pullback.condition],
  transitivity pullback.snd ≫ (pullback_p1_iso 𝒰 f g _).hom ≫ (gluing 𝒰 f g).imm _,
  { congr' 1, rw ← pullback_p1_iso_hom_imm },
  simp_rw ← category.assoc,
  congr' 1,
  apply pullback.hom_ext,
  { simp only [category.comp_id, pullback_left_pullback_fst_iso_hom_snd, category.assoc,
      pullback_p1_iso_hom_fst, pullback.lift_snd, pullback.lift_fst,
      pullback_symmetry_hom_comp_fst] },
  { simp only [category.comp_id, pullback_left_pullback_fst_iso_hom_fst_assoc,
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

def affine_cover (X : Scheme) : open_cover X :=
{ obj := λ x, Spec.obj $ opposite.op (X.local_affine x).some_spec.some,
  map := λ x, ((X.local_affine x).some_spec.some_spec.some.inv ≫
    X.to_LocallyRingedSpace.of_restrict _ : _),
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
  (f : X ⟶ Z) (g : Y ⟶ Z) (x : X.carrier) :
    has_pullback ((Z.affine_cover.pullback_cover f).map x ≫ f) g :=
begin
  let Xᵢ := pullback f (Z.affine_cover.map (f.1.base x)),
  let Yᵢ := pullback g (Z.affine_cover.map (f.1.base x)),
  let W := pullback (pullback.snd : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _),
  have := comp_square_is_limit_of_is_limit (pullback.fst : W ⟶ _) (pullback.fst : Yᵢ ⟶ _)
    (pullback.snd : Xᵢ ⟶ _) (Z.affine_cover.map (f.1.base x)) pullback.snd pullback.snd g
    pullback.condition.symm pullback.condition.symm
      (pullback_cone.flip_is_limit $ pullback_is_pullback _ _)
      (pullback_cone.flip_is_limit $ pullback_is_pullback _ _),
  have : has_pullback (pullback.snd ≫ Z.affine_cover.map (f.val.base x) : Xᵢ ⟶ _) g :=
    ⟨⟨⟨_,this⟩⟩⟩,
  rw ← pullback.condition at this,
  exact this,
end

instance {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) : has_pullback f g :=
has_pullback_of_cover (Z.affine_cover.pullback_cover f) f g


end algebraic_geometry.Scheme
