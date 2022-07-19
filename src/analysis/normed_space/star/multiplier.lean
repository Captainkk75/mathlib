import analysis.normed_space.star.basic
import analysis.normed_space.operator_norm
import data.real.sqrt
import analysis.special_functions.pow

/-!
# Multiplier Algebra of a C⋆-algebra

Define the multiplier algebra of a C⋆-algebra as the algebra (over `𝕜`) of double centralizers,
for which we provide the localized notation `𝓜(𝕜, A)`.  A double centralizer is a pair of
continuous linear maps `L R : A →L[𝕜] A` satisfying the intertwining condition `R x * y = x * L y`.

There is a natural embedding `A → 𝓜(𝕜, A)` which sends `a : A` to the continuous linear maps
`L R : A →L[𝕜] A` given by left and right multiplication by `a`, and we provide this map as a
coercion.

The multiplier algebra corresponds to a non-commutative Stone–Čech compactification in the sense
that when the algebra `A` is commutative, it can be identified with `C₀(X, ℂ)` for some locally
compact Hausdorff space `X`, and in that case `𝓜(𝕜, A)` can be identified with `C(βX, ℂ)`.

## Implementation notes

## TODO

+ show that `𝓜(𝕜, A)` is a C⋆-ring
+ show that `𝓜(𝕜, A)` is complete in the norm topology
+ define a type synonym for `𝓜(𝕜, A)` which is equipped with the strict topology
+ after ⋆-algebra morphisms are implemented in mathlib, bundle the coercion `A → 𝓜(𝕜, A)`
+ show that the image of `A` in `𝓜(𝕜, A)` is an essential ideal
+ prove the universal property of `𝓜(𝕜, A)`

-/

noncomputable theory

open_locale nnreal ennreal
open nnreal

universes u v

variables (𝕜 : Type u) (A : Type v)
  [nondiscrete_normed_field 𝕜]
  [non_unital_normed_ring A]
  [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A]

section prereqs

namespace continuous_linear_map

-- `lmul` exists, but doesn't work for us because we have *non-unital* ring, so we need this
-- very similar version. There's a PR open to fix this: #15310
noncomputable def lmul' (𝕜 : Type u) (A : Type v) [nondiscrete_normed_field 𝕜]
  [non_unital_normed_ring A] [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A] :
  A →L[𝕜] A →L[𝕜] A :=
linear_map.mk_continuous₂
  ({ to_fun := λ a,
     { to_fun := λ b, a * b,
       map_add' := λ x y, mul_add _ _ _,
       map_smul' := λ k x, mul_smul_comm _ _ _ },
     map_add' := λ x y, by { ext, exact add_mul _ _ _ },
     map_smul' := λ k x, by { ext, exact smul_mul_assoc _ _ _ } })
  (1 : ℝ)
  (by simpa only [linear_map.coe_mk, one_mul] using norm_mul_le)

@[simp]
lemma lmul'_apply (x y : A) : lmul' 𝕜 A x y = x * y := rfl

@[simp] lemma op_norm_lmul'_apply_le (x : A) : ∥lmul' 𝕜 A x∥ ≤ ∥x∥ :=
op_norm_le_bound _ (norm_nonneg x) (norm_mul_le x)

lemma lmul_eq_lmul' (𝕜 : Type u) (A : Type v) [nondiscrete_normed_field 𝕜] [normed_ring A]
  [normed_algebra 𝕜 A] : lmul 𝕜 A = lmul' 𝕜 A := by {ext, refl}

noncomputable def lmul_right' (𝕜 : Type u) (A : Type v) [nondiscrete_normed_field 𝕜]
  [non_unital_normed_ring A] [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A] :
  A →L[𝕜] A →L[𝕜] A :=
(lmul' 𝕜 A).flip

@[simp]
lemma lmul_right'_apply (x y : A) : lmul_right' 𝕜 A x y = y * x := rfl

@[simp] lemma op_norm_lmul_right'_apply_le (x : A) : ∥lmul_right' 𝕜 A x∥ ≤ ∥x∥ :=
op_norm_le_bound _ (norm_nonneg x) (λ y, (norm_mul_le y x).trans_eq (mul_comm _ _))

lemma lmul_right_eq_lmul' (𝕜 : Type u) (A : Type v) [nondiscrete_normed_field 𝕜] [normed_ring A]
  [normed_algebra 𝕜 A] : lmul_right 𝕜 A = lmul_right' 𝕜 A := by {ext, refl}

end continuous_linear_map

end prereqs

@[ext]
structure double_centralizer : Type v :=
(left : A →L[𝕜] A)
(right : A →L[𝕜] A)
(central : ∀ x y : A, right x * y = x * left y)

localized "notation `𝓜(` 𝕜 `, ` A `)` := double_centralizer 𝕜 A" in multiplier_algebra

/-!
### Normed space structure

Because the multiplier algebra is defined as the algebra of double centralizers, there is a natural
map `double_centralizer.prod_mk := λ a, (a.left, a.right) : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)`.
We use this map to pull back the normed space structure from `(A →L[𝕜] A) × (A →L[𝕜] A)` to
`𝓜(𝕜, A)`, which provides a definitional isometric embedding. Consequently, completeness of
`𝓜(𝕜, A)` is obtained by proving that the range of this map is closed.
-/

namespace double_centralizer

def prod_mk : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A) := λ a, (a.left, a.right) -- (a.left, a.right)

@[simp] lemma prod_mk_def (a : 𝓜(𝕜, A)) : prod_mk 𝕜 A a = (a.left, a.right) := rfl

variables {𝕜 A}

lemma injective_prod_mk : function.injective (prod_mk 𝕜 A) :=
λ a b h, ext a b (prod.ext_iff.mp h).1 (prod.ext_iff.mp h).2

lemma range_prod_mk : set.range (prod_mk 𝕜 A) = {lr | ∀ x y, lr.2 x * y = x * lr.1 y} :=
set.ext $ λ x, ⟨by {rintro ⟨a, rfl⟩, exact a.central}, λ hx, ⟨⟨x.1, x.2, hx⟩, by simp⟩⟩

instance : has_add 𝓜(𝕜, A) :=
{ add := λ a b,
  { left := a.left + b.left,
    right := a.right + b.right,
    central :=
            begin
            intros x y,
            simp only [continuous_linear_map.add_apply],
            rw add_mul,
            rw mul_add,
            repeat {rw central _ _},
            end } }

instance : has_zero 𝓜(𝕜, A) :=
{ zero :=
  { left := 0,
    right := 0,
    central := λ x y, by simp only [continuous_linear_map.zero_apply, zero_mul, mul_zero] } }

instance : has_neg 𝓜(𝕜, A) :=
{ neg := λ a,
  { left := -(a.left),
    right := -(a.right),
    central :=
              begin
              intros x y,
              simp only [continuous_linear_map.neg_apply, neg_mul, mul_neg, neg_inj],
              apply central,
              end } }

instance : has_sub 𝓜(𝕜, A) :=
{ sub := λ a b,
  { left := a.left - b.left,
    right := a.right - b.right,
  central :=
            begin
            intros x y,
            simp only [continuous_linear_map.coe_sub', pi.sub_apply],
            rw sub_mul,
            rw mul_sub,
            simp only [central],
            end } }

instance : has_smul 𝕜 𝓜(𝕜, A) :=
{ smul := λ k a,
  { left := k • a.left,
    right := k • a.right,
    central :=
              begin
              intros x y,
              simp only [continuous_linear_map.coe_smul', pi.smul_apply],
              repeat {rw central _ _},
              rw mul_smul_comm _ _ _,
              rw smul_mul_assoc,
              rw central _ _,
              exact _inst_4,
              end } }

-- this is easier than defining the instances of `has_smul` for `ℕ` and `ℤ`.
instance : add_comm_group 𝓜(𝕜, A) :=
{ add := (+),
  add_assoc := λ a b c, by {ext; exact add_assoc _ _ _},
  zero := 0,
  zero_add := λ a, by {ext; exact zero_add _},
  add_zero := λ a, by {ext; exact add_zero _},
  neg := λ x, -x,
  sub := λ x y,  x - y,
  sub_eq_add_neg := λ a b, by {ext; exact sub_eq_add_neg _ _},
  add_left_neg := λ a, by {ext; exact add_left_neg _},
  add_comm := λ a b, by {ext; exact add_comm _ _}, }

def add_group_hom_prod_mk : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A) :=
{ to_fun := prod_mk 𝕜 A,
  map_zero' := rfl,
  map_add' := λ x y, rfl }

instance : module 𝕜 𝓜(𝕜, A) :=
function.injective.module 𝕜 add_group_hom_prod_mk injective_prod_mk (λ x y, rfl)

instance : normed_group 𝓜(𝕜, A) := normed_group.induced add_group_hom_prod_mk injective_prod_mk

instance : normed_space 𝕜 𝓜(𝕜, A) :=
{ norm_smul_le := λ k a, show max (∥k • a.left∥) (∥k • a.right∥) ≤ ∥k∥ * max (∥a.left∥) (∥a.right∥),
    by simp only [mul_max_of_nonneg _ _ (norm_nonneg k), norm_smul],
  .. double_centralizer.module }

lemma uniform_embedding_prod_mk : uniform_embedding (prod_mk 𝕜 A) :=
uniform_embedding_comap injective_prod_mk

-- does this really not exist in `mathlib`?
def clm_apply (x : A) : (A →L[𝕜] A) →L[𝕜] A :=
linear_map.mk_continuous ⟨λ f, f x, λ f g, rfl, λ k f, rfl⟩ (∥x∥)
  (λ f, mul_comm (∥f∥) (∥x∥) ▸ f.le_op_norm x)

instance [complete_space A] : complete_space 𝓜(𝕜, A) :=
begin
  rw complete_space_iff_is_complete_range uniform_embedding_prod_mk.to_uniform_inducing,
  apply is_closed.is_complete,
  simp only [range_prod_mk, set.set_of_forall],
  refine is_closed_Inter (λ x, is_closed_Inter $ λ y, is_closed_eq _ _),
  { exact ((continuous_mul_right y).comp (clm_apply x).continuous).comp continuous_snd },
  { exact ((continuous_mul_left x).comp (clm_apply y).continuous).comp continuous_fst }
end

/-- For `a : 𝓜(𝕜, A)`, the norms of `a.left` and `a.right` coincide. Consequently,
`double_centralizer.prod_mk : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)` is injective (see
`double_centralizer.prod_mk_injective`). The `normed_space` structure on `𝓜(𝕜, A)` is
defined as the pullback of the normed space structure along this map.  -/
lemma norm_left_eq_right (a : 𝓜(𝕜, A)) : ∥a.left∥ = ∥a.right∥ :=
begin
  -- a handy lemma for this proof
  have h0 : ∀ f : A →L[𝕜] A, ∀ C : ℝ≥0, (∀ b : A, ∥f b∥₊ ^ 2 ≤ C * ∥f b∥₊ * ∥b∥₊) → ∥f∥₊ ≤ C,
  { intros f C h,
    have h1 : ∀ b, C * ∥f b∥₊ * ∥b∥₊ ≤ C * ∥f∥₊ * ∥b∥₊ ^ 2,
    { intros b,
      convert mul_le_mul_right' (mul_le_mul_left' (f.le_op_nnnorm b) C) (∥b∥₊) using 1,
      ring, },
    have := div_le_of_le_mul (f.op_nnnorm_le_bound _ (by simpa only [sqrt_sq, sqrt_mul]
      using (λ b, sqrt_le_sqrt_iff.mpr ((h b).trans (h1 b))))),
    convert rpow_le_rpow this (by exact_mod_cast zero_le (2 : ℕ) : 0 ≤ (2 : ℝ)),
    { simp only [rpow_two, div_pow, sq_sqrt], simp only [sq, mul_self_div_self] },
    { simp only [rpow_two, sq_sqrt] } },
  have h1 : ∀ b, ∥ a.left b ∥₊ ^ 2 ≤  ∥ a.right ∥₊ * ∥ a.left b ∥₊ * ∥ b ∥₊,
  { intros b,
    calc ∥ a.left b ∥₊ ^ 2
        = ∥ star (a.left b) * (a.left b) ∥₊
        : by simpa only [←sq] using (cstar_ring.nnnorm_star_mul_self).symm
    ... ≤ ∥ a.right (star (a.left b))∥₊ * ∥ b ∥₊ : a.central (star (a.left b)) b ▸ nnnorm_mul_le _ _
    ... ≤ ∥ a.right ∥₊ * ∥ a.left b ∥₊ * ∥ b ∥₊
        : nnnorm_star (a.left b) ▸ mul_le_mul_right' (a.right.le_op_nnnorm _) _},
  have h2 : ∀ b, ∥ a.right b ∥₊ ^ 2 ≤  ∥ a.left ∥₊ * ∥ a.right b ∥₊ * ∥ b ∥₊,
  { intros b,
    calc ∥ a.right b ∥₊ ^ 2
        = ∥ a.right b * star (a.right b) ∥₊
        : by simpa only [←sq] using (cstar_ring.nnnorm_self_mul_star).symm
    ... ≤ ∥ b ∥₊ * ∥ a.left (star (a.right b))∥₊
        : (a.central b (star (a.right b))).symm ▸ nnnorm_mul_le _ _
    ... = ∥ a.left (star (a.right b))∥₊ * ∥b∥₊ : mul_comm _ _
    ... ≤ ∥ a.left ∥₊ * ∥ a.right b ∥₊ * ∥ b ∥₊
        : nnnorm_star (a.right b) ▸ mul_le_mul_right' (a.left.le_op_nnnorm _) _  },
  exact le_antisymm (h0 _ _ h1) (h0 _ _ h2),
end

#exit

-- this requires approximate units, which we don't yet have, and it's a bit of a mess.
def of_central_funs (L : A → A) (R : A → A) (h : ∀ x y : A, R x * y = x * L y) : 𝓜(𝕜, A) :=
{ left :=
  { to_fun := L,
    map_add' := sorry,
    map_smul' := sorry,
    cont := sorry },
  right :=
  { to_fun := R,
    map_add' := sorry,
    map_smul' := sorry,
    cont := sorry },
  central := h }


noncomputable instance : has_coe A 𝓜(𝕜, A) :=
{ coe := λ a,
  { left := continuous_linear_map.lmul' 𝕜 A a,
    right := continuous_linear_map.lmul_right' 𝕜 A a,
    central := λ x y, mul_assoc _ _ _ } }

@[simp, norm_cast]
lemma coe_left (a : A) : (a : 𝓜(𝕜, A)).left = continuous_linear_map.lmul' 𝕜 A a := rfl
@[simp, norm_cast]
lemma coe_right (a : A) : (a : 𝓜(𝕜, A)).right = continuous_linear_map.lmul_right' 𝕜 A a := rfl

instance : has_add 𝓜(𝕜, A) :=
{ add := λ a b,
  { left := a.left + b.left,
    right := a.right + b.right,
    central := λ x y, by simp only [continuous_linear_map.add_apply, add_mul, mul_add, central]}}

-- all these simp lemmas should be prefixed with `coe_`, then the non-`coe_` ones should just be
-- linear maps, not their coercions to functions.
@[simp]
lemma add_left (a b : 𝓜(𝕜, A)) : ⇑(a + b).left = a.left + b.left := rfl
@[simp]
lemma add_right (a b : 𝓜(𝕜, A)) : ⇑(a + b).right = a.right + b.right := rfl

instance : has_mul 𝓜(𝕜, A) :=
{ mul := λ a b,
  { left := a.left.comp b.left,
    right := b.right.comp a.right,
    central := λ x y, by simp only [continuous_linear_map.coe_comp', function.comp_app, central]}}

@[simp]
lemma mul_left (a b : 𝓜(𝕜, A)) : ⇑(a * b).left = a.left ∘ b.left := rfl
@[simp]
lemma mul_right (a b : 𝓜(𝕜, A)) : ⇑(a * b).right = b.right ∘ a.right := rfl

@[simp]
lemma mul_left_apply (a b : 𝓜(𝕜, A)) (c : A) : (a * b).left c = a.left (b.left c) := rfl
@[simp]
lemma mul_right_apply (a b : 𝓜(𝕜, A)) (c : A) : (a * b).right c = b.right (a.right c) := rfl

instance : has_smul 𝕜 𝓜(𝕜, A) :=
{ smul := λ k a,
  { left := k • a.left,
    right := k • a.right,
    central := λ x y , by simp only [continuous_linear_map.coe_smul', pi.smul_apply, central,
               mul_smul_comm, smul_mul_assoc]}}

@[simp]
lemma smul_left (k : 𝕜) (a : 𝓜(𝕜, A)) : ⇑(k • a).left = k • a.left := rfl
@[simp]
lemma smul_right (k : 𝕜) (a : 𝓜(𝕜, A)) : ⇑(k • a).right = k • a.right := rfl

@[simp]
lemma zero_left : (0 : 𝓜(𝕜, A)).left = 0 := rfl
@[simp]
lemma zero_right : (0 : 𝓜(𝕜, A)).right = 0 := rfl

instance : has_one 𝓜(𝕜, A) :=
{ one :=
  { left := 1,
    right := 1,
    central := λ x y, rfl } }

@[simp]
lemma one_left : (1 : 𝓜(𝕜, A)).left = 1 := rfl
@[simp]
lemma one_right : (1 : 𝓜(𝕜, A)).right = 1 := rfl

variables [star_ring 𝕜] [star_ring A] [star_module 𝕜 A] [normed_star_group A]

instance : has_star 𝓜(𝕜, A) :=
{ star := λ a,
  { left := (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.right).comp
      ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A),
    right := (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.left).comp
      ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A),
    central := λ x y, by simpa only [star_mul, star_star] using (congr_arg star (a.central (star y)
                         (star x))).symm}}

@[simp]
lemma star_left (a : 𝓜(𝕜, A)) (b : A) : (star a).left b = star (a.right (star b)) := rfl
@[simp]
lemma star_right (a : 𝓜(𝕜, A)) (b : A) : (star a).right b = star (a.left (star b)) := rfl

instance : has_neg 𝓜(𝕜, A) :=
{ neg := λ a,
  { left := -(a.left),
    right := -(a.right),
    central := λ x y, by simp only [continuous_linear_map.neg_apply, neg_mul,
                      mul_neg, neg_inj, central]}}

@[simp]
lemma neg_left (a : 𝓜(𝕜, A)) : ⇑(-a).left = -a.left := rfl
@[simp]
lemma neg_right (a : 𝓜(𝕜, A)) : ⇑(-a).right = -a.right := rfl

instance : has_sub 𝓜(𝕜, A) :=
{ sub := λ a b,
  { left := a.left - b.left,
    right := a.right - b.right,
  central := λ x y, by simp only [continuous_linear_map.coe_sub', pi.sub_apply, sub_mul,
                       mul_sub, central]}}

@[simp]
lemma sub_left (a b : 𝓜(𝕜, A)) : ⇑(a - b).left = a.left - b.left := rfl
@[simp]
lemma sub_right (a b : 𝓜(𝕜, A)) : ⇑(a - b).right = a.right - b.right := rfl

instance : star_add_monoid 𝓜(𝕜, A) :=
{ star_involutive := λ x, by {ext; simp},
  star_add := λ x y, by {ext; simp},
  .. double_centralizer.has_star }

instance : ring 𝓜(𝕜, A) :=
{ one := 1,
  mul := λ x y, x * y,
  mul_assoc := λ a b c, by {ext; simp only [mul_left, mul_right], },
  one_mul := λ a, by {ext; simp only [mul_left_apply, one_left, mul_right_apply, one_right, continuous_linear_map.one_apply]},
  mul_one := λ a, by {ext; simp only [mul_left_apply, one_left, mul_right_apply, one_right, continuous_linear_map.one_apply]},
  left_distrib := λ a b c,
  begin
    ext,
    { rw [mul_left, add_left, add_left],
      simp only [function.comp_app, pi.add_apply, map_add, mul_left] },
    { rw [mul_right, add_right, add_right],
      simp only [function.comp_app, pi.add_apply, mul_right] }
  end,
  right_distrib := λ a b c,
  begin
    ext,
    { rw [mul_left, add_left, add_left],
      simp only [function.comp_app, pi.add_apply, map_add, mul_left] },
    { change (c.right * (a.right + b.right)) x = ((c.right * a.right) + (c.right * b.right)) x,
      rw mul_add, }
  end,
  .. double_centralizer.add_comm_group }

instance : star_ring 𝓜(𝕜, A) :=
{ star_mul := λ a b, by {ext; simp only [star_left, star_right, mul_right, mul_left,
    function.comp_apply, star_star]},
  .. double_centralizer.star_add_monoid }

instance : module 𝕜 𝓜(𝕜, A) :=
{ smul := λ k a, k • a,
  one_smul := λ a, by {ext; simp only [smul_left, smul_right, one_smul],},
  mul_smul := λ k₁ k₂ a, by {ext; exact mul_smul _ _ _},
  smul_add := λ k a b, by {ext; exact smul_add _ _ _},
  smul_zero := λ k, by {ext; exact smul_zero _},
  add_smul := λ k₁ k₂ a, by {ext; exact add_smul _ _ _},
  zero_smul := λ a, by {ext; simp only [smul_left, one_smul, smul_right, smul_add, smul_zero,
    pi.smul_apply, zero_smul, zero_left, zero_right, continuous_linear_map.zero_apply,
    eq_self_iff_true, pi.zero_apply]} }

instance : star_module 𝕜 𝓜(𝕜, A) :=
{ star_smul := λ k a, by {ext; exact star_smul _ _},
  .. double_centralizer.star_add_monoid }

-- this might already require `A` to be a `cstar_ring`, for otherwise I don't think we'll be able
-- to prove `norm_right` below.
noncomputable instance : has_norm 𝓜(𝕜, A) :=
{ norm := λ a, ∥a.left∥ }

open_locale nnreal
open nnreal
variables [cstar_ring A]

-- this should go in `analysis.normed_space.star_basic`
lemma _root_.cstar_ring.nnnorm_self_mul_star {E : Type*} [non_unital_normed_ring E] [star_ring E]
  [cstar_ring E] {x : E} : ∥x * star x∥₊ = ∥x∥₊ * ∥x∥₊ :=
by simpa using @cstar_ring.nnnorm_star_mul_self _ _ _ _ (star x)


lemma norm_left (a : 𝓜(𝕜, A)) : ∥a∥ = ∥a.left∥ := rfl


lemma norm_right (a : 𝓜(𝕜, A)) : ∥a∥ = ∥a.right∥ := by rw [norm_left, norm_left_eq_right]

noncomputable instance : metric_space 𝓜(𝕜, A) :=
{ dist := λ a b, ∥a - b∥,
  dist_self := λ x, by { simpa only [sub_self, norm_left] using norm_zero },
  dist_comm := λ x y, dist_comm x.left y.left,
  dist_triangle := λ x y z, dist_triangle x.left y.left z.left,
  eq_of_dist_eq_zero := λ x y h₁,
  begin
    change ∥(x - y).left∥ = 0 at h₁,
    have h₂ := h₁,
    rw [←norm_left, norm_right] at h₂,
    ext1,
    exact (@eq_of_dist_eq_zero _ _ x.left y.left h₁),
    exact (@eq_of_dist_eq_zero _ _ x.right y.right h₂),
  end }

noncomputable instance : normed_group 𝓜(𝕜, A) :=
{ dist_eq := λ x y, rfl,
  .. double_centralizer.add_comm_group,
  .. double_centralizer.has_norm,
  .. double_centralizer.metric_space }




noncomputable instance : normed_ring 𝓜(𝕜, A) :=
{ norm_mul := λ a b, norm_mul_le a.left b.left,
  .. double_centralizer.ring,
  .. double_centralizer.normed_group }

open_locale ennreal

/- I think we don't have the necessary type class to make this lemma true.
`nondiscrete_normed_field 𝕜` is too weak, but `is_R_or_C 𝕜` is far too strong. What we
want is a type class for `𝕜` where we can say `λ k : 𝕜, ∥k∥` has dense range in `ℝ`. -/
lemma normed_field.exists_nnnorm_lt_and_lt {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  (r : ℝ) (hr : 0 < r) : ∃ k : 𝕜, 1 - r < ∥k∥ ∧ ∥k∥ < 1 :=
begin
  sorry
end

-- it would be nice if maybe we could get this for `ℝ≥0` instead, but we go to `ℝ≥0∞` because it
-- is a complete lattice and therefore `supr` is well-behaved.
lemma key_lemma {𝕜 E : Type*} [nondiscrete_normed_field 𝕜] [non_unital_normed_ring E] [star_ring E]
  [cstar_ring E] [module 𝕜 E] [is_scalar_tower 𝕜 E E] [normed_space 𝕜 E] (a : E) :
  (∥a∥₊ : ℝ≥0∞) = ⨆ b (hb : ∥b∥₊ ≤ 1), ∥b * a∥₊ :=
begin
  refine le_antisymm _ (supr₂_le (λ b hb, _)),
  { by_cases h : ∥a∥₊ = 0,
    { rw h, exact_mod_cast zero_le _ },
    { refine ennreal.le_of_forall_pos_le_add (λ ε hε h_lt, _),
      rw ennreal.bsupr_add' (⟨0, by simp only [nnnorm_zero, zero_le']⟩ : ∃ x : E, ∥x∥₊ ≤ 1),
      /- we now want to choose some `k : 𝕜` such that `(1 + ε * ∥a∥₊⁻¹)⁻¹ * ∥a∥₊ < ∥k'∥₊ < 1`, then
      we will apply `refine le_trans _ (le_supr₂ (k⁻¹ • (star a)) _)`; This is why we want that
      lemma above. -/
      sorry, } },
  { calc (∥b * a∥₊ : ℝ≥0∞) ≤ ∥b∥₊ * ∥a∥₊ : by exact_mod_cast norm_mul_le _ _
    ...                    ≤ ∥a∥₊ : by simpa using (ennreal.coe_mono $ mul_le_mul_right' hb _) }
end

instance : cstar_ring 𝓜(𝕜, A) :=
{ norm_star_mul_self := sorry }

instance : complete_space 𝓜(𝕜, A) :=
{ complete := sorry }

end double_centralizer
