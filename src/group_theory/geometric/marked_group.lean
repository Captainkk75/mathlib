import group_theory.geometric.mathlib
import group_theory.geometric.normed_group

/-!
# Marked groups
-/

set_option old_structure_cmd true

noncomputable theory
open function nat list real set

namespace geometric_group_theory
variables (G S : Type*) [group G]

/-- A marking of a group is a generating family of elements. -/
structure marking extends free_group S →* G :=
(to_fun_surjective : surjective to_fun)

namespace marking
variables {G S}

instance : monoid_hom_class (marking G S) (free_group S) G :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_mul := λ f, f.map_mul',
  map_one := λ f, f.map_one' }

lemma map_surjective (m : marking G S) : surjective m := m.to_fun_surjective

end marking

/-- The trivial marking. -/
def marking.refl : marking G G :=
{ to_fun_surjective := λ x, ⟨free_group.of x, free_group.lift.of⟩,
  ..free_group.lift id }

variables {G S} {m : marking G S}

/-- A type synonym of `G`, tagged with a marking of the group. -/
@[derive group] def marked (m : marking G S) : Type* := G

instance : add_group (marked m) := additive.add_group

/-- "Identity" isomorphism between `G` and a marking of it. -/
def to_marked : G ≃* marked m := mul_equiv.refl _

/-- "Identity" isomorphism between a marking of `G` and itself. -/
def of_marked : marked m ≃* G := mul_equiv.refl _

@[simp] lemma to_marked_symm_eq : (to_marked : G ≃* marked m).symm = of_marked := rfl
@[simp] lemma of_marked_symm_eq : (of_marked : marked m ≃* G).symm = to_marked := rfl
@[simp] lemma to_marked_of_marked (a) : to_marked (of_marked (a : marked m)) = a := rfl
@[simp] lemma of_marked_to_marked (a) : of_marked (to_marked a : marked m) = a := rfl
@[simp] lemma to_marked_inj {a b} : (to_marked a : marked m) = to_marked b ↔ a = b := iff.rfl
@[simp] lemma of_marked_inj {a b : marked m} : of_marked a = of_marked b ↔ a = b := iff.rfl

lemma aux [decidable_eq S] (x : marked m) :
  ∃ n (l : free_group S), m l = x ∧ l.to_word.length ≤ n :=
by { classical, obtain ⟨l, rfl⟩ := m.map_surjective x, exact ⟨_, _, rfl, le_rfl⟩ }

instance : normed_mul_group (marked m) :=
group_norm.to_normed_mul_group _
{ to_fun := λ x, by classical; exact nat.find (aux x),
  map_one' := cast_eq_zero.2 $ (find_eq_zero $ aux _).2 ⟨1, map_one _, le_rfl⟩,
  nonneg' := λ _, cast_nonneg _,
  mul_le' := λ x y, begin
    norm_cast,
    obtain ⟨a, rfl, ha⟩ := nat.find_spec (aux x),
    obtain ⟨b, rfl, hb⟩ := nat.find_spec (aux y),
    refine find_le ⟨a * b, map_mul _ _ _, _⟩,
    refine (a.to_word_mul_sublist _).length.trans _,
    rw length_append,
    exact add_le_add ha hb,
  end,
  inv' := begin
    suffices : ∀ {x : marked m}, nat.find (aux x⁻¹) ≤ nat.find (aux x),
    { refine λ _, congr_arg coe (this.antisymm _),
      convert this,
      simp_rw inv_inv },
    refine λ x, find_mono (λ n, _),
    rintro ⟨l, hl, h⟩,
    exact ⟨l⁻¹, by simp [hl], h.trans_eq' $ by simp⟩,
  end,
  eq_one_of_to_fun := λ x hx, begin
    obtain ⟨l, rfl, hl⟩ := (find_eq_zero $ aux _).1 (cast_eq_zero.1 hx),
    rw [nat.le_zero_iff, length_eq_zero] at hl,
    sorry,
  end }

/- comments by Sébastien Gouëzel:

If you want to register your group as a metric space (where the distance depends on S), you will need to embrace the type synonym trick. Instead of a class, define a structure marking S G as you did. And then given a group G and a marking m, define a new type marked_group m G := G. On this new type, you can register the same group structure as on G, but you can also register a distance as m is now available to the system when you consider x y : marked_group m G.

    First, work with normed groups, and prove whatever you like here. Possibly adding new typeclass assumptions that say that the distance is proper or hyperbolic or whatever.
    Then, to construct instances of such normed groups, do it on type synonyms. For instance, given two types S and G with [group G], define marking S G as the space of markings of G parameterized by S. Then, given a group G and a marking m, define a typemarked_group G m := G as a copy of G, then define on it the group structure coming from G (with @[derive ...]) and the norm associated to m. Then marked_group G m will be an instance of a normed group.

-/

end geometric_group_theory
