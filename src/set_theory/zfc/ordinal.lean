import set_theory.zfc.basic

namespace Set

/-- A set is a von Neumann ordinal when it's well-ordered with respect to `∈`, and every element is
a subset.-/
def is_ordinal (x : Set) : Prop := is_well_order x.to_set (subrel (∈) _) ∧ ∀ y ∈ x, y ⊆ x

theorem is_ordinal.is_well_order {x : Set} (h : x.is_ordinal) :
  is_well_order x.to_set (subrel (∈) _) :=
h.1

theorem is_ordinal.subset_of_mem {x y : Set} (hx : x.is_ordinal) : y ∈ x → y ⊆ x :=
hx.2 y

theorem is_ordinal.mem_trichotomous {x y z : Set} (hx : x.is_ordinal) (hy : y ∈ x) (hz : z ∈ x) :
  y ∈ z ∨ y = z ∨ z ∈ y :=
begin
  haveI := hx.is_well_order,
  simpa using @trichotomous x.to_set (subrel (∈) _) _ ⟨y, hy⟩ ⟨z, hz⟩
end

theorem is_ordinal.mem_trans {x y z : Set} (hx : x.is_ordinal) (hz : z ∈ y) (hy : y ∈ x) : z ∈ x :=
hx.subset_of_mem hy hz

theorem is_ordinal.mem_trans' {x y z w : Set} (hx : x.is_ordinal)
  (hy : y ∈ z) (hz : z ∈ w) (hw : w ∈ x) : y ∈ w :=
let H := hx.is_well_order.trans, hz' := hx.mem_trans hz hw in
  H ⟨y, hx.mem_trans hy hz'⟩ ⟨z, hz'⟩ ⟨w, hw⟩ hy hz

theorem is_ordinal.mem {x y : Set} (hx : x.is_ordinal) (hy : y ∈ x) : y.is_ordinal :=
begin
  refine ⟨@rel_embedding.is_well_order _ _ _ _ _ hx.is_well_order,
    λ z hz a ha, hx.mem_trans' ha hz hy⟩,
  exact ⟨⟨λ b, ⟨b.1, hx.subset_of_mem hy b.2⟩, λ a b, by simp [subtype.coe_inj]⟩,
    λ a b, by simp⟩
end

@[simp] theorem empty_is_ordinal : is_ordinal ∅ :=
⟨by { rw empty_to_set, apply_instance }, λ y, by simp⟩

/-- The successor of an ordinal `x` is `x ∪ {x}`. -/
def succ (x : Set) : Set := insert x x

@[simp] theorem mem_succ_iff {x y : Set} : y ∈ succ x ↔ y = x ∨ y ∈ x := by simp [succ]

theorem mem_succ_of_mem {x y : Set} (h : y ∈ x) : y ∈ succ x := mem_succ_iff.2 $ or.inr h

theorem mem_succ_self (x : Set) : x ∈ succ x := mem_succ_iff.2 $ or.inl rfl

@[simp] theorem succ_to_set (x : Set) : x.succ.to_set = insert x x.to_set := by simp [succ]

theorem is_ordinal.succ {x : Set} (hx : x.is_ordinal) : x.succ.is_ordinal :=
begin
  refine ⟨_, λ y hy z hz, _⟩,
  { exact
    { trichotomous := begin
        rintros ⟨a, ha⟩ ⟨b, hb⟩,
        rw [mem_to_set, mem_succ_iff] at ha hb,
        rcases ha with rfl | ha;
        rcases hb with rfl | hb,
        { exact or.inr (or.inl rfl) },
        { exact or.inr (or.inr hb) },
        { exact or.inl ha },
        { simpa using hx.mem_trichotomous ha hb }
      end,
      irrefl := sorry,
      trans := begin
        rintros ⟨a, ha⟩ ⟨b, hb⟩,
        rw [mem_to_set, mem_succ_iff] at ha hb,
        rcases ha with rfl | ha;
        rcases hb with rfl | hb,
        { exact or.inr (or.inl rfl) },
        { exact or.inr (or.inr hb) },
        { exact or.inl ha },
        { simpa using hx.mem_trichotomous ha hb }
      end,
      wf := sorry } },
  { rcases mem_succ_iff.1 hy with rfl | hy,
    { exact mem_succ_of_mem hz },
    { exact mem_succ_of_mem (hx.mem_trans hz hy) } }
end

end Set
