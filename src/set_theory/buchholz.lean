import set_theory.cardinal_ordinal

noncomputable theory

-- This should go on another PR.

namespace ordinal

/-- The minimum excluded ordinal in a family of ordinals. -/
def mex {ι} (f : ι → ordinal) : ordinal :=
omin (set.range f)ᶜ ⟨_, lsub_nmem_range f⟩

theorem mex_nmem {ι} (f : ι → ordinal) (i) : f i ≠ mex f :=
λ h, (omin_mem (set.range f)ᶜ _) ⟨i, h⟩

theorem mex_le_of_nmem {ι} {f : ι → ordinal} {a} (ha : ∀ i, f i ≠ a) : mex f ≤ a :=
by { apply omin_le, simp [ha] }

theorem mem_of_lt_mex {ι} {f : ι → ordinal} {a} (ha : a < mex f) : ∃ i, f i = a :=
by { by_contra' ha', exact not_le_of_lt ha (mex_le_of_nmem ha') }

theorem mex_le_lsub {ι} (f : ι → ordinal) : mex f ≤ lsub f :=
omin_le (lsub_nmem_range f)

theorem mex.monotone {α β} (f : α → ordinal) (g : β → ordinal) (h : set.range f ⊆ set.range g) :
  mex f ≤ mex g :=
begin
  refine mex_le_of_nmem (λ i hi, _),
  cases h ⟨i, rfl⟩ with j hj,
  rw ←hj at hi,
  exact mex_nmem g j hi
end

theorem mex_lt_card_succ {ι} (f : ι → ordinal) : mex f < (cardinal.mk ι).succ.ord :=
begin
  by_contra' h,
  apply not_le_of_lt (cardinal.lt_succ_self (cardinal.mk ι)),
  let g : (cardinal.mk ι).succ.ord.out.α → ι :=
    λ a, classical.some (mem_of_lt_mex ((typein_lt_self a).trans_le h)),
  have hg : function.injective g := begin
    intros a b h',
    have H : ∀ x, f (g x) = typein _ x :=
      λ x, classical.some_spec (mem_of_lt_mex ((typein_lt_self x).trans_le h)),
    apply_fun f at h',
    rwa [H, H, typein_inj] at h'
  end,
  convert cardinal.mk_le_of_injective hg,
  rw cardinal.mk_ord_out
end

end ordinal

open cardinal
namespace ordinal

/-- The `Ωᵥ` function as defined by Buchholz. -/
-- Todo: generalize
def Omega : ℕ → cardinal.{0}
| 0       := 1
| (v + 1) := aleph (v + 1)

theorem Omega_pos : Π v, 0 < Omega v
| 0       := cardinal.zero_lt_one
| (v + 1) := aleph_pos _

theorem Omega_le_aleph : Π v, Omega v ≤ aleph v
| 0       := by { convert le_of_lt cardinal.one_lt_omega, exact aleph_zero }
| (v + 1) := le_of_eq rfl

theorem Omega_strict_mono : strict_mono Omega :=
begin
  rintros ⟨_⟩ ⟨_⟩ h,
  { exact (lt_irrefl 0 h).elim },
  { exact cardinal.one_lt_omega.trans_le (omega_le_aleph b.succ) },
  { exact (not_lt_bot h).elim },
  { exact cardinal.aleph_lt.2 (ordinal.nat_cast_lt.2 h) }
end

-- Omega is principal additive

/-- The type of all Buchholz expressions. These may consist of
* ordinals less than `Ωᵥ`
* sums of two other Buchholz expressions
* some function `Ψᵤ` applied to a Buchholz expression -/
inductive buchholz_exp' (v : ℕ) : Type 0
| lt_Omega' (a : (Omega v).ord.out.α) : buchholz_exp'
| add       (a b : buchholz_exp') : buchholz_exp'
| psi       (u : ℕ) (a : buchholz_exp') : buchholz_exp'

namespace buchholz_exp'

/-- A Buchholz expression from an ordinal less than `Ωᵥ`. -/
def lt_Omega {v : ℕ} {a : ordinal} (ha : a < (Omega v).ord) : buchholz_exp' v :=
buchholz_exp'.lt_Omega' (enum (Omega v).ord.out.r a (by rwa type_out))

instance (v : ℕ) : has_zero (buchholz_exp' v) :=
⟨lt_Omega (ord_lt_ord.2 (Omega_pos v))⟩

/-- The value of a well-formed Buchholz expression when interpreted as an ordinal. -/
noncomputable def value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  buchholz_exp' v → ordinal
| (lt_Omega' a)  := typein (Omega v).ord.out.r a
| (add a b)      := a.value + b.value
| (psi u a)      := if ha : a.value < o then Ψ _ ha u else 0

@[simp] theorem lt_Omega'_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (a : (Omega v).ord.out.α) : (lt_Omega' a).value Ψ = typein (Omega v).ord.out.r a :=
rfl

@[simp] theorem lt_Omega_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) {a : ordinal}
  (ha : a < (Omega v).ord) : (lt_Omega ha).value Ψ = a :=
typein_enum _ _

theorem zero_value {o : ordinal} (ho : o = 0) {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  Π (e : buchholz_exp' v), e.value Ψ < (Omega v).ord
| (lt_Omega' a)  := typein_lt_self _
| (add a b)      := sorry -- this is a theorem about additive principal ordinals.
| (psi u a)      := begin
  unfold value,
  split_ifs,
  { simp_rw ho at h,
    exact (not_lt_bot h).elim },
  rw ←ord_zero,
  exact ord_lt_ord.2 (Omega_pos v)
end

@[simp] theorem add_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (e₁ e₂ : buchholz_exp' v) : (add e₁ e₂).value Ψ = e₁.value Ψ + e₂.value Ψ :=
by unfold value

@[simp] theorem psi_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (u : ℕ) {e : buchholz_exp' v} (he : e.value Ψ < o) : (psi u e).value Ψ = Ψ (e.value Ψ) he u :=
by { unfold value, exact dif_pos he }

/-- The height of a Buchholz expression, thought of as a syntax tree. -/
noncomputable def height {v : ℕ} : buchholz_exp' v → ℕ
| (lt_Omega' a) := 0
| (add a b)     := max (height a) (height b) + 1
| (psi u a)     := height a + 1

theorem lt_Omega'_height {v : ℕ} (a) : height (@lt_Omega' v a) = 0 :=
rfl

theorem lt_Omega'_of_height {v : ℕ} {e : buchholz_exp' v} (he : height e = 0) :
  ∃ a, e = lt_Omega' a :=
by { induction e with a, use a, all_goals { simpa only [height] } }

theorem left_height_lt_add_height {v : ℕ} (a b : buchholz_exp' v) : a.height < (add a b).height :=
by { unfold height, exact nat.lt_succ_iff.2 (le_max_left _ _) }

theorem right_height_lt_add_height {v : ℕ} (a b : buchholz_exp' v) : b.height < (add a b).height :=
by { unfold height, exact nat.lt_succ_iff.2 (le_max_right _ _) }

theorem psi_height {v : ℕ} (u : ℕ) (a : buchholz_exp' v) : (psi u a).height = a.height + 1 :=
by unfold height

/-- An auxiliary definition which gives a denumerable family of well-formed Buchholz expressions. -/
def add_iterate (n : ℕ) : buchholz_exp' 0 :=
(add 0)^[n] 0

theorem add_iterate_succ (n : ℕ) : add_iterate n.succ = (add 0) ((add 0)^[n] 0) :=
by { unfold add_iterate, rw function.iterate_succ_apply' }

theorem add_iterate.inj : function.injective add_iterate :=
begin
  intros m n h,
  induction m with m hm generalizing n; cases n,
  all_goals { simp only [add_iterate, function.iterate_succ'] at h },
  any_goals { cases h },
  rw hm (add.inj h).right
end

private theorem card_of_height (v : ℕ) : Π h, mk {e : buchholz_exp' v | e.height ≤ h} ≤ aleph v
| 0 := begin
  refine le_trans _ (Omega_le_aleph v),
  let f : ↥{e : buchholz_exp' v | e.height = 0} → (Omega v).ord.out.α :=
    λ e, classical.some (lt_Omega'_of_height e.prop),
  have hf : function.injective f := begin
    intros e₁ e₂ h,
    apply_fun lt_Omega' at h,
    have H := λ e : ↥{e : buchholz_exp' v | e.height = 0},
      classical.some_spec (lt_Omega'_of_height e.prop),
    rwa [←H, ←H, ←subtype.ext_iff] at h
  end,
  convert mk_le_of_injective hf,
  simp only [nonpos_iff_eq_zero],
  exact (mk_ord_out _).symm
end
| (h + 1) := begin
  let α : Type := {e : buchholz_exp' v | e.height ≤ h},
  have hα : mk α ≤ aleph v := card_of_height h,
  let f : ↥{e : buchholz_exp' v | e.height ≤ h + 1} → (Omega v).ord.out.α ⊕ (α × α) ⊕ (ℕ × α) :=
  begin
    rintro ⟨a | ⟨a, b⟩ | ⟨u, a⟩, he⟩;
    dsimp at he,
    { exact sum.inl a },
    { exact sum.inr (sum.inl ⟨
      ⟨a, nat.lt_succ_iff.1 ((left_height_lt_add_height a b).trans_le he)⟩,
      ⟨b, nat.lt_succ_iff.1 ((right_height_lt_add_height a b).trans_le he)⟩⟩) },
    { refine sum.inr (sum.inr ⟨u, a, _⟩),
      rw psi_height at he,
      exact nat.le_of_add_le_add_right he }
  end,
  have hf : function.injective f := begin
    rintro ⟨a | ⟨a, b⟩ | ⟨u, a⟩, he₁⟩;
    rintro ⟨c | ⟨c, d⟩ | ⟨w, c⟩, he₂⟩;
    intro h;
    simp [f] at *;
    assumption
  end,
  apply le_trans (mk_le_of_injective hf),
  simp only [mk_prod, mk_sum, lift_uzero, mk_denumerable],
  convert cardinal.add_le_add (Omega_le_aleph v)
    (cardinal.add_le_add (mul_le_mul' hα hα) (mul_le_mul' (omega_le_aleph v) hα)),
  { exact cardinal.mk_ord_out _ },
  { simp only [cardinal.mul_eq_self (omega_le_aleph v), cardinal.add_eq_self (omega_le_aleph v)] }
end

private theorem card_eq_Union_height (v : ℕ) :
  mk (buchholz_exp' v) = mk (⋃ h, {e : buchholz_exp' v | e.height ≤ h}) :=
begin
  let f : buchholz_exp' v → ⋃ h, {e : buchholz_exp' v | e.height ≤ h} :=
    λ e', ⟨e', by { rw set.mem_Union, exact ⟨_, le_refl e'.height⟩ }⟩,
  refine le_antisymm
    (@mk_le_of_injective _ _ f (λ e₁ e₂ h, _))
    (@mk_le_of_surjective _ _ f (λ a, ⟨a, _⟩)),
  { simp only [subtype.mk_eq_mk] at h, exact h },
  { simp only [f, subtype.coe_eta] }
end

theorem card_eq_aleph (v : ℕ) : mk (buchholz_exp' v) = cardinal.aleph v :=
begin
  apply le_antisymm,
  { rw card_eq_Union_height,
    apply le_trans (mk_Union_le _) _,
    rw [mk_nat],
    refine le_trans (mul_le_max _ _) (max_le (max_le (omega_le_aleph v) _) (omega_le_aleph v)),
    { rw cardinal.sup_le,
      exact card_of_height v } },
  { induction v with v hv,
    { convert cardinal.mk_le_of_injective add_iterate.inj, simp },
    { convert cardinal.mk_le_of_injective (@lt_Omega'.inj (v + 1)),
      exact (cardinal.mk_ord_out _).symm } }
end

/-- A well-formed Buchholz expression is one where `Ψ` is only ever called with arguments with value
less than `o`. -/
def well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) : set (buchholz_exp' v)
| (lt_Omega' a)  := tt
| (add a b)      := a.well_formed ∧ b.well_formed
| (psi u a)      := a.well_formed ∧ a.value Ψ < o

theorem lt_Omega'_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal)
  (a : (Omega v).ord.out.α) : lt_Omega' a ∈ well_formed v Ψ :=
(rfl : well_formed v Ψ (lt_Omega' a))

theorem lt_Omega_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal)
  {a : ordinal} (ha : a < (Omega v).ord) : lt_Omega ha ∈ well_formed v Ψ :=
lt_Omega'_well_formed v Ψ _

theorem zero_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) :
  (0 : buchholz_exp' v) ∈ well_formed v Ψ :=
lt_Omega_well_formed v Ψ _

theorem add_well_formed {o : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} {e₁ e₂} :
  e₁ ∈ well_formed v Ψ ∧ e₂ ∈ well_formed v Ψ ↔ add e₁ e₂ ∈ well_formed v Ψ :=
iff.rfl

theorem psi_well_formed {o : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} {e : buchholz_exp' v}
  (u : ℕ) : e ∈ well_formed v Ψ ∧ e.value Ψ < o ↔ psi u e ∈ well_formed v Ψ :=
iff.rfl

theorem add_iterate_well_formed {o : ordinal} (Ψ : Π a, a < o → ℕ → ordinal) (n : ℕ) :
  (add_iterate n) ∈ well_formed 0 Ψ :=
begin
  have h := zero_well_formed 0 Ψ,
  induction n with n hn,
  { exact h },
  { rw add_iterate_succ, exact add_well_formed.2 ⟨h, hn⟩ }
end

theorem value_eq_of_extend_psi {o o' : ordinal} (ho : o ≤ o') {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal}
  {Ψ' : Π a, a < o' → ℕ → ordinal} (H : ∀ a (ha : a < o) u, Ψ a ha u = Ψ' a (ha.trans_le ho) u)
  (e : buchholz_exp' v) (he : e ∈ well_formed v Ψ) : e.value Ψ = e.value Ψ' :=
begin
  induction e with a a b ha hb u a h,
  { refl },
  { unfold value, rw [ha he.1, hb he.2] },
  { unfold value,
    rw ←(h he.1) at *,
    split_ifs with hΨ hΨ' hΨ',
    { exact H _ _ u },
    { exact (hΨ' (hΨ.trans_le ho)).elim },
    { exact (hΨ he.2).elim },
    { refl } }
end

end buchholz_exp'

/-- The type of well-formed Buchholz expressions. This corresponds to `C` in Buchholz's original
definition. -/
def buchholz_exp (o : ordinal) (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) : Type 0 :=
buchholz_exp'.well_formed v Ψ

namespace buchholz_exp

/-- Transfers a well-formed Buchholz expression for a family of functions to a larger one. -/
def lift {o o' : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} (ho : o ≤ o')
  {Ψ' : Π a, a < o' → ℕ → ordinal} (H : ∀ a (ha : a < o) u, Ψ a ha u = Ψ' a (ha.trans_le ho) u)
  (e : buchholz_exp o v Ψ) : buchholz_exp o' v Ψ' :=
⟨e.val, begin
  revert e,
  rintro ⟨e, he⟩,
  dsimp,
  induction e with a a b ha hb u a ha,
  { exact buchholz_exp'.lt_Omega'_well_formed v Ψ' a },
  { exact buchholz_exp'.add_well_formed.2 ⟨ha he.1, hb he.2⟩ },
  { refine (buchholz_exp'.psi_well_formed u).2 ⟨ha he.1, _⟩,
    rw ←buchholz_exp'.value_eq_of_extend_psi ho H _ he.1,
    exact he.2.trans_le ho }
end⟩

/-- The hypothesis needed to use lift on an unbounded family of functions. -/
theorem lift_H {o o' : ordinal} (ho : o ≤ o') (Ψ : ordinal → ℕ → ordinal) (a) (ha : a < o) (u) :
  (λ a (ha : a < o) u, Ψ a u) a ha u = (λ a (ha : a < o') u, Ψ a u) a (ha.trans_le ho) u :=
rfl

/-- A well-formed Buchholz expression from an ordinal less than `Ωᵥ`. -/
def lt_Omega' {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) (a : (Omega v).ord.out.α) :
  buchholz_exp o v Ψ :=
⟨_, buchholz_exp'.lt_Omega'_well_formed v Ψ a⟩

/-- A well-formed Buchholz expression from an ordinal less than `Ωᵥ`. -/
def lt_Omega {o : ordinal} {v : ℕ} {a : ordinal} (ha : a < (Omega v).ord)
  (Ψ : Π a, a < o → ℕ → ordinal) : buchholz_exp o v Ψ :=
⟨_, buchholz_exp'.lt_Omega_well_formed v Ψ ha⟩

theorem lt_Omega'.inj {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) :
  function.injective (@lt_Omega' o v Ψ) :=
λ a b h, buchholz_exp'.lt_Omega'.inj (subtype.mk.inj h)

/-- The value of a well-formed Buchholz expression when interpreted as an ordinal. -/
def value {o : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} (a : buchholz_exp o v Ψ) :
  ordinal :=
a.val.value Ψ

theorem lt_Omega_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) {a : ordinal}
  (ha : a < (Omega v).ord) : (lt_Omega ha Ψ).value = a :=
buchholz_exp'.lt_Omega_value Ψ ha

theorem zero_value {o : ordinal} (ho : o = 0) {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (e : buchholz_exp o v Ψ) : e.value < (Omega v).ord :=
buchholz_exp'.zero_value ho Ψ _

@[simp] theorem lift_value {o o' : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} (ho : o ≤ o')
  {Ψ' : Π a, a < o' → ℕ → ordinal} (H : ∀ a (ha : a < o) u, Ψ a ha u = Ψ' a (ha.trans_le ho) u)
  (e : buchholz_exp o v Ψ) : (lift ho H e).value = e.value :=
begin
  revert e,
  rintro ⟨e, he⟩,
  unfold lift value,
  induction e with a a b ha hb u a ha,
  { refl },
  { unfold buchholz_exp'.value,
    rw [ha he.1, hb he.2] },
  { rw [buchholz_exp'.psi_value _ u he.2, buchholz_exp'.psi_value];
    simp_rw ha he.1,
    { exact (H _ _ u).symm },
    { exact he.2.trans_le ho } }
end

/-- An auxiliary definition which gives a denumerable family of well-formed Buchholz expressions. -/
def add_iterate {o : ordinal} (Ψ : Π a, a < o → ℕ → ordinal) (n : ℕ) : buchholz_exp o 0 Ψ :=
⟨_, buchholz_exp'.add_iterate_well_formed Ψ n⟩

theorem add_iterate.inj {o : ordinal} (Ψ : Π a, a < o → ℕ → ordinal) :
  function.injective (add_iterate Ψ) :=
λ a b h, buchholz_exp'.add_iterate.inj (subtype.mk.inj h)

theorem card_eq_aleph {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  mk (buchholz_exp o v Ψ) = cardinal.aleph v :=
begin
  apply le_antisymm,
  { rw ←buchholz_exp'.card_eq_aleph,
    exact mk_le_of_injective (λ a b h, subtype.ext_val h) },
  { induction v with v hv,
    { convert cardinal.mk_le_of_injective (add_iterate.inj Ψ), simp },
    { convert cardinal.mk_le_of_injective (lt_Omega'.inj (v + 1) Ψ),
      exact (cardinal.mk_ord_out _).symm } }
end

end buchholz_exp

/-- Buchholz's `Ψ` function. -/
def buchholz : ordinal → ℕ → ordinal.{0} :=
wf.fix $ λ o Ψ v, mex (@buchholz_exp.value o v Ψ)

theorem buchholz_def' : Π o, buchholz o = λ v, mex (@buchholz_exp.value o v (λ a _, buchholz a)) :=
wf.fix_eq _

theorem buchholz_def (o : ordinal) (v : ℕ) :
  buchholz o v = mex (@buchholz_exp.value o v (λ a _, buchholz a)) :=
by rw buchholz_def'

theorem Omega_le_buchholz (o : ordinal) (v : ℕ) : (Omega v).ord ≤ buchholz o v :=
begin
  rw buchholz_def,
  by_contra' h,
  exact mex_nmem _ (buchholz_exp.lt_Omega h _) (buchholz_exp.lt_Omega_value _ _)
end

theorem buchholz_zero (v : ℕ) : buchholz 0 v = (Omega v).ord :=
begin
  refine le_antisymm _ (Omega_le_buchholz 0 v),
  rw buchholz_def,
  exact (mex_le_lsub _).trans (lsub_le.2 (buchholz_exp.zero_value rfl _))
end

-- Buchholz is additive principal

theorem buchholz_lt_Omega (o : ordinal) (v : ℕ) : buchholz o v < (Omega (v + 1)).ord :=
begin
  rw buchholz_def,
  convert mex_lt_card_succ.{0 0} buchholz_exp.value,
  rw [buchholz_exp.card_eq_aleph, ←aleph_succ],
  refl
end

/-- Buchholz's psi function is strictly monotonic in its subscript. -/
theorem buchholz_strict_mono (o : ordinal) : strict_mono (buchholz o) :=
λ a b h, (buchholz_lt_Omega o a).trans_le $
  (ord_le_ord.2 (Omega_strict_mono.monotone (nat.succ_le_iff.2 h))).trans (Omega_le_buchholz o b)

/-- Buchholz's psi function is monotonic in its ordinal argument. -/
theorem buchholz_monotone (v : ℕ) : monotone (function.swap buchholz v) :=
begin
  intros a b h,
  unfold function.swap,
  rw [buchholz_def, buchholz_def],
  apply mex.monotone,
  rintros o ⟨e, he⟩,
  use buchholz_exp.lift h (buchholz_exp.lift_H h buchholz) e,
  rw ←he,
  exact buchholz_exp.lift_value h _ e
end

end ordinal
