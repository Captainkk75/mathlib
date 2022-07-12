import representation_theory.cohomology.shenyang
import representation_theory.invariants
import representation_theory.cohomology.one_cocycles

universes v u w w'

noncomputable theory

namespace stuff

variables {k : Type*} [comm_ring k] {G H : Type u} [group G] [group H]
  {M N : Type v} [add_comm_group M] [add_comm_group N] [module k M] [module k N]
  (ρ : representation k G M) (τ : representation k H N)
  (f : G →* H) (φ : N →ₗ[k] M)

def pair : Prop :=
∀ (g : G) (x : N), φ (τ (f g) x) = ρ g (φ x)

variables (k)

@[simps] def pair_chain_map_aux (n : ℕ) :
  ((fin n → H) → N) →ₗ[k] ((fin n → G) → M) :=
{ to_fun := λ F x, φ (F (f ∘ x)),
  map_smul' := λ r x, by ext; exact φ.map_smul _ _,
  map_add' := λ x y, by ext; exact φ.map_add _ _ }

open representation

variables {k} (S : subgroup G)

def quotient_action_aux [h1 : S.normal] (g : G) :
  invariants (ρ.comp S.subtype) →ₗ[k] invariants (ρ.comp S.subtype) :=
{ to_fun := λ m, ⟨ρ g m, λ h, by { have : ρ (g⁻¹ * h * g) m = m,
  by {refine m.2 (⟨g⁻¹ * h * g, _⟩ : S),
  convert subgroup.normal.conj_mem h1 (h : S) h.2 g⁻¹, rw inv_inv},
  conv_rhs {rw ←this},

  sorry,
  --rw [←ρ.map_mul, ←mul_assoc, mul_inv_cancel_left, mul_smul],
  --refl
  }⟩,
  map_add' := sorry,
  map_smul' := sorry }

def inf_rep [S.normal] :
  representation k (G ⧸ S) (invariants (ρ.comp S.subtype)) :=
{ to_fun := λ g, quotient.lift_on' g (λ (g : G), quotient_action_aux ρ S g) $ λ a b hab,
  begin
    sorry/-ext,
    show (a • x : M) = b • x,
    have : (a⁻¹  * b) • (x : M) = x, from x.2 (⟨a⁻¹ * b, hab⟩),
    conv_lhs {rw ←this},
    rw [←mul_smul, mul_inv_cancel_left],-/
  end,
  map_one' := sorry,
  map_mul' := sorry }

lemma quotient_pair (S : subgroup G) [S.normal] :
  pair ρ (inf_rep ρ S) (quotient_group.mk' S) (invariants (ρ.comp S.subtype)).subtype :=
λ x y, rfl

lemma subgroup_pair (S : subgroup G) :
  pair (ρ.comp S.subtype) ρ S.subtype linear_map.id :=
λ x y, rfl

lemma rep_hom_pair {k : Type u} [comm_ring k] {G : Type u} [group G]
  {M N : Rep k G} (f : M ⟶ N) :
  pair N.ρ M.ρ (monoid_hom.id G) f.hom :=
λ g, linear_map.ext_iff.1 (f.comm _)

lemma pair_chain_map_aux_comm (hp : pair ρ τ f φ) (n : ℕ) :
  (cochain.d ρ n).comp (pair_chain_map_aux k f φ n)
    = (pair_chain_map_aux k f φ (n + 1)).comp (cochain.d τ n) :=
begin
  ext x g,
  dsimp [d_to_fun, pair_chain_map_aux],
  simp only [φ.map_add, φ.map_sum, φ.map_smul, hp (g 0)],
  congr,
  ext i,
  congr,
  ext j,
  dsimp,
  by_cases h : ((j : ℕ) < i),
  { simp only [F_lt_apply _ _ _ h] },
  { by_cases heq : ((j : ℕ) = i),
    { simp only [F_eq_apply _ _ _ heq, f.map_mul] },
    { simp only [F_neg_apply _ _ _ h heq] }}
end

def pair_chain_map (hp : pair ρ τ f φ) :
  cochain_cx τ ⟶ cochain_cx ρ :=
{ f := λ i, pair_chain_map_aux k f φ i,
  comm' := λ i j hij, by
  { cases hij,
    dsimp,
    erw [cochain_complex.of_d, cochain_complex.of_d],
    exact pair_chain_map_aux_comm ρ τ f φ hp i }}

def pair_homology_map (hp : pair ρ τ f φ) (n : ℕ) :
  (cochain_cx τ).homology n →ₗ[k] (cochain_cx ρ).homology n :=
(homology_functor _ _ n).map (pair_chain_map ρ τ f φ hp)

variables {G}

noncomputable def cohomology_map (ρ : representation k G M) (τ : representation k G N)
  (φ : M →ₗ[k] N) (hp : pair τ ρ (monoid_hom.id G) φ) (n : ℕ) :
  (cochain_cx ρ).homology n →ₗ[k] (cochain_cx τ).homology n :=
(pair_homology_map τ ρ (monoid_hom.id G) φ hp n)

noncomputable def cohomology_map' {k : Type u} [comm_ring k] {G : Type u} [group G]
  (M N : Rep k G) (φ : M ⟶ N) (n : ℕ) :
  (cochain_cx M.ρ).homology n →ₗ[k] (cochain_cx N.ρ).homology n :=
(pair_homology_map _ _ (monoid_hom.id G) φ.hom (rep_hom_pair φ) n)

def Res (S : subgroup G) (n : ℕ) :
  (cochain_cx ρ).homology n →ₗ[k] (cochain_cx (ρ.comp S.subtype)).homology n :=
pair_homology_map _ _ S.subtype linear_map.id (subgroup_pair ρ S) n

def Res_one (S : subgroup G) :
  firstcoh ρ →ₗ[k] firstcoh (ρ.comp S.subtype) :=
((first_iso (ρ.comp S.subtype)).to_linear_map.comp (Res ρ S 1)).comp (first_iso ρ).symm.to_linear_map

@[simp] lemma Res_one_apply (S : subgroup G) (x : one_cocycles ρ) :
  Res_one ρ S (quotient.mk' x : firstcoh ρ) = quotient.mk' (⟨↑x ∘ S.subtype, λ g h, x.2 g h⟩ : one_cocycles (ρ.comp S.subtype)) :=
begin
  sorry
end

def Inf (S : subgroup G) [h1 : S.normal] (n : ℕ) :
  (cochain_cx (inf_rep ρ S)).homology n →ₗ[k] (cochain_cx ρ).homology n :=
pair_homology_map _ _ (quotient_group.mk' S) (invariants (ρ.comp S.subtype)).subtype (quotient_pair ρ S) n

def Inf_one (S : subgroup G) [h1 : S.normal] :
  firstcoh (inf_rep ρ S) →ₗ[k] firstcoh ρ :=
((first_iso ρ).to_linear_map.comp (Inf ρ S 1)).comp
  (first_iso (inf_rep ρ S)).symm.to_linear_map

lemma Inf_one_apply_aux (S : subgroup G) [h1 : S.normal] (x : one_cocycles (inf_rep ρ S)) :
  (invariants (ρ.comp S.subtype)).subtype ∘ ↑x ∘ (coe : G → G ⧸ S) ∈ one_cocycles ρ :=
λ g h, subtype.ext_iff.1 (x.2 g h)
#exit
lemma Inf_one_apply (S : subgroup G) [h1 : S.normal] (x : one_cocycles (inf_rep ρ H)) :
  Inf_one ρ H (quotient.mk' x) =
    (⟨(invariants (ρ.comp S.subtype)).subtype ∘ ↑x ∘ (coe : G → G ⧸ H), Inf_one_apply_aux ρ H x⟩ : one_cocycles ρ) :=
begin
  sorry
end

def ibuprofenrules (S : subgroup G) [h1 : S.normal]
  (x : one_cocycles (G ⧸ H) (invariants H M)) (m : M)
  (h : ∀ g : G, ((↑x : G ⧸ H → invariants H M) (g : G ⧸ H) : M) = g • m - m) :
  G ⧸ H → M :=
λ g, quotient.lift_on' g (λ y, y • m - m) $ λ a b hab,
begin
  dsimp,
  rw [←h a, ←h b, quotient_group.eq.2 hab],
end

def ibuprofen (S : subgroup G) [h1 : S.normal]
  (x : one_cocycles (G ⧸ H) (invariants H M)) (m : M)
  (h : ∀ g : G, ((↑x : G ⧸ H → invariants H M) (g : G ⧸ H) : M) = g • m - m) :
  G ⧸ H → invariants H M :=
λ g, ⟨ibuprofenrules M H x m h g,
begin
  intros a,
  refine g.induction_on' _,
  intro y,
  dsimp [ibuprofenrules],
  rw ←h,
  exact coe_invariants _,
end⟩

lemma Inf_ker_eq_bot_aux (S : subgroup G) [h1 : S.normal]
  (x : one_cocycles (G ⧸ H) (invariants H M)) (m : M)
  (h : ∀ g : G, ((↑x : G ⧸ H → invariants H M) (g : G ⧸ H) : M) = g • m - m) :
  m ∈ invariants H M :=
begin
  intro y,
  rw ←sub_eq_zero,
  erw ←h y,
  rw [(quotient_group.eq_one_iff (y : G)).2 y.2, one_cocycles_map_one _],
  refl,
end

lemma Inf_ker_eq_bot (S : subgroup G) [h1 : S.normal] :
  (Inf_one M H).ker = ⊥ :=
begin
  rw eq_bot_iff,
  intros x,
  refine x.induction_on' _,
  intros y hy,
  erw [add_monoid_hom.mem_ker, Inf_one_apply] at hy,
  refine (quotient_add_group.eq_zero_iff y).2 _,
  obtain ⟨m, hm⟩ := (quotient_add_group.eq_zero_iff _).1 hy,
  let F := ibuprofen M H y m hm,
  use [m, Inf_ker_eq_bot_aux _ _ y _ hm],
  intro g,
  refine g.induction_on' _,
  { intro z, ext, exact hm z },
end

lemma Inf_one_range_le_Res_one_ker (S : subgroup G) [h1 : S.normal] :
  (Inf_one M H).range ≤ (Res_one M H).ker :=
begin
  intros x hx,
  obtain ⟨y, rfl⟩ := add_monoid_hom.mem_range.1 hx,
  refine quotient_add_group.induction_on' y (λ z, _),
  rw [add_monoid_hom.mem_ker, Inf_one_apply, Res_one_apply, quotient_add_group.eq_zero_iff],
  use 0,
  intro g,
  simp only [add_subgroup.coe_subtype, add_subgroup.coe_mk, subgroup.coe_subtype,
    function.comp_app, smul_zero, sub_zero, add_submonoid_class.coe_eq_zero],
  rw [(quotient_group.eq_one_iff (g : G)).2 g.2, one_cocycles_map_one],
end

lemma seriously (S : subgroup G) [h1 : S.normal] (h : H) (g : G) :
  g⁻¹ * h * g ∈ H :=
by {convert subgroup.normal.conj_mem h1 h h.2 g⁻¹, rw inv_inv }

lemma helper (S : subgroup G) [h1 : S.normal]  (y : one_cocycles G M) (m : M)
  (Hy : ∀ h : H, (y : G → M) h = h • m - m) (g : G) (h : H) :
  h • ((y : G → M) g - g • m + m) = (y : G → M) g - g • m + m :=
begin
  have := one_cocycles_map_mul y g (g⁻¹ * h * g),
  rw [mul_assoc, mul_inv_cancel_left, one_cocycles_map_mul, Hy, ←mul_assoc, (show
    (y : G → M) (g⁻¹ * h * g) = (g⁻¹ * h * g) • m - m, from Hy (⟨g⁻¹ * h * g, seriously _ _ _⟩)),
    smul_sub, mul_assoc, mul_smul, smul_inv_smul, mul_smul, ←eq_sub_iff_add_eq] at this,
  rw [smul_add, smul_sub],
  erw this,
  show h • g • m - _ + _ - _ - _ + _ = _,
  abel,
end

lemma Inf_one_range_eq_Res_one_ker (S : subgroup G) [h1 : S.normal] :
  (Inf_one M H).range = (Res_one M H).ker :=
le_antisymm (Inf_one_range_le_Res_one_ker M H) $ λ x,
begin
  refine quotient_add_group.induction_on' x _,
  intros y hy,
  rw [add_monoid_hom.mem_ker, Res_one_apply] at hy,
  obtain ⟨m, hm⟩ := (quotient_add_group.eq_zero_iff _).1 hy,
  let F' : G ⧸ H → M := λ g, quotient.lift_on' g
    (λ g, (y : G → M) g - g • m + m)
    (λ a b hab, by
    {dsimp,
     congr' 1,
     have Hy : (y : G → M) (a⁻¹ * b) = (a⁻¹ * b) • m - m := hm ⟨a⁻¹ * b, hab⟩,
     rw [one_cocycles_map_mul] at Hy,
     replace Hy := congr_arg ((•) a) Hy,
     simp only [smul_add, smul_sub, smul_inv_smul, mul_smul] at Hy,
     rw [one_cocycles_map_inv, add_neg_eq_iff_eq_add] at Hy,
     rw Hy,
     abel }),
  let F : G ⧸ H → invariants H M :=
  λ g, ⟨F' g, by {refine g.induction_on' _, intro x, dsimp [F'], exact helper M H y m hm x}⟩,
  have HF : F ∈ one_cocycles (G ⧸ H) (invariants H M) := λ g h,
  begin
    refine quotient.induction_on₂' g h _,
    intros a b,
    show _ - F (quotient.mk' (a * b)) + _ = _,
    ext,
    dsimp [F, F', (•), quotient_action_aux],
    rw [one_cocycles_map_mul, smul_add, smul_sub, mul_smul],
    abel,
  end,
  let FF : firstcoh (G ⧸ H) (invariants H M) := (⟨F, HF⟩ : one_cocycles _ _),
  use FF,
  rw Inf_one_apply,
  dsimp [FF, F, F'],
  rw quotient_add_group.eq,
  use m,
  intro g,
  dsimp,
  abel,
end

end stuff
