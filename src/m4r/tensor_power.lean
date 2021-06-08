import linear_algebra.tensor_algebra m4r.fin

universe u

variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M]
  [module R M] (n : ℕ)

open_locale classical tensor_product

def tensor_power_aux :
  ℕ → Σ (N : Type*) (h : add_comm_group N), @module R N _ h
| 0 := ⟨R, ⟨by apply_instance, by apply_instance⟩⟩
| (n+1) := ⟨@tensor_product R _ (tensor_power_aux n).1 M (@add_comm_group.to_add_comm_monoid _
  (tensor_power_aux n).2.1) _ (tensor_power_aux n).2.2 _, ⟨by apply_instance, by apply_instance⟩⟩

@[reducible] def tensor_power := (tensor_power_aux R M n).1

instance tensor_power_add_comm_group :
  add_comm_group (tensor_power R M n) := (tensor_power_aux R M n).2.1

instance tensor_power_module :
  module R (tensor_power R M n) :=
(tensor_power_aux R M n).2.2

instance tensor_power_zero_comm_ring : comm_ring (tensor_power_aux R M 0).1 := by assumption

namespace tensor_power

variables (R M)

def mk : Π (n : ℕ) (f : fin n → M), tensor_power R M n
| 0 _ := (1 : R)
| (n + 1) f := (mk n (fin.init f)) ⊗ₜ[R] (f n)

def mk' (n : ℕ) : multilinear_map R (λ i : fin n, M) (tensor_power R M n) :=
{ to_fun := mk R M n,
  map_add' := λ f m x y,
    begin
      induction n with n hn,
        { exact fin.elim0 m },
      { unfold mk,
        by_cases (m = n),
        { rw h,
          simp only [function.update_same],
          rw tensor_product.tmul_add,
          simp only [fin.init_update_last'] },
        { have Hn := hn (fin.init f) ⟨m, fin.succ_lt_of_ne m $
            (λ hnot, h $ fin.ext $ by rwa fin.coe_nat_fin_succ)⟩,
          rw [fin.init_update, fin.init_update, fin.init_update] at Hn,
          rw [Hn, tensor_product.add_tmul],
          repeat {rw function.update_noteq},
          all_goals {try {exact (ne.symm h)} },
          all_goals {exact (λ hnot, h $ fin.ext $ by rwa fin.coe_nat_fin_succ) }}}
    end,
  map_smul' := λ f m c x,
    begin
      induction n with n hn,
        { exact fin.elim0 m },
    { unfold mk,
      by_cases (m = n),
      { rw h,
        simp only [function.update_same],
        rw tensor_product.tmul_smul,
        congr' 3,
        rw [fin.init_update_last', fin.init_update_last'] },
      { have Hn := hn (fin.init f) ⟨m, fin.succ_lt_of_ne m $ (λ hnot, h $
          fin.ext $ by rwa fin.coe_nat_fin_succ)⟩,
        rw [fin.init_update, fin.init_update] at Hn,
        rw [Hn, tensor_product.smul_tmul'],
        repeat {rw function.update_noteq},
        all_goals {exact (ne.symm h) }}}
    end }

variables {R M}

lemma mk'_apply (n : ℕ) (x) : mk' R M n x = mk R M n x := rfl

lemma mk_one_lid (x : tensor_product R R M) :
  tensor_product.mk R R M 1 (tensor_product.lid R M x) = x :=
begin
  apply tensor_product.induction_on x,
  { rw linear_equiv.map_zero,
    convert tensor_product.tmul_zero _ _ },
  { intros y z,
    rw [tensor_product.lid_tmul, tensor_product.mk_apply, tensor_product.tmul_smul],
    erw tensor_product.smul_tmul',
    rw [algebra.id.smul_eq_mul, mul_one] },
  { intros y z hy hz,
    simp only [tensor_product.mk_apply, linear_equiv.map_add] at *,
    rw [tensor_product.tmul_add, hy, hz] },
end

lemma mk_one_lid_symm (x : M) :
  (tensor_product.lid R M).symm x = mk' R M 1 (λ i, x) :=
rfl

lemma mk_one_fin (r : R) (x : M) :
  (r ⊗ₜ[R] x : tensor_power R M 1) = tensor_power.mk R M 1 (λ i, r • x) :=
begin
  unfold tensor_power.mk,
  rw [tensor_product.tmul_smul, tensor_product.smul_tmul', algebra.id.smul_eq_mul, mul_one],
end

lemma mk_one_rid (x : tensor_product R M R) :
  tensor_product.mk R M R (tensor_product.rid R M x) 1 = x :=
begin
  apply tensor_product.induction_on x,
  { rw linear_equiv.map_zero,
    convert tensor_product.zero_tmul _ _ },
  { intros y z,
    erw tensor_product.lid_tmul,
    rw tensor_product.mk_apply,
    simp only,
    rw [tensor_product.smul_tmul, algebra.id.smul_eq_mul, mul_one] },
  { intros y z hy hz,
    simp only [tensor_product.mk_apply, linear_equiv.map_add] at *,
    rw [tensor_product.add_tmul, hy, hz] },
end

variables (R M)

def fin0_to_multilinear (f : R) :
  @multilinear_map R (fin 0) (λ _, M) R _ _ _ _ _ _ :=
{ to_fun := λ _, f,
  map_add' := λ x y a b, fin.elim0 y,
  map_smul' := λ x y, fin.elim0 y }

variables {R M}

@[simp] lemma to_span_singleton_apply (x : M) (r : R) :
  linear_map.to_span_singleton R M x r = r • x := rfl

lemma eq_smul_one (f : R →ₗ[R] M) (x : R) :
  x • f 1 = f x :=
by rw [←f.map_smul, algebra.id.smul_eq_mul, mul_one]

lemma eq_iff_eq_one (f g : R →ₗ[R] M) :
  f = g ↔ f 1 = g 1 :=
⟨λ h, h ▸ rfl, λ h, linear_map.ext $ λ x, by
  rw [←eq_smul_one, h, eq_smul_one]⟩

variables (R M)

def lift {M : Type u} [add_comm_group M] [module R M] :
  Π (n : ℕ) (P : Type u) {h1 : add_comm_group P}, by exactI Π
  {h2 : module R P}, by exactI Π
  (f : multilinear_map R (λ i : fin n, M) P),
  tensor_power R M n →ₗ[R] P
| 0 P h1 h2 g := @linear_map.to_span_singleton R P _
  (@add_comm_group.to_add_comm_monoid _ h1) h2 $ g (default (fin 0 → M))
| (n + 1) P h1 h2 g := @tensor_product.lift _ _ _ _ _ _ _
  (@add_comm_group.to_add_comm_monoid _ h1) _ _ h2
    $ lift n _ (@multilinear_map.curry_right _ _ _ _ _ _
        (@add_comm_group.to_add_comm_monoid _ h1) _ h2 g)

variables {R M}

lemma lift_mk {M : Type u} [add_comm_group M] [module R M] (n : ℕ) :
  ∀ {P : Type u} [add_comm_group P], by exactI ∀ [module R P],
  by exactI ∀ (f : @multilinear_map R (fin n) (λ _, M) P _ _ _ _ _ _),
  (lift R n P f).comp_multilinear_map (mk' R M n) = f :=
begin
  induction n with n hn,
  { intros,
    ext,
    show linear_map.to_span_singleton _ _ _ (1 : R) = _,
    rw linear_map.to_span_singleton_one,
    congr },
  { intros,
    ext,
    show tensor_product.lift _ (tensor_product.mk _ _ _ _ _) = _,
    rw [tensor_product.mk_apply, tensor_product.lift.tmul],
    unfreezingI {erw multilinear_map.ext_iff.1 (hn f.curry_right) (fin.init x)},
    rw f.curry_right_apply,
    congr,
    rw fin.snoc_succ },
end

lemma lift_mk_apply (n : ℕ)
  {P : Type u} [add_comm_group P] [module R P]
  (f : @multilinear_map R (fin n) (λ _, M) P _ _ _ _ _ _) (x) :
  lift R n P f (mk' R M n x) = f x := multilinear_map.ext_iff.1 (lift_mk n f) _

lemma lift_unique {M : Type u} [add_comm_group M] [module R M] (n : ℕ) :
  ∀ {P : Type u} [add_comm_group P], by exactI ∀ [module R P],
  by exactI ∀ (f : @multilinear_map R (fin n) (λ _, M) P _ _ _ _ _ _)
  (g : tensor_power R M n →ₗ[R] P) (H : ∀ x : fin n → M, g (mk' R M n x) = f x),
  g = lift R n P f :=
begin
  induction n with n hn,
  { intros,
    ext,
    rw ←eq_smul_one,
    erw H (default _),
    refl },
  { intros,
    unfold lift,
    ext (x : tensor_power R M n) y,
    erw tensor_product.lift.tmul,
    unfreezingI { rw ←hn f.curry_right (tensor_product.lcurry _ (tensor_power R M n) _ _ g)
     (λ x, begin
      ext z,
      rw [f.curry_right_apply, ←H (fin.snoc x z),
          tensor_product.lcurry_apply, mk'_apply, mk'_apply],
      unfold mk,
      congr,
      { ext,
        rw fin.init_snoc },
      { rw fin.snoc_mk_apply }
     end) },
    refl },
end

lemma mk_snoc {n : ℕ} (f : fin n → M) (z : M) :
  tensor_power.mk R M n.succ (fin.snoc f z) = tensor_product.mk _ _ _ (tensor_power.mk R M n f) z :=
begin
  unfold tensor_power.mk,
  rw fin.snoc_mk_apply,
  congr,
  ext,
  rw fin.init_snoc,
end

end tensor_power
