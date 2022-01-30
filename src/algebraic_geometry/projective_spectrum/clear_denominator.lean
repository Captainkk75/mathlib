import ring_theory.localization
import ring_theory.graded_algebra.basic

open_locale  big_operators

section clear_denominator

variables (R : Type*) [comm_ring R] (f : R) [decidable_eq (localization.away f)]

def clear_denominator (s : finset (localization.away f)) :
  ∃ (n : ℕ), ∀ (x : localization.away f), x ∈ s →
    x * (localization.mk (f^n) 1 : localization.away f) ∈
    (λ y : R, (localization.mk y 1 : localization.away f)) '' set.univ :=
begin
  induction s using finset.induction_on with a s a_nin_s ih,
  { refine ⟨0, λ x rid, _⟩, exfalso, erw set.mem_empty_eq x at rid, exact rid, },
  { obtain ⟨n, hn⟩ := ih,
    have : ∃ (m : ℕ) (x : R), a = localization.mk x ⟨f^m, ⟨m, rfl⟩⟩,
    { induction a using localization.induction_on with data,
      obtain ⟨a, ⟨b, ⟨m, rfl⟩⟩⟩ := data,
      refine ⟨m, a, _⟩, refl, },
    obtain ⟨m, x, rfl⟩ := this,
    refine ⟨n + m, λ y hy, _⟩,
    rw finset.mem_insert at hy,
    rcases hy,
    { erw [hy, localization.mk_mul],
      have : (localization.mk (x * f ^ (n + m)) (⟨f ^ m, _⟩ * 1) : localization.away f) =
        localization.mk (x * f ^ n) 1,
      { rw [localization.mk_eq_mk', is_localization.eq], use 1,
        erw [mul_one, mul_one, mul_one, mul_one, pow_add, mul_assoc],
        refl },
      erw [this, set.mem_image],
      refine ⟨_, set.mem_univ _, rfl⟩, },
    { specialize hn y hy,
      erw set.mem_image at hn,
      obtain ⟨y', _, eq1⟩ := hn,
      have : (localization.mk (f ^ (n + m)) 1 : localization.away f) =
        localization.mk (f ^ n) 1 * localization.mk (f^m) 1,
      { rw [localization.mk_mul], congr, rw pow_add, rw mul_one, },
      erw [this, ←mul_assoc, ←eq1, localization.mk_mul, mul_one],
      refine ⟨_, set.mem_univ _, rfl⟩, } }
end

lemma localization.mk_pow (m n : ℕ) (hm : 0 < m) (α : R) :
  (localization.mk α ⟨f^n, ⟨n, rfl⟩⟩ : localization.away f)^m
  = (localization.mk (α ^ m) ⟨f^(m * n), ⟨_, rfl⟩⟩) :=
begin
  induction m with m ih,
  { exfalso, apply lt_irrefl 0 hm, },
  { by_cases ineq : m = 0,
    { rw [ineq, pow_one, pow_one, one_mul], },
    { replace ineq : 0 < m,
      { by_contra,
        rw not_lt at h,
        have ineq2 := lt_of_le_of_ne h ineq,
        linarith, },
      { specialize ih ineq,
        rw [pow_succ, ih, pow_succ, nat.succ_mul, localization.mk_mul],
        congr',

        rw [subtype.ext_iff_val, show ∀ (a b : submonoid.powers f), (a * b).1 = a.1 * b.1,
          from λ _ _, rfl],
        dsimp only,
        rw [mul_comm, pow_add], }, }, },
end

end clear_denominator


section homogeneous_induction

variables {ι R A: Type*} [linear_ordered_cancel_add_comm_monoid ι]
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variable [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)]

@[elab_as_eliminator]
lemma set_like.homogeneous_induction {P : A → Prop}
  (a : A)
  (h_zero : P 0)
  (h_hom : ∀ (a : set_like.homogeneous_submonoid 𝒜), P a.1)
  (h_add : ∀ (a b : A), P a → P b → P (a + b))
  : P a :=
begin
  erw ←graded_algebra.sum_support_decompose 𝒜 a,
  suffices : ∀ (i : graded_algebra.support 𝒜 a), P (graded_algebra.decompose 𝒜 a i.1 : A),
  { induction (graded_algebra.support 𝒜 a) using finset.induction_on with x s hx ih,
    erw finset.sum_empty, exact h_zero,

    erw finset.sum_insert hx, apply h_add _ _ _ ih,
    refine h_hom ⟨(graded_algebra.decompose 𝒜 a x), ⟨x, submodule.coe_mem _⟩⟩, },

  rintros ⟨i, hi⟩,
  refine h_hom ⟨(graded_algebra.decompose 𝒜 a i), ⟨i, submodule.coe_mem _⟩⟩,
end


end homogeneous_induction


section mem_span

universe u
variables (R : Type u) [comm_ring R]

lemma ideal.mem_span.smul_mem (s : set R) (r a : R) (ha : a ∈ s) : r • a ∈ ideal.span s :=
begin
  rw ideal.mem_span,
  intros J hs,
  apply ideal.mul_mem_left,
  exact hs ha,
end

end mem_span

section

variables {R A: Type*}
variables [comm_ring R] [comm_ring A] [algebra R A] [nontrivial A]

variables (𝒜 : ℕ → submodule R A)
variables [graded_algebra 𝒜] [Π (i : ℕ) (x : 𝒜 i), decidable (x ≠ 0)]

lemma graded_algebra.proj_hom_mul (a b : A) (i j : ℕ) (a_hom : a ∈ 𝒜 i)
  (hb : graded_algebra.proj 𝒜 j b ≠ 0) :
  graded_algebra.proj 𝒜 (i + j) (a * b) = a * graded_algebra.proj 𝒜 j b :=
begin
  by_cases INEQ : a = 0,
  rw [INEQ, zero_mul, zero_mul, linear_map.map_zero],

  rw [graded_algebra.proj_apply, alg_equiv.map_mul, direct_sum.coe_mul_apply_submodule 𝒜,
    ←graded_algebra.support, ←graded_algebra.support],

  have set_eq1 : graded_algebra.support 𝒜 a = {i},
    { ext1, split; intros hx,
      { erw graded_algebra.mem_support_iff at hx,
        erw finset.mem_singleton,
        contrapose hx,
        erw [not_not, graded_algebra.proj_apply, graded_algebra.decompose_of_mem_ne],
        exact a_hom,
        symmetry,
        exact hx, },
      { rw finset.mem_singleton at hx,
        rw [hx, graded_algebra.mem_support_iff, graded_algebra.proj_apply,
          graded_algebra.decompose_of_mem_same],
        exact INEQ,
        exact a_hom, }, },
    erw [set_eq1],
    have set_eq2 : finset.filter
          (λ z : ℕ × ℕ, z.1 + z.2 = i + j)
          (finset.product
            {i}
            (graded_algebra.support 𝒜 b)) =
      {(i, j)},
    { ext1 x, rcases x with ⟨n1, n2⟩,
      split; intros ha,
      { erw finset.mem_filter at ha,
        rcases ha with ⟨ha1, ha3⟩,
        erw finset.mem_product at ha1,
        rcases ha1 with ⟨ha1, ha2⟩,
        dsimp only at ha1 ha2 ha3,
        erw finset.mem_singleton at ha1,
        erw finset.mem_singleton,
        ext; dsimp only,
        { exact ha1, },
        { erw ha1 at ha3,
          linarith, }, },
      { erw [finset.mem_singleton, prod.ext_iff] at ha,
        rcases ha with ⟨ha1, ha2⟩,
        dsimp only at ha1 ha2,
        erw [ha1, ha2, finset.mem_filter, finset.mem_product, finset.mem_singleton],
        refine ⟨⟨rfl, _⟩, rfl⟩,
        dsimp only,
        erw graded_algebra.mem_support_iff,
        exact hb, }, },
    erw [set_eq2, finset.sum_singleton],
    dsimp only,
    erw [graded_algebra.decompose_of_mem_same 𝒜, ←graded_algebra.proj_apply],
    exact a_hom,
end

end
