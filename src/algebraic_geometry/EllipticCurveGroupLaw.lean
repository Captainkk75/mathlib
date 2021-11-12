import algebraic_geometry.EllipticCurve
import tactic
--import algebra.field_power

example (K : Type) [field K] (x : K) (hx : x ≠ 0) : x * (1/x) = 1 := mul_div_cancel' 1 hx

namespace EllipticCurve

variables {K : Type*} [field K] (E : EllipticCurve K)
/-

# Elliptic curves over fields.

-/

/-

## Points on the elliptic curve `[a₁,a₂,a₃,a₄,a₆]`

`K` is a field throughout, and `E` is an elliptic curve over `K`.

The affine curve we're thinking about is `y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆`. But the
curve itself is a smooth projective curve, cut out as a subspace of `ℙ²` by
the projectve cubic `Y²Z+a₁XYZ+a₃YZ³=X³+a₂X²Z+a₄XZ²+a₆Z³`, with the affine
solution `(x,y) := (t,s) : K²` corresponding to the projective point
`[X:Y:Z] := [t:s:1] : ℙ²(K)`. To analyse what is happening at infinity
one sets `Z=0`; the line at infinity is then `[*:*:0]`,
and the projective curve meets this line at the solutions to `X³=0`,
which is the point `[0:1:0]` with multiplicity 3.

-/
inductive points (E : EllipticCurve K)
| zero : points -- the so-called "point at infinity".
| some (x y : K) (h : y^2+E.a1*x*y+E.a3*y=x^3+E.a2*x^2+E.a4*x+E.a6) : points

open points

variable {E}

-- use `0` to mean `zero`
instance : has_zero (points E) := ⟨zero⟩

/--

## Lines through infinity.

The line at infinity `[*:*:0]` is the complement of the affine piece `[*:*:1]`.
The lines through the point at infinity `[0:1:0]` correspond to the points on
the line `B=0` in the dual `[A:B:C]` plane. The points in that line are the `[A:0:C]`
with `[A:C]` in projective 1-space, and are hence either `[0:0:1]` or of the
form `[1:0:t]` for some `t` in the field. Hence the lines through the point at
infinity are the line at infinity, and the lines corresponding to the vertical
lines `x=t` as `t` varies.

## Consequences for the group law.

`P + Q = 0 ↔ Q = -P`. Two points sum to zero iff the line through them
goes through the point at infinity. This means that the generic affine
point `P=(t,s)` will have negative `-P=(t,s')`, where `s` and `s'` are the
two roots of `y^2+a₁ty+a₃y-f(t)=0` for `f(x)=x³+a₂x^2+a₄x+a₆`. This
means that `s+s'=-(a₁t+a₃)` and one can then solve for `s'`. Using the
language of algebraic geometry one can make this statement precise in
cases where the roots coincide.

-/

def neg : points E → points E
| zero := zero
| (some t s h) := some t (-E.a3 - E.a1 * t - s) begin
  rw ← h,
  ring,
end

instance : has_neg (points E) := ⟨EllipticCurve.neg⟩

theorem neg_neg : ∀ P : points E, - -P = P
| zero := rfl
| (some x y h) := by simp [has_neg.neg, neg]

/-
Addition needs to split on equality in ℙ²(K) if we work with affine coordinates
-/

variable [decidable_eq K]

/-

## Elliptic curve addition

The point at infinity is the identity. The interesting question
is adding two finite points `P₁=(t₁,s₁)` and `P₂=(t₂,s₂)`.

We first deal with the case `t₁=t₂=t`. Then s₁ and s₂ are the two
roots of a monic quadratic, so either their sum is `-(a₁t+a₃)` or they
are not the two distinct roots of this quadratic and hence must coincide.

If `s₁+s₂=-(a₁t+a₃)` then `P₁+P₂=∞` because `P₂=-P₁`.

The remaining `t₁=t₂=t` case is when `s₁=s₂=s`. The tangent
`y=lx+m` to the curve at `(t,s)` cuts the curve at `(t,s)` with multiplicity
2 (generically); let `P₃=(t₃,s₃)` be the third point of intersection.
Differentiating the cubic wrt `x` and substituting in `l` for `dy/dx` we get
deduce `2yl+a₁xl+a₃l=3x²+2a₂x+a₄`. Recall that we are assuming that
`2s≠-(a₁t+a₃)` and so `l=(3t²+2a₂t+a₄)/(2s+a₁t+a₃)` and `m=s-lt`.
Letting the third point of intersection be `(t₃,s₃)` as before,
we see `t₃:=l²+a₁l+a₃-2t` and then `s₃=lt₃+m`.

Now we deal with `t₁≠t₂`. The line joining the two points is `y=lx+m`
where `l=(s₁-s₂)/(t₁-t₂)` and `m` is some mess. The
line cuts the curve `P₁`, `P₂` and `P₃:=-(P₁+P₂) =:(t₃,s₃)`. Eliminating
`y` we see that the `tᵢ` are the three roots of
`(lx+m)²+a₁x(lx+m)+a₃(lx+m)=x³+a₂x²+a₄x+a₆`, and hence their
sum can be computed to be by `l²+a₁l+a₃` (consider the coefficients of `x²`
in the equation). Hence `t₃:=l²+a₁l+a₃-t₁-t₂` and the simplest way to
compute `s₃` is that it's equal to `lt₃+m` where
`m=s₁-lt₁=s₂-lt₂=(s₁t₂+s₂t₁)/(t₁-t₂)`; now apply `neg`.

-/

lemma pow_three {M : Type*} [monoid M] (m : M) : m^3=m*m*m := by {rw [pow_succ, pow_succ, pow_one, mul_assoc] }

protected def add : points E → points E → points E
| zero           zero           := zero
| zero           (some x y h)   := some x y h
| (some x y h)   zero           := some x y h
| (some t₁ s₁ h₁) (some t₂ s₂ h₂) :=
if h : (t₁ = t₂) then
  --  `P₁=±P₂`. Let's deal with `P₁=-P₂` first
  if h' : s₁ + s₂ + E.a1 * t₁ + E.a3 = 0 then zero
  -- `P₁=P₂` -- we use variables s₁ and t₁ and can prove s₁=s₂
  else let l := (3*t₁*t₁+2*E.a2*t₁+E.a4)/(2*s₁+E.a1*t₁+E.a3) in
       let m := s₁-l*t₁ in
       let t₃ := l^2+E.a1*l+E.a3-2*t₁ in
  some t₃ (l*t₃+m) begin
    subst h,
    rename t₁ t,
    -- prove that s₁ = s₂ using h₁ and h₂ and also h'
    have hs : s₁ = s₂,
    { rw [← h₂,← sub_eq_zero,
        show s₁ ^ 2 + E.a1 * t * s₁ + E.a3 * s₁ - (s₂ ^ 2 + E.a1 * t * s₂ + E.a3 * s₂) =
        (s₁-s₂)*((s₁+s₂)+E.a1*t+E.a3), by ring,
      mul_eq_zero, sub_eq_zero] at h₁,
      cases h₁, assumption, contradiction },
    subst hs,
    rename s₁ s,
    rw ← two_mul at h', -- s+s -> 2s because that's the denominator.
    change 2 * s + E.a1 * t + E.a3 ≠ 0 at h',
    -- these lines are long and manually undo the `let`s other than `u`, which stays for now.
    set u : units K := ⟨2*s+E.a1*t+E.a3,1/(2*s+E.a1*t+E.a3), mul_div_cancel' 1 h', div_mul_cancel _ h'⟩ with hu,
    change (((3 * t * t + 2 * E.a2 * t + E.a4) / u) * (((3 * t * t + 2 * E.a2 * t + E.a4) / u) ^ 2 + E.a1 * ((3 * t * t + 2 * E.a2 * t + E.a4) / u) + E.a3 - 2 * t) + (s - ((3 * t * t + 2 * E.a2 * t + E.a4) / u) * t)) ^ 2 + E.a1 * (((3 * t * t + 2 * E.a2 * t + E.a4) / u) ^ 2 + E.a1 * ((3 * t * t + 2 * E.a2 * t + E.a4) / u) + E.a3 - 2 * t) * (((3 * t * t + 2 * E.a2 * t + E.a4) / u) * (((3 * t * t + 2 * E.a2 * t + E.a4) / u) ^ 2 + E.a1 * ((3 * t * t + 2 * E.a2 * t + E.a4) / u) + E.a3 - 2 * t) + (s - ((3 * t * t + 2 * E.a2 * t + E.a4) / u) * t)) + E.a3 * (((3 * t * t + 2 * E.a2 * t + E.a4) / u) * (((3 * t * t + 2 * E.a2 * t + E.a4) / u) ^ 2 + E.a1 * ((3 * t * t + 2 * E.a2 * t + E.a4) / u) + E.a3 - 2 * t) + (s - ((3 * t * t + 2 * E.a2 * t + E.a4) / u) * t)) =
  (((3 * t * t + 2 * E.a2 * t + E.a4) / u) ^ 2 + E.a1 * ((3 * t * t + 2 * E.a2 * t + E.a4) / u) + E.a3 - 2 * t) ^ 3 + E.a2 * (((3 * t * t + 2 * E.a2 * t + E.a4) / u) ^ 2 + E.a1 * ((3 * t * t + 2 * E.a2 * t + E.a4) / u) + E.a3 - 2 * t) ^ 2 + E.a4 * (((3 * t * t + 2 * E.a2 * t + E.a4) / u) ^ 2 + E.a1 * ((3 * t * t + 2 * E.a2 * t + E.a4) / u) + E.a3 - 2 * t) + E.a6
    ,
    simp only [pow_two, pow_three],
    field_simp [h'], -- I think this tactic is extremely wayward with the denominators here?
    -- it's also a shame `u` got unfolded, it's the only thing we ever divide by
    -- we now need to use h₁
    rw ← sub_eq_zero,
    -- next job: divide LHS of current `<huge>=0` goal by `(s ^ 2 + E.a1 * t * s + E.a3 * s - (t ^ 3 + E.a2 * t ^ 2 + E.a4 * t + E.a6)) `
    -- in a computer algebra package; it should divide exactly! Say the quotient is q.
    let q := s + 37*t, -- probably not right but I don't have a computer algebra package which can do this
    suffices : (s ^ 2 + E.a1 * t * s + E.a3 * s - (t ^ 3 + E.a2 * t ^ 2 + E.a4 * t + E.a6)) * q = 0,
    { rw ← this,
      sorry }, -- will be `ring` when we've got `q` right -- if `ring` can handle it
    rw [h₁, sub_self, zero_mul],
  end
else let l :=(s₁-s₂)/(t₁-t₂) in
     let m := (s₁*t₂+s₂*t₁)/(t₁-t₂) in
     let t₃ :=l*l+E.a1*l+E.a3-t₁-t₂ in
     let s₃ := l*t₃+m in
     -(some t₃ s₃ sorry) -- level 2; add

instance : has_add (points E) := ⟨EllipticCurve.add⟩

@[simp] lemma tell_simplifier_to_use_numerals : (zero : points E) = 0 := rfl
@[simp] lemma add_zero (P : points E) : P + 0 = P := by {cases P; refl }
@[simp] lemma zero_add (P : points E) : 0 + P = P := by {cases P; refl }

lemma add_assoc : ∀ {P Q R : points E}, P + Q + R = P + (Q + R)
| zero           zero           zero           := rfl
| (some a b hab) zero           zero           := rfl
| zero           (some c d hcd) zero           := rfl
| zero           zero           (some e f hef) := rfl
| (some a b hab) (some c d hcd) zero           := by simp
| (some a b hab) zero           (some e f hef) := rfl
| zero           (some c d hcd) (some e f hef) := by simp
| (some a b hab) (some c d hcd) (some e f hef) := sorry -- boss level; add_assoc

end EllipticCurve
