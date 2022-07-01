import tactic.group

variables {G : Type} [group G]

example (a b c d : G) : c *(a*b)*(b⁻¹*a⁻¹)*c = c*c :=
by group

example (a b c d : G) : (b*c⁻¹)*c *(a*b)*(b⁻¹*a⁻¹)*c = b*c :=
by group

example (a b c d : G) : c⁻¹*(b*c⁻¹)*c *(a*b)*(b⁻¹*a⁻¹*b⁻¹)*c = 1 :=
by group

-- The following is known as the Hall-Witt identity,
-- see e.g.
-- https://en.wikipedia.org/wiki/Three_subgroups_lemma#Proof_and_the_Hall%E2%80%93Witt_identity
example (g h k : G) :
  g * ⁅⁅g⁻¹, h⁆, k⁆ * g⁻¹ * k * ⁅⁅k⁻¹, g⁆, h⁆ * k⁻¹ * h *⁅⁅h⁻¹, k⁆, g⁆ * h⁻¹ = 1 :=
by group

example (a : G) : a^2*a = a^3 :=
by group

example (n m : ℕ) (a : G) : a^n*a^m = a^(n+m) :=
by group

example (a b c d : G) : c *(a*b^2)*((b*b)⁻¹*a⁻¹)*c = c*c :=
by group

example (n m : ℕ) (a : G) : a^n*(a⁻¹)^n = 1 :=
by group

example (n m : ℕ) (a : G) : a^2*a⁻¹*a⁻¹ = 1 :=
by group

example (n m : ℕ) (a : G) : a^n*a^m = a^(m+n) :=
by group

example (n : ℕ) (a : G) : a^(n-n) = 1 :=
by group

example (n : ℤ) (a : G) : a^(n-n) = 1 :=
by group

example (n : ℤ) (a : G) (h : a^(n*(n+1)-n -n^2) = a) : a = 1 :=
begin
 group at h,
 exact h.symm,
 end

example (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a :=
begin
  group at h,
  rw h,
  group,
end

-- The next example can be expand to require an arbitrarily high number of alternation
-- between simp and ring

example (n m : ℤ) (a b : G) : a^n*b^n*a^n*a^n*a^-n*a^-n*b^-n*a^-n = 1 :=
by group

-- Test that group deals with `1⁻¹` properly

example (x y : G) : (x⁻¹ * (x * y) * y⁻¹)⁻¹ = 1 :=
by group

example (x : G) (h : x = 1) : x = 1 :=
begin
  group,
  exact h,
end
