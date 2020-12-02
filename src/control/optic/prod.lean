/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import control.optic.profunctor_optic
/-!
Some definitions for optics on products.
-/

universes u v
variables {A B C D S T X Y : Type}

/-- `square A := A × A` -/
def prod.square (A : Type u) := A × A

namespace prod.square

open prod

instance : functor square := {map := λ A B f, prod.map f f}

instance [has_repr A] : has_repr (square A) := prod.has_repr

def traverse {M} [applicative M] {A B : Type} (f : A → M B) : square A → M (square B)
| (a₁, a₂) := pure prod.mk <*> f a₁ <*> f a₂

instance is_trav : traversable square :=
{ traverse := @traverse }

end prod.square

namespace control.optic

open control.profunctor

def zip_with2 : grate A B S T → (A → A → B) → S → S → T
| g p s₁ s₂ := @g (costar prod.square) _ _ (λ ⟨a₁, a₂⟩, p a₁ a₂) (s₁, s₂)

def both : traversal A B (A × A) (B × B) :=
@control.optic.traversal.traversed prod.square prod.square.is_trav A B

def fst : lens A B (A × C) (B × C) :=
begin intros P pf st x, unfreezingI {apply strong.first, apply x}  end

def snd : lens A B (C × A) (C × B) :=
begin intros P pf st x, unfreezingI {apply strong.second, apply x}  end

end control.optic
