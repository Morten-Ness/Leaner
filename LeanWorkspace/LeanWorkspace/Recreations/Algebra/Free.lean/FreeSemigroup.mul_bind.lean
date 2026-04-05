import Mathlib

variable {α : Type u}

variable {β : Type u}

theorem mul_bind (f : α → FreeSemigroup β) (x y : FreeSemigroup α) :
    x * y >>= f = (x >>= f) * (y >>= f) := map_mul (FreeSemigroup.lift f) _ _

