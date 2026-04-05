import Mathlib

variable {α β : Type u}

theorem mul_bind (f : α → FreeMagma β) (x y : FreeMagma α) : x * y >>= f = (x >>= f) * (y >>= f) := rfl

