import Mathlib

variable {α β : Type u}

theorem pure_bind (f : α → FreeMagma β) (x) : pure x >>= f = f x := rfl

