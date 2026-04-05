import Mathlib

variable {α : Type u}

variable {β : Type u}

theorem pure_bind (f : α → FreeSemigroup β) (x) : pure x >>= f = f x := rfl

