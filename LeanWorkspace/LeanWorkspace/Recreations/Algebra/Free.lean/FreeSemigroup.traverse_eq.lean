import Mathlib

variable {α : Type u}

variable {β : Type u}

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

theorem traverse_eq (x) : FreeSemigroup.traverse F x = traverse F x := rfl

