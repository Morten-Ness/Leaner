import Mathlib

variable {α : Type u}

theorem «exists» {p : WithOne α → Prop} : (∃ x, p x) ↔ p 1 ∨ ∃ a : α, p a := Option.exists

