import Mathlib

variable {α : Type u}

theorem invOf_inj [Monoid α] {a b : α} [Invertible a] [Invertible b] : ⅟a = ⅟b ↔ a = b := ⟨invertible_unique _ _, invertible_unique _ _⟩

