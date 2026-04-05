import Mathlib

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem mul_left_inj_of_invertible : a * c = b * c ↔ a = b := ⟨fun h => by simpa using congr_arg (· * ⅟c) h, congr_arg (· * _)⟩

