import Mathlib

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem mul_right_inj_of_invertible : c * a = c * b ↔ a = b := ⟨fun h => by simpa using congr_arg (⅟c * ·) h, congr_arg (_ * ·)⟩

