import Mathlib

variable {F α β : Type*}

theorem IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a → IsSquare b → IsSquare (a * b) := fun ⟨r, _⟩ ⟨s, _⟩ => ⟨r * s, by simp_all [mul_mul_mul_comm]⟩

