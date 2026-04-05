import Mathlib

variable {G : Type*}

variable [Semigroup G]

theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) := Semigroup.mul_assoc

