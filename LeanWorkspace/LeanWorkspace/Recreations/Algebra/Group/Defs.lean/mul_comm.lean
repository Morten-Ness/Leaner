import Mathlib

variable {G : Type*}

variable [CommMagma G] {a : G}

theorem mul_comm : ∀ a b : G, a * b = b * a := CommMagma.mul_comm

