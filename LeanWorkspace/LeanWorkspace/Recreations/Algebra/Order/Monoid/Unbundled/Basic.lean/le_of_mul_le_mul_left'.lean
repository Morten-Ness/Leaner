import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LE α]

theorem le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b c : α}
    (bc : a * b ≤ a * c) :
    b ≤ c := ContravariantClass.elim _ bc

