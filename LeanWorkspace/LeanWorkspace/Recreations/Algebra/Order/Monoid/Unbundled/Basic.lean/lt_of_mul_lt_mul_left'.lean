import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LT α]

theorem lt_of_mul_lt_mul_left' [MulLeftReflectLT α] {a b c : α}
    (bc : a * b < a * c) :
    b < c := ContravariantClass.elim _ bc

