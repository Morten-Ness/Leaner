import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LT α]

theorem mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc : b < c) (a : α) :
    a * b < a * c := CovariantClass.elim _ bc

