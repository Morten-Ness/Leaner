import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LT α]

theorem mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (bc : b < c)
    (a : α) :
    b * a < c * a := i.elim a bc

