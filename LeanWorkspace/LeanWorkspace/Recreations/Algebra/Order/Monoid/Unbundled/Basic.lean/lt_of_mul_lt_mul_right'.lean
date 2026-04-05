import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LT α]

theorem lt_of_mul_lt_mul_right' [i : MulRightReflectLT α] {a b c : α}
    (bc : b * a < c * a) :
    b < c := i.elim a bc

