import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LE α]

theorem le_of_mul_le_mul_right' [i : MulRightReflectLE α] {a b c : α}
    (bc : b * a ≤ c * a) :
    b ≤ c := i.elim a bc

