import Mathlib

variable {R : Type u}

theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocCommRing R] [NoZeroDivisors R] {a b : R} :
    a * a = b * b ↔ a = b ∨ a = -b := Commute.mul_self_eq_mul_self_iff (Commute.all a b)

