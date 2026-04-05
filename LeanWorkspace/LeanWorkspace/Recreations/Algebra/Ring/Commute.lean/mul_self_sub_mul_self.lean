import Mathlib

variable {R : Type u}

theorem mul_self_sub_mul_self [NonUnitalNonAssocCommRing R] (a b : R) :
    a * a - b * b = (a + b) * (a - b) := Commute.mul_self_sub_mul_self_eq (Commute.all a b)

