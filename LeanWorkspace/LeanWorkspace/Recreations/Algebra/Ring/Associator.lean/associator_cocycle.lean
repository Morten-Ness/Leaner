import Mathlib

variable {R : Type*}

variable [NonUnitalNonAssocRing R]

theorem associator_cocycle (a b c d : R) :
    a * associator b c d - associator (a * b) c d + associator a (b * c) d - associator a b (c * d)
    + (associator a b c) * d = 0 := by
  simp only [associator, mul_sub, sub_mul]
  abel1

