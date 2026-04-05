import Mathlib

open scoped Pointwise

variable {R M : Type*}

variable [NonUnitalNonAssocRing R]

theorem mul_toAddSubmonoid (M N : AddSubgroup R) :
    (M * N).toAddSubmonoid = M.toAddSubmonoid * N.toAddSubmonoid := rfl

