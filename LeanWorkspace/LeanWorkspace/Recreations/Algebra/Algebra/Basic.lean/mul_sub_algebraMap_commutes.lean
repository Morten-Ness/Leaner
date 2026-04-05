import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

theorem mul_sub_algebraMap_commutes [Ring A] [Algebra R A] (x : A) (r : R) :
    x * (x - algebraMap R A r) = (x - algebraMap R A r) * x := by rw [mul_sub, ← commutes, sub_mul]

