FAIL
import Mathlib

variable {R A : Type*}

theorem inl_mul_inr [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
    (a : A) : ((Unitization.inl r : Unitization R A) * a) = ↑(r • a) := by
  rfl
