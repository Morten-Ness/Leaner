import Mathlib

variable {R A : Type*}

theorem inr_mul_inl [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
    (a : A) : a * (Unitization.inl r : Unitization R A) = ↑(r • a) := Unitization.ext (zero_mul r) <| by simp

