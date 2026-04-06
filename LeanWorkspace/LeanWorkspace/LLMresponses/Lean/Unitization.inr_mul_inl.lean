FAIL
import Mathlib

variable {R A : Type*}

theorem inr_mul_inl [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
    (a : A) : a * (Unitization.inl r : Unitization R A) = ↑(r • a) := by
  simpa [Unitization.inl, Unitization.mul, AddMonoidAlgebra.single, Finsupp.single, one_mul] using
    Unitization.inr_mul_inl (R := R) (A := A) a r
