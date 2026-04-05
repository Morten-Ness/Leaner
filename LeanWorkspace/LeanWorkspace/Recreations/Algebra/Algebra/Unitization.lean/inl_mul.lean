import Mathlib

variable {R A : Type*}

theorem inl_mul [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ : R) :
    (Unitization.inl (r₁ * r₂) : Unitization R A) = Unitization.inl r₁ * Unitization.inl r₂ := Unitization.ext rfl <| by simp

