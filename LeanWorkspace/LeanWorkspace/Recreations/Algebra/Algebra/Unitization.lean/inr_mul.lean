import Mathlib

variable {R A : Type*}

theorem inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [SMulWithZero R A] (a₁ a₂ : A) :
    (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂ := Unitization.ext (mul_zero _).symm <| by simp

