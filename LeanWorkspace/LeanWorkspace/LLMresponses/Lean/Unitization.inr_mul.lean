FAIL
import Mathlib

variable {R A : Type*}

theorem inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [SMulWithZero R A] (a₁ a₂ : A) :
    (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂ := by
  ext <;> simp [Unitization.mul_coe, add_comm, add_left_comm, add_assoc]
