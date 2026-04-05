import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inr_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂ := Unitization.ext (add_zero 0).symm rfl

