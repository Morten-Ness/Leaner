import Mathlib

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

theorem torsionOf_zero : Ideal.torsionOf R M (0 : M) = ⊤ := by simp [Ideal.torsionOf]

