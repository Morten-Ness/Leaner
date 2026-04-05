import Mathlib

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

theorem mem_torsionOf_iff (x : M) (a : R) : a ∈ Ideal.torsionOf R M x ↔ a • x = 0 := Iff.rfl

