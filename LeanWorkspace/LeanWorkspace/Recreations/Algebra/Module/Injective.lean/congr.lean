import Mathlib

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

theorem congr (e : Q ≃ₗ[R] M) : Module.Baer R Q ↔ Module.Baer R M := ⟨Module.Baer.of_equiv e, Module.Baer.of_equiv e.symm⟩

