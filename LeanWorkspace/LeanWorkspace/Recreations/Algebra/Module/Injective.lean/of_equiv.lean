import Mathlib

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

theorem of_equiv (e : Q ≃ₗ[R] M) (h : Module.Baer R Q) : Module.Baer R M := fun I g ↦
  have ⟨g', h'⟩ := h I (e.symm ∘ₗ g)
  ⟨e ∘ₗ g', by simpa [LinearEquiv.eq_symm_apply] using h'⟩

