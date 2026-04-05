import Mathlib

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

theorem ExtensionOf.toLinearPMap_injective :
    Function.Injective (α := ExtensionOf i f) ExtensionOf.toLinearPMap :=
  fun _ _ _ ↦ by ext <;> Module.Baer.congr!

