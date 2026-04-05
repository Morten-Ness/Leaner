import Mathlib

variable {R : Type u} [Ring R]

theorem hasKernels_moduleCat : HasKernels (ModuleCat R) := ⟨fun f => HasLimit.mk ⟨_, ModuleCat.kernelIsLimit f⟩⟩

