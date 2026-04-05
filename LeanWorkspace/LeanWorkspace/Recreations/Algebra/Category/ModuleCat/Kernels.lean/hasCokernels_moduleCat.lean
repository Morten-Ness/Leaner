import Mathlib

variable {R : Type u} [Ring R]

theorem hasCokernels_moduleCat : HasCokernels (ModuleCat R) := ⟨fun f => HasColimit.mk ⟨_, ModuleCat.cokernelIsColimit f⟩⟩

