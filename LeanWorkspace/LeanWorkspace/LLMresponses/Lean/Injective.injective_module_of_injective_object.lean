import Mathlib

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

theorem injective_module_of_injective_object
    [inj : CategoryTheory.Injective <| ModuleCat.of R M] :
    Module.Injective R M := by
  rw [Module.injective_iff_injective_object]
  infer_instance
