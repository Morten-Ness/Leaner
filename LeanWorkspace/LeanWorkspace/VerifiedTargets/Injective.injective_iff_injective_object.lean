import Mathlib

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

theorem injective_iff_injective_object :
    Module.Injective R M ↔
    CategoryTheory.Injective (ModuleCat.of R M) := ⟨fun _ => Module.injective_object_of_injective_module R M,
   fun _ => Module.injective_module_of_injective_object R M⟩

