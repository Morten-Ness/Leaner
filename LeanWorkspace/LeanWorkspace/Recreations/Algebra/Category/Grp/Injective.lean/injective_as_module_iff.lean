import Mathlib

variable (A : Type u) [AddCommGroup A]

theorem injective_as_module_iff : Function.Injective (ModuleCat.of ℤ A) ↔
    Function.Injective (C := AddCommGrpCat) (AddCommGrpCat.of A) :=
  ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.map_injective_iff (ModuleCat.of ℤ A)).symm

