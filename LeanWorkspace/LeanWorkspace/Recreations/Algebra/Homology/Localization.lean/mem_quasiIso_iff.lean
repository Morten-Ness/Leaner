import Mathlib

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

theorem mem_quasiIso_iff {X Y : HomotopyCategory C c} (f : X ⟶ Y) :
    HomotopyCategory.quasiIso C c f ↔ ∀ (n : ι), IsIso ((HomologicalComplexUpToQuasiIso.homologyFunctor _ _ n).map f) := by
  rfl

