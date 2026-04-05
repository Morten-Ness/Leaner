import Mathlib

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

theorem homologyFunctor_inverts_quasiIso (i : ι) :
    (HomotopyCategory.quasiIso C c).IsInvertedBy (HomologicalComplexUpToQuasiIso.homologyFunctor C c i) := fun _ _ _ hf => hf i

