import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

variable {C c} [CategoryWithHomology C]

theorem mem_quasiIso_iff (f : K ⟶ L) : HomologicalComplex.quasiIso C c f ↔ QuasiIso f := by rfl

