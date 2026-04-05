import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i ↔
      ShortComplex.QuasiIso ((shortComplexFunctor C c i).map f) := by
  constructor
  · intro h
    exact h.quasiIso
  · intro h
    exact ⟨h⟩

