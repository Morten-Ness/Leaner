import Mathlib

variable {C ι J : Type*} [Category* C] [Category* J] {c : ComplexShape ι} [HasZeroMorphisms C]

theorem preservesLimitsOfShape_of_eval {D : Type*} [Category* D]
    (G : D ⥤ HomologicalComplex C c)
    (_ : ∀ (i : ι), PreservesLimitsOfShape J (G ⋙ eval C c i)) :
    PreservesLimitsOfShape J G := ⟨fun {_} => ⟨fun hs ↦ ⟨HomologicalComplex.isLimitOfEval _ _
    (fun i => isLimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩⟩

