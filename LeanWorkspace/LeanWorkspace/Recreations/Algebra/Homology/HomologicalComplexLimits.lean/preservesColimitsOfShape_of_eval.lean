import Mathlib

variable {C ι J : Type*} [Category* C] [Category* J] {c : ComplexShape ι} [HasZeroMorphisms C]

theorem preservesColimitsOfShape_of_eval {D : Type*} [Category* D]
    (G : D ⥤ HomologicalComplex C c)
    (_ : ∀ (i : ι), PreservesColimitsOfShape J (G ⋙ eval C c i)) :
    PreservesColimitsOfShape J G := ⟨fun {_} => ⟨fun hs ↦ ⟨HomologicalComplex.isColimitOfEval _ _
    (fun i => isColimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩⟩

