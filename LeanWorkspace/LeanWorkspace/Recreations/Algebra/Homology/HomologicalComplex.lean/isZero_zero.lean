import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem isZero_zero [HasZeroObject V] : IsZero (HomologicalComplex.zero : HomologicalComplex V c) := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  all_goals
    ext
    dsimp only [HomologicalComplex.zero]
    subsingleton

