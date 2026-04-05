import Mathlib

variable {R : Type max u v} [CommRing R] {D : Type v} [SmallCategory D]

theorem hasColimitDiagram (I : D ⥤ Ideal R) (i : ℕ) :
    HasColimit (localCohomology.diagram I i) := inferInstance

