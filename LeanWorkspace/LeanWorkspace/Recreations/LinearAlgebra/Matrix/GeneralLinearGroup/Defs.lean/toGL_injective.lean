import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {S : Type*} [CommRing S] [Algebra R S]

theorem toGL_injective :
    Function.Injective (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup n R → GL n R) := fun g g' ↦ by
  simpa [Matrix.SpecialLinearGroup.toGL] using fun h _ ↦ Subtype.ext h

