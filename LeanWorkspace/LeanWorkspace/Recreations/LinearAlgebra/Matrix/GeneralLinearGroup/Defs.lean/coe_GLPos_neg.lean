import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n]
  {R : Type v} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

variable [Fact (Even (Fintype.card n))]

theorem coe_GLPos_neg (g : Matrix.SpecialLinearGroup n R) : ↑(-g) = -(↑g : Matrix.GLPos n R) := Subtype.ext <| Units.ext rfl

