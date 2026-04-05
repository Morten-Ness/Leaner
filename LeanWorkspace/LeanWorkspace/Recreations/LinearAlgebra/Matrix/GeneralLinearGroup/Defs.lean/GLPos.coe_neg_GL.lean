import Mathlib

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [Fact (Even (Fintype.card n))]

theorem GLPos.coe_neg_GL (g : Matrix.GLPos n R) : ↑(-g) = -(g : GL n R) := rfl

