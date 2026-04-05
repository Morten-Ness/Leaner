import Mathlib

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [Fact (Even (Fintype.card n))]

theorem GLPos.coe_neg (g : Matrix.GLPos n R) : (↑(-g) : GL n R) = -((g : GL n R) : Matrix n n R) := rfl

