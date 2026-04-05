import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem _root_.Matrix.posDef_diagonal_iff
    [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R] [Nontrivial R] {d : n → R} :
    Matrix.PosDef (Matrix.PosDef.diagonal d) ↔ ∀ i, 0 < d i := ⟨fun h i => by simpa using h.2 (x := .single i 1), .diagonal⟩

