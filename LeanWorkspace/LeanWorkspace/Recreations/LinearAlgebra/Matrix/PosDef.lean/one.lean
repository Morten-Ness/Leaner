import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem one [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R] :
    Matrix.PosDef (1 : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun i ↦ zero_lt_one' R

