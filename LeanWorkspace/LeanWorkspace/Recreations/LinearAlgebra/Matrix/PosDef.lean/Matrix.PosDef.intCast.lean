import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem intCast [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : ℤ) (hd : 0 < d) :
    Matrix.PosDef (d : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun _ ↦ by simpa [pos_iff_ne_zero]

