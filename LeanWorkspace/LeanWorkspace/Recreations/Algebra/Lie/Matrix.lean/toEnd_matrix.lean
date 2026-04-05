import Mathlib

open scoped Matrix

variable {R : Type u} [CommRing R]

variable {n : Type w} [DecidableEq n] [Fintype n]

theorem toEnd_matrix :
    toEnd R (Matrix n n R) (n → R) = (lieEquivMatrix' (R := R) (n := n)).symm := by
  ext; simp

