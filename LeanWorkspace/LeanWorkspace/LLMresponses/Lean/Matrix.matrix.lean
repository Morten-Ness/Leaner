FAIL
import Mathlib

open scoped TensorProduct

variable (R n : Type*) [CommSemiring R] [Fintype n] [DecidableEq n]

theorem matrix [Nonempty n] : IsAzumaya R (Matrix n n R) where
  bij := by
    simpa using (isAzumaya_matrix (R := R) (n := n)).bij
  eq_of_smul_eq_smul := by
    intro a b h
    simpa using h 1
