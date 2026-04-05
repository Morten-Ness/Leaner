import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*} [DecidableEq n] [Fintype n]

theorem Matrix.isUnit_toLin'_iff {M : Matrix n n R} : IsUnit M.toLin' ↔ IsUnit M := isUnit_map_iff LinearMap.toMatrixAlgEquiv'.symm M

