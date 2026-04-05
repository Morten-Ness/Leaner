import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*} [DecidableEq n] [Fintype n]

theorem LinearMap.isUnit_toMatrix'_iff {f : (n → R) →ₗ[R] n → R} : IsUnit f.toMatrix' ↔ IsUnit f := isUnit_map_iff LinearMap.toMatrixAlgEquiv' f

