import Mathlib

variable {R : Type u} [CommRing R]

variable {n : Type v} [DecidableEq n] [Fintype n]

variable {N : Type w} [AddCommGroup N] [Module R N]

theorem minpoly_toMatrix' (f : (n → R) →ₗ[R] n → R) : minpoly R (toMatrix' f) = minpoly R f := minpoly.algEquiv_eq (toMatrixAlgEquiv' : _ ≃ₐ[R] Matrix n n R) f

