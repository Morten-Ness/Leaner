import Mathlib

variable {R : Type u} [CommRing R]

variable {n : Type v} [DecidableEq n] [Fintype n]

variable {N : Type w} [AddCommGroup N] [Module R N]

variable (M : Matrix n n R)

theorem minpoly_toLin' : minpoly R (toLin' M) = minpoly R M := minpoly.algEquiv_eq (toLinAlgEquiv' : Matrix n n R ≃ₐ[R] _) M

