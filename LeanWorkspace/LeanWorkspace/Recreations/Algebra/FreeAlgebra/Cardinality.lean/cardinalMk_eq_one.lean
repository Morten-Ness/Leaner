import Mathlib

variable (R : Type u) [CommSemiring R]

variable (X : Type v)

theorem cardinalMk_eq_one [Subsingleton R] : #(FreeAlgebra R X) = 1 := by
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq, MonoidAlgebra, mk_eq_one]

