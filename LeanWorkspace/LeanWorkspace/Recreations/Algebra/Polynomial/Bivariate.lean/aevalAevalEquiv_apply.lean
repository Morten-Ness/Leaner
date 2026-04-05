import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem aevalAevalEquiv_apply (xy : A × A) : aevalAevalEquiv R A xy = aevalAeval xy.1 xy.2 := rfl

