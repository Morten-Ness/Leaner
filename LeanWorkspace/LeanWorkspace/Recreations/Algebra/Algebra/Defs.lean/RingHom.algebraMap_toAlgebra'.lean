import Mathlib

set_option linter.docPrime false in
theorem RingHom.algebraMap_toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S)
    (h : ∀ c x, i c * x = x * i c) :
    @algebraMap R S _ _ (i.toAlgebra' h) = i := rfl

