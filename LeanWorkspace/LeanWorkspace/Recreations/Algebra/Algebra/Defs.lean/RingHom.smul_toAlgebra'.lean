import Mathlib

set_option linter.docPrime false in
theorem RingHom.smul_toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S)
    (h : ∀ c x, i c * x = x * i c) (r : R) (s : S) :
    let _ := RingHom.toAlgebra' i h
    r • s = i r * s := rfl

