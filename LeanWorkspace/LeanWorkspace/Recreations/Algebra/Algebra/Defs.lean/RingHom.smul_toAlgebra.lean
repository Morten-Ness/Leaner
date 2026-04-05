import Mathlib

theorem RingHom.smul_toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R →+* S)
    (r : R) (s : S) :
    let _ := RingHom.toAlgebra i
    r • s = i r * s := rfl

