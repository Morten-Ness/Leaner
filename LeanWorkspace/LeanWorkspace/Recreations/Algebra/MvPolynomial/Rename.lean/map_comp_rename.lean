import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem map_comp_rename (f : R →+* S) (g : σ → τ) :
    (map f).comp (MvPolynomial.rename g).toRingHom = (MvPolynomial.rename g).toRingHom.comp (map f) := RingHom.ext fun p ↦ MvPolynomial.map_rename f g p

