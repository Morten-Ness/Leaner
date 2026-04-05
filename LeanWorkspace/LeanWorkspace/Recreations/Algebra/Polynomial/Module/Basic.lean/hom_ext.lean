import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

theorem hom_ext {f g : PolynomialModule R M →ₗ[R] M'}
    (h : ∀ a, f ∘ₗ PolynomialModule.lsingle R a = g ∘ₗ PolynomialModule.lsingle R a) : f = g := Finsupp.lhom_ext' h

