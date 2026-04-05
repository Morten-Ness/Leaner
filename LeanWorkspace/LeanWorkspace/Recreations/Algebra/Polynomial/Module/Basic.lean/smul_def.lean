import Mathlib

open scoped Polynomial

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

theorem smul_def (f : R[X]) (m : PolynomialModule R M) :
    f • m = Polynomial.aeval (Finsupp.lmapDomain M R Nat.succ) f m := by
  rfl

