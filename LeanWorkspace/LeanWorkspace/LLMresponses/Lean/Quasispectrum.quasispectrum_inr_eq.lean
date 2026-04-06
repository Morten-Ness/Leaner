FAIL
import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem quasispectrum_inr_eq (R S : Type*) {A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    quasispectrum R (a : Unitization S A) = quasispectrum R a := by
  ext r
  constructor
  · intro h hr hqr
    exact h hr (by simpa using hqr)
  · intro h hr hqr
    exact h hr (by simpa using hqr)
