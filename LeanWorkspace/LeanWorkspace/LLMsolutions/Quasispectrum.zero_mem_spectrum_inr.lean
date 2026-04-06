import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem zero_mem_spectrum_inr (R S : Type*) {A : Type*} [CommSemiring R]
    [CommRing S] [Nontrivial S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    0 ∈ spectrum R (a : Unitization S A) := by
  simpa using Unitization.zero_mem_spectrum_inr (R := R) (S := S) a
