import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrum.preimage_algebraMap (S : Type*) {R A : Type*} [Semifield R] [Field S]
    [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} :
    algebraMap R S ⁻¹' quasispectrum S a = quasispectrum R a := Set.ext fun _ => quasispectrum.algebraMap_mem_iff _

