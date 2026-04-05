import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem preimage_algebraMap (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} :
    algebraMap R S ⁻¹' spectrum S a = spectrum R a := Set.ext fun _ => spectrum.algebraMap_mem_iff spectrum _

