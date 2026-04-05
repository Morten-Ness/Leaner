import Mathlib

open scoped Algebra

variable {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E] (b : F →ₗ[F] E)

theorem bijective_algebraMap_of_linearEquiv (b : F ≃ₗ[F] E) :
    Function.Bijective (algebraMap F E) := bijective_algebraMap_of_linearMap _ b.bijective

