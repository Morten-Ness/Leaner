import Mathlib

open scoped Algebra

variable {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E] (b : F →ₗ[F] E)

theorem bijective_algebraMap_of_linearMap (hb : Function.Bijective b) :
    Function.Bijective (algebraMap F E) := ⟨injective_algebraMap_of_linearMap b hb.1, surjective_algebraMap_of_linearMap b hb.2⟩

