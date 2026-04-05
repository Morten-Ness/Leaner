import Mathlib

variable {R : Type u} [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]

theorem monic_of_monic_mapAlg [FaithfulSMul R S] {p : Polynomial R} (hp : (mapAlg R S p).Monic) :
    p.Monic := monic_of_injective (FaithfulSMul.algebraMap_injective R S) hp

