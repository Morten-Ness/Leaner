import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBySet_ideal_span_singleton_eq :
    Submodule.torsionBySet R M (Ideal.span {a}) = Submodule.torsionBy R M a := Submodule.torsionBySet_span_singleton_eq a

