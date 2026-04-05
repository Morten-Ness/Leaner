import Mathlib

variable {M : Type*} [Monoid M]

theorem IsUnit.coe {S : Type*} [SetLike S M] [SubmonoidClass S M] {N : S} {a : N}
    (ha : IsUnit a) : IsUnit (a : M) := ha.map (SubmonoidClass.subtype N)

