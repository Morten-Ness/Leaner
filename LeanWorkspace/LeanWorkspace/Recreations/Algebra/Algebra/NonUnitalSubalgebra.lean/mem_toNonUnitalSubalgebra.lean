import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

theorem mem_toNonUnitalSubalgebra {p : Submodule R A} {h_mul} {x} :
    x ∈ p.toNonUnitalSubalgebra h_mul ↔ x ∈ p := Iff.rfl

