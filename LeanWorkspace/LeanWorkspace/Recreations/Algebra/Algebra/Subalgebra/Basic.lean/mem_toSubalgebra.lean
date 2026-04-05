import Mathlib

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable (p : Submodule R A)

theorem mem_toSubalgebra {p : Submodule R A} {h_one h_mul} {x} :
    x ∈ p.toSubalgebra h_one h_mul ↔ x ∈ p := Iff.rfl

