import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem mem_center_iff {a : A} : a ∈ Subalgebra.center R A ↔ ∀ b : A, b * a = a * b := Subsemigroup.mem_center_iff

