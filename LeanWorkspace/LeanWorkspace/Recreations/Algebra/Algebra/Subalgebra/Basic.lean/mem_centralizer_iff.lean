import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem mem_centralizer_iff {s : Set A} {z : A} : z ∈ Subalgebra.centralizer R s ↔ ∀ g ∈ s, g * z = z * g := Iff.rfl

