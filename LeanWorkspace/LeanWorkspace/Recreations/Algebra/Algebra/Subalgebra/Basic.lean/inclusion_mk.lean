import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem inclusion_mk (x : A) (hx : x ∈ S) : Subalgebra.inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ := rfl

