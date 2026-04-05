import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem mapAlgEquiv_toAlgHom (f : A ≃ₐ[R] B) :
    (Polynomial.mapAlgEquiv f : Polynomial A →ₐ[R] Polynomial B) = Polynomial.mapAlgHom f := rfl

