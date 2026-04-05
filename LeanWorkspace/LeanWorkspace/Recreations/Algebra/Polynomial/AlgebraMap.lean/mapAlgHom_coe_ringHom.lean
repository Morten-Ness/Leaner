import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem mapAlgHom_coe_ringHom (f : A →ₐ[R] B) :
    ↑(Polynomial.mapAlgHom f : _ →ₐ[R] Polynomial B) = (mapRingHom ↑f : Polynomial A →+* Polynomial B) := rfl

