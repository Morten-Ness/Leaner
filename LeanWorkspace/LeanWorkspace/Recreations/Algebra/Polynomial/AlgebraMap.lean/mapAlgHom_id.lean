import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem mapAlgHom_id : Polynomial.mapAlgHom (AlgHom.id R A) = AlgHom.id R (Polynomial A) := AlgHom.ext fun _x => map_id

