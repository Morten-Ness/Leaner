import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem mem_map {S : Subalgebra R A} {f : A →ₐ[R] B} {y : B} : y ∈ Subalgebra.map f S ↔ ∃ x ∈ S, f x = y := Subsemiring.mem_map

