import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (φ : A →ₐ[R] B)

theorem mem_range (φ : A →ₐ[R] B) {y : B} : y ∈ φ.range ↔ ∃ x, φ x = y := RingHom.mem_rangeS

