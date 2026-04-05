import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem mem_mk (s : Subsemiring A) (h) (x) : x ∈ Subalgebra.mk (R := R) s h ↔ x ∈ s :=
  .rfl

