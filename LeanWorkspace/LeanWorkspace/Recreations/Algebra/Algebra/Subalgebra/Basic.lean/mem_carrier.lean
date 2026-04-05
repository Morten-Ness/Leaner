import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem mem_carrier {s : Subalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s := Iff.rfl

