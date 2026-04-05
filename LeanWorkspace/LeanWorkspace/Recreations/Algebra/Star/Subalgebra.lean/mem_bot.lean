import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem mem_bot {x : A} : x ∈ (⊥ : StarSubalgebra R A) ↔ x ∈ Set.range (algebraMap R A) := Iff.rfl

