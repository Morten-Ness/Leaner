import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_top {x : A} : x ∈ (⊤ : Subalgebra R A) := Set.mem_univ x

