import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem toSubmodule_bot : Subalgebra.toSubmodule (⊥ : Subalgebra R A) = 1 := Submodule.one_eq_range.symm

