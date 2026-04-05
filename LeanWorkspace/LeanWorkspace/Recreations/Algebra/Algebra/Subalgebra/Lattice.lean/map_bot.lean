import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_bot (f : A →ₐ[R] B) : (⊥ : Subalgebra R A).map f = ⊥ := Subalgebra.toSubmodule_injective <| by
    simpa only [Subalgebra.map_toSubmodule, Algebra.toSubmodule_bot] using Submodule.map_one _

