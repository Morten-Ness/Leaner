import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem equivOfEq_rfl (S : Subalgebra R A) : Subalgebra.equivOfEq S S rfl = AlgEquiv.refl := by ext; rfl

