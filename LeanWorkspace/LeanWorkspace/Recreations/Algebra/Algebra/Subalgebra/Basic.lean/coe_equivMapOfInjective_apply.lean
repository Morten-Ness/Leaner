import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

variable (f : A →ₐ[R] B)

variable (hf : Function.Injective f)

theorem coe_equivMapOfInjective_apply (x : S) : ↑(Subalgebra.equivMapOfInjective S f hf x) = f x := rfl

