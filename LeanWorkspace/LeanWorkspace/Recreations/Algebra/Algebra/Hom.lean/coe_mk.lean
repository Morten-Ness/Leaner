import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

theorem coe_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₐ[R] B) : A → B) = f := rfl

