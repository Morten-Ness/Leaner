import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem ker_rangeRestrict (f : A →ₐ[R] B) : RingHom.ker f.rangeRestrict = RingHom.ker f := Ideal.ext fun _ ↦ Subtype.ext_iff

