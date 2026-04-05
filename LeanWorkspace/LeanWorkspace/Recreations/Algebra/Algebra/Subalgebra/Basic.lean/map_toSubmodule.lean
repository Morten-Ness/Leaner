import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem map_toSubmodule {S : Subalgebra R A} {f : A →ₐ[R] B} :
    (Subalgebra.toSubmodule <| S.map f) = S.toSubmodule.map f.toLinearMap := SetLike.coe_injective rfl

