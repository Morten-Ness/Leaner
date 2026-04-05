import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem ofLinearMap_id (map_one) (map_mul) :
    AlgHom.ofLinearMap LinearMap.id map_one map_mul = AlgHom.id R A := rfl

