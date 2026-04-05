import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem toLinearMap_ofLinearMap (f : A →ₗ[R] B) (map_one) (map_mul) :
    AlgHom.toLinearMap (AlgHom.ofLinearMap f map_one map_mul) = f := rfl

