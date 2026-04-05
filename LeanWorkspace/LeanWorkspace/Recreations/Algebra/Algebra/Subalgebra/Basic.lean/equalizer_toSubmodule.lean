import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable {F : Type*}

variable [FunLike F A B] [AlgHomClass F R A B]

theorem equalizer_toSubmodule {φ ψ : F} :
    Subalgebra.toSubmodule (AlgHom.equalizer φ ψ) = LinearMap.eqLocus φ ψ := rfl

