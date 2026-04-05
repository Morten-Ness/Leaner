import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem topEquiv_toMulHom :
    ((Subsemigroup.topEquiv : _ ≃* M) : _ →ₙ* M) = MulMemClass.subtype (⊤ : Subsemigroup M) := rfl

