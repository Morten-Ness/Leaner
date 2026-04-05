import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.toMulHom_injective [MulOne M] [MulOne N] :
    Function.Injective (MonoidHom.toMulHom : (M →* N) → M →ₙ* N) := Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

