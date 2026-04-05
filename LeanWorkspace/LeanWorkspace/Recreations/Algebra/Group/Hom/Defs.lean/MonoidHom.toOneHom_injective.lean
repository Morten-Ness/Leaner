import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.toOneHom_injective [MulOne M] [MulOne N] :
    Function.Injective (MonoidHom.toOneHom : (M →* N) → OneHom M N) := Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

