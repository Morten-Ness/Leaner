import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M →* N⦄ (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

