import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inr_injective [Zero R] : Function.Injective (TrivSqZeroExt.inr : M → tsze R M) := Function.LeftInverse.injective <| TrivSqZeroExt.snd_inr _

