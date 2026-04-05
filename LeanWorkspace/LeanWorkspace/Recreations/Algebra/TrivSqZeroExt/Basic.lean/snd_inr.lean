import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_inr [Zero R] (m : M) : (TrivSqZeroExt.inr m : tsze R M).snd = m := rfl

