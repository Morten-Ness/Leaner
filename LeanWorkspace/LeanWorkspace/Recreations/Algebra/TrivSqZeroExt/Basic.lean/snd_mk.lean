import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_mk (r : R) (m : M) : TrivSqZeroExt.snd (r, m) = m := rfl

