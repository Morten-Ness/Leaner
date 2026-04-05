import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_surjective [Nonempty R] : Function.Surjective (TrivSqZeroExt.snd : tsze R M → M) := Prod.snd_surjective

