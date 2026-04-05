import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_surjective [Nonempty M] : Function.Surjective (TrivSqZeroExt.fst : tsze R M → R) := Prod.fst_surjective

