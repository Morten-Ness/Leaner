import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem AddMonoid.End.one_apply [AddZeroClass M] (m : M) : (1 : AddMonoid.End M) m = m := rfl

