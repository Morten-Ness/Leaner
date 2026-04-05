import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem AddMonoid.End.intCast_apply [AddCommGroup M] (z : ℤ) (m : M) :
    (↑z : AddMonoid.End M) m = z • m := rfl

