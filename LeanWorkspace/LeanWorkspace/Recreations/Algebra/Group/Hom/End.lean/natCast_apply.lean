import Mathlib

variable {M : Type uM}

theorem natCast_apply [AddCommMonoid M] (n : ℕ) (m : M) : (↑n : AddMonoid.End M) m = n • m := rfl

