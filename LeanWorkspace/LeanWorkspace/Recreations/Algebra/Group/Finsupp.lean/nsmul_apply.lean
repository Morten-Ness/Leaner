import Mathlib

variable {ι F M N O G H : Type*}

variable [AddMonoid M]

theorem nsmul_apply (n : ℕ) (f : ι →₀ M) (x : ι) : (n • f) x = n • f x := rfl

