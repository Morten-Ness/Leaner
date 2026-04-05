import Mathlib

variable {ι F M N O G H : Type*}

theorem neg_apply [NegZeroClass G] (g : ι →₀ G) (a : ι) : (-g) a = -g a := rfl

