import Mathlib

variable {R S G M N O ι : Type*}

variable [Ring R]

theorem neg_apply (m : M) (x : R[M]) : (-x) m = -x m := rfl

