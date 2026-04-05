import Mathlib

variable {M : Type*} {N : Type*}

theorem coe_ofDense [Semigroup M] [Semigroup N] {s : Set M} (f : M → N) (hs : Subsemigroup.closure s = ⊤)
    (hmul) : (MulHom.ofDense f hs hmul : M → N) = f := rfl

