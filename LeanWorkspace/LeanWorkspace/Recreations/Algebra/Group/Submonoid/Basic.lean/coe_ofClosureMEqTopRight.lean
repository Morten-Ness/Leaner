import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [Monoid M] [Monoid N] {s : Set M}

theorem coe_ofClosureMEqTopRight (f : M → N) (hs : Submonoid.closure s = ⊤) (h1 hmul) :
    ⇑(MonoidHom.ofClosureMEqTopRight f hs h1 hmul) = f := rfl

