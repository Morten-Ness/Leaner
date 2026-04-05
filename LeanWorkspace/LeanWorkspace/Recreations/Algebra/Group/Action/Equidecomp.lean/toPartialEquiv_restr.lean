import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [SMul G X]

theorem toPartialEquiv_restr (f : Equidecomp X G) (A : Set X) :
    (f.restr A).toPartialEquiv = f.toPartialEquiv.restr A := rfl

