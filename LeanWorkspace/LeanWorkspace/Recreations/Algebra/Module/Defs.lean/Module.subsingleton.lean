import Mathlib

variable {R S M M₂ : Type*}

theorem Module.subsingleton (R M : Type*) [MonoidWithZero R] [Subsingleton R] [Zero M]
    [MulActionWithZero R M] : Subsingleton M := MulActionWithZero.subsingleton R M

