import Mathlib

variable {R S M M₂ : Type*}

theorem Module.nontrivial (R M : Type*) [MonoidWithZero R] [Nontrivial M] [Zero M]
    [MulActionWithZero R M] : Nontrivial R := MulActionWithZero.nontrivial R M

-- see Note [lower instance priority]

