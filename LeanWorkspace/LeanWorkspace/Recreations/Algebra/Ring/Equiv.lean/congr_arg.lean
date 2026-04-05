import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem congr_arg {f : R ≃+* S} {x x' : R} : x = x' → f x = f x' := DFunLike.congr_arg f

