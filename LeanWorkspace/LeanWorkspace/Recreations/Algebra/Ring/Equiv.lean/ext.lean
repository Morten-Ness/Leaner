import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem ext {f g : R ≃+* S} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

