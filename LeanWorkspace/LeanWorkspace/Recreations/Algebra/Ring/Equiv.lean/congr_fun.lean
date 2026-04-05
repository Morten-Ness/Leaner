import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem congr_fun {f g : R ≃+* S} (h : f = g) (x : R) : f x = g x := DFunLike.congr_fun h x

