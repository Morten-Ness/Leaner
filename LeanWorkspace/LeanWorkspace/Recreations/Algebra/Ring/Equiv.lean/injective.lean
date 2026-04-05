import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem injective (e : R ≃+* S) : Function.Injective e := EquivLike.injective e

