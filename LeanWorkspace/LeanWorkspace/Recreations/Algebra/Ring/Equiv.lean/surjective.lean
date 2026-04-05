import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem surjective (e : R ≃+* S) : Function.Surjective e := EquivLike.surjective e

