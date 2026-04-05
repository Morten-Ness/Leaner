import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem bijective (e : R ≃+* S) : Function.Bijective e := EquivLike.bijective e

