import Mathlib

variable {F α M N G : Type*}

variable [Monoid M] [Monoid N]

theorem mulLeft_bijective (a : Mˣ) : Function.Bijective ((a * ·) : M → M) := (Units.mulLeft a).bijective

