import Mathlib

variable {F α M N G : Type*}

variable [Monoid M] [Monoid N]

theorem mulRight_bijective (a : Mˣ) : Function.Bijective ((· * a) : M → M) := (Units.mulRight a).bijective

