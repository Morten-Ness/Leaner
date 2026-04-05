import Mathlib

variable {M : Type*}

theorem quot_mk_eq_mk [Monoid M] (a : M) : Quot.mk Setoid.r a = Associates.mk a := Associated.rfl

