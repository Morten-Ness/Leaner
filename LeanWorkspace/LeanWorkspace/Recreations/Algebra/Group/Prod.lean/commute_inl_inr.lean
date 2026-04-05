import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

theorem commute_inl_inr (m : M) (n : N) : Commute (MonoidHom.inl M N m) (MonoidHom.inr M N n) := Commute.prod (.one_right m) (.one_left n)

