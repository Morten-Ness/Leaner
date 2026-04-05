import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

theorem inl_apply (x) : MonoidHom.inl M N x = (x, 1) := rfl

