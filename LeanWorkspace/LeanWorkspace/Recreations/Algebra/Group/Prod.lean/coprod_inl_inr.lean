import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

variable [CommMonoid P] (f : M →* P) (g : N →* P)

theorem coprod_inl_inr {M N : Type*} [CommMonoid M] [CommMonoid N] :
    (MonoidHom.inl M N).coprod (MonoidHom.inr M N) = id (M × N) := MonoidHom.coprod_unique (id <| M × N)

