import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

variable [CommMonoid P] (f : M →* P) (g : N →* P)

theorem comp_coprod {Q : Type*} [CommMonoid Q] (h : P →* Q) (f : M →* P) (g : N →* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) := ext fun x => by simp

