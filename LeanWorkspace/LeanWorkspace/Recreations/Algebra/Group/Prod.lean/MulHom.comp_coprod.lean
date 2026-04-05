import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [Mul M] [Mul N] [CommSemigroup P] (f : M →ₙ* P) (g : N →ₙ* P)

theorem comp_coprod {Q : Type*} [CommSemigroup Q] (h : P →ₙ* Q) (f : M →ₙ* P) (g : N →ₙ* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) := ext fun x => by simp

