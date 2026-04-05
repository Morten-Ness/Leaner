import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

variable [CommMonoid P] (f : M →* P) (g : N →* P)

theorem coprod_comp_inr : (f.coprod g).comp (MonoidHom.inr M N) = g := ext fun x => by simp [MonoidHom.coprod_apply]

