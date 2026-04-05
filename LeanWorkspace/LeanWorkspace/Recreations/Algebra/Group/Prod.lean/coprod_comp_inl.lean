import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

variable [CommMonoid P] (f : M →* P) (g : N →* P)

theorem coprod_comp_inl : (f.coprod g).comp (MonoidHom.inl M N) = f := ext fun x => by simp [MonoidHom.coprod_apply]

