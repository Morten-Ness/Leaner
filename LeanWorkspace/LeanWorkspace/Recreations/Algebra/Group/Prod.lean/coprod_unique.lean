import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

variable [CommMonoid P] (f : M →* P) (g : N →* P)

theorem coprod_unique (f : M × N →* P) : (f.comp (MonoidHom.inl M N)).coprod (f.comp (MonoidHom.inr M N)) = f := ext fun x => by simp [MonoidHom.coprod_apply, MonoidHom.inl_apply, MonoidHom.inr_apply, ← map_mul]

